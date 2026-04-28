#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# host/plot_results.py
#
# Visualize STREAM characterization sweep CSVs produced by characterize.py.
# Auto-detects which axis (or pair of axes) varies and picks an appropriate
# plot shape:
#
#   1-D sweeps (single varying axis among
#     {rd_delay_cyc, descriptors, num_channels, total_bytes}):
#       - Line plot with three series: throughput_MBps (total), r2r_MBps,
#         w2w_MBps. Useful for "BW vs N" curves.
#
#   2-D sweeps (two varying axes):
#       - Heatmap of throughput_MBps on the (axis_x, axis_y) grid.
#       - Companion line plot with one line per axis_y value, x=axis_x.
#
# Each input CSV produces a single PNG (1-D sweeps) or a paired PNG
# (2-D sweeps: <name>_heatmap.png + <name>_lines.png) under --outdir.
#
# USAGE:
#   python3 host/plot_results.py                      # plots every *.csv in cwd
#   python3 host/plot_results.py *.csv                # specific files
#   python3 host/plot_results.py --outdir plots/      # different output dir
#   python3 host/plot_results.py --show               # also display interactively

from __future__ import annotations

import argparse
import os
import sys
from typing import List, Tuple

import matplotlib

matplotlib.use("Agg")  # headless-safe; --show flag overrides below.
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

# "Independent" sweep axes — the host varies these directly. total_bytes is
# excluded here because it's derived (channels × descriptors × per-descriptor
# size), so it tags along on most sweeps and would falsely turn a 1-D sweep
# into a 2-D one. We treat it as a sweep axis only when none of the other
# three vary (the pure size sweep). Order = X-axis preference for 2-D plots.
_SWEEP_AXES = [
    "rd_delay_cyc",
    "descriptors",
    "num_channels",
]

_THROUGHPUT_COLS = [
    ("throughput_MBps", "total (descriptor → last B)"),
    ("r2r_MBps",        "r2r (first R → last R)"),
    ("w2w_MBps",        "w2w (first W → last W)"),
]


def _varying_axes(df: pd.DataFrame) -> List[str]:
    """Return the list of axes whose values vary across the sweep.

    Only the independent sweep variables in _SWEEP_AXES count. total_bytes
    is treated as the sweep axis only if NONE of those vary (i.e. a pure
    size sweep at fixed channels/descriptors/delay).
    """
    out = []
    for col in _SWEEP_AXES:
        if col in df.columns and df[col].nunique(dropna=True) > 1:
            out.append(col)
    if not out and "total_bytes" in df.columns \
            and df["total_bytes"].nunique(dropna=True) > 1:
        out.append("total_bytes")
    return out


def _filter_passing(df: pd.DataFrame) -> pd.DataFrame:
    """Drop timeout=True rows; they're useless for a throughput plot."""
    if "timeout" in df.columns:
        df = df[~df["timeout"].astype(bool)]
    return df


def _axis_label(col: str) -> str:
    return {
        "rd_delay_cyc":  "response delay (cycles, rd=wr)",
        "descriptors":   "descriptors per channel",
        "num_channels":  "channels",
        "total_bytes":   "total bytes moved",
    }.get(col, col)


def _format_x_ticks(ax, col: str, values: np.ndarray) -> None:
    """For total_bytes axes, use KB/MB labels; otherwise let matplotlib do it."""
    if col == "total_bytes":
        # Use log-x to span 8KB..several MB cleanly.
        ax.set_xscale("log", base=2)
        labels = []
        for v in values:
            v = int(v)
            if v >= 1 << 20:
                labels.append(f"{v >> 20}MB")
            elif v >= 1 << 10:
                labels.append(f"{v >> 10}KB")
            else:
                labels.append(str(v))
        ax.set_xticks(values)
        ax.set_xticklabels(labels)


def plot_1d(df: pd.DataFrame, x_col: str, title: str, out_path: str) -> None:
    """Throughput-vs-axis line plot, 3 series."""
    df = df.sort_values(by=x_col)
    fig, ax = plt.subplots(figsize=(8.0, 5.0))

    for col, label in _THROUGHPUT_COLS:
        if col not in df.columns:
            continue
        # Cast to float so missing/None becomes NaN cleanly.
        y = pd.to_numeric(df[col], errors="coerce")
        ax.plot(df[x_col], y, marker="o", linewidth=1.6, label=label)

    ax.set_xlabel(_axis_label(x_col))
    ax.set_ylabel("throughput (MB/s)")
    ax.set_title(title)
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(loc="best", fontsize=9)

    _format_x_ticks(ax, x_col, df[x_col].to_numpy())

    fig.tight_layout()
    fig.savefig(out_path, dpi=140)
    plt.close(fig)
    print(f"  wrote {out_path}")


def plot_2d(df: pd.DataFrame, x_col: str, y_col: str, base_path: str,
            title: str) -> None:
    """Heatmap (throughput surface) + companion line plot grouped by y_col."""
    df = _filter_passing(df).copy()
    df["throughput_MBps"] = pd.to_numeric(df["throughput_MBps"], errors="coerce")

    # Pivot to a regular grid: rows = y_col, cols = x_col, cells = throughput
    pivot = (
        df.pivot_table(
            index=y_col, columns=x_col, values="throughput_MBps",
            aggfunc="mean")
        .sort_index(axis=0)
        .sort_index(axis=1)
    )

    # ---- Heatmap ----
    fig, ax = plt.subplots(figsize=(8.5, 5.0))
    im = ax.imshow(
        pivot.to_numpy(),
        aspect="auto", origin="lower",
        cmap="viridis",
        interpolation="nearest",
    )
    ax.set_xticks(range(len(pivot.columns)))
    ax.set_xticklabels(pivot.columns)
    ax.set_yticks(range(len(pivot.index)))
    ax.set_yticklabels(pivot.index)
    ax.set_xlabel(_axis_label(x_col))
    ax.set_ylabel(_axis_label(y_col))
    ax.set_title(f"{title}\n(throughput_MBps surface)")

    # Annotate each cell with its value (rounded).
    for iy in range(pivot.shape[0]):
        for ix in range(pivot.shape[1]):
            v = pivot.iat[iy, ix]
            if not np.isnan(v):
                ax.text(ix, iy, f"{v:.0f}", ha="center", va="center",
                        color="white" if v < pivot.to_numpy().max() / 2 else "black",
                        fontsize=8)

    fig.colorbar(im, ax=ax, label="throughput (MB/s)")
    fig.tight_layout()
    heatmap_path = base_path + "_heatmap.png"
    fig.savefig(heatmap_path, dpi=140)
    plt.close(fig)
    print(f"  wrote {heatmap_path}")

    # ---- Companion line plot: one line per y_col value, x = x_col ----
    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    for y_val, group in df.groupby(y_col):
        g = group.sort_values(x_col)
        ax.plot(g[x_col], g["throughput_MBps"], marker="o", linewidth=1.6,
                label=f"{y_col}={y_val}")
    ax.set_xlabel(_axis_label(x_col))
    ax.set_ylabel("throughput_MBps")
    ax.set_title(f"{title} — slices by {y_col}")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(fontsize=9, title=_axis_label(y_col))
    _format_x_ticks(ax, x_col, np.array(sorted(df[x_col].unique())))
    fig.tight_layout()
    lines_path = base_path + "_lines.png"
    fig.savefig(lines_path, dpi=140)
    plt.close(fig)
    print(f"  wrote {lines_path}")


def _summary(df: pd.DataFrame, csv_name: str) -> None:
    """One-line summary printed before each plot — sanity check + stats."""
    df = _filter_passing(df)
    if df.empty:
        print(f"  [{csv_name}] all rows timed out — nothing to plot")
        return
    peak = df["throughput_MBps"].max()
    n = len(df)
    n_pass = int(df["pass"].sum()) if "pass" in df.columns else n
    print(f"  [{csv_name}] {n} rows, {n_pass} passed, peak={peak:.1f} MB/s")


def plot_csv(csv_path: str, outdir: str) -> None:
    df = pd.read_csv(csv_path)
    base = os.path.splitext(os.path.basename(csv_path))[0]
    out_base = os.path.join(outdir, base)

    print(f"\n• {csv_path}")
    _summary(df, base)
    df = _filter_passing(df)
    if df.empty:
        return

    axes = _varying_axes(df)

    if len(axes) == 0:
        print(f"  [{base}] no varying sweep axis — skipping")
        return

    if len(axes) == 1:
        plot_1d(df, axes[0], title=base, out_path=out_base + ".png")
        return

    # 2-D (or higher — just use the top two and warn).
    if len(axes) > 2:
        print(f"  [{base}] {len(axes)} axes vary ({axes}); using "
              f"x={axes[0]}, y={axes[1]}; the rest collapsed by mean")
    x_col, y_col = axes[0], axes[1]
    plot_2d(df, x_col, y_col, base_path=out_base, title=base)


def main() -> int:
    p = argparse.ArgumentParser(
        description="Plot STREAM characterization sweep CSVs.")
    p.add_argument("csvs", nargs="*",
                   help="CSV files to plot (default: every *.csv in cwd)")
    p.add_argument("--outdir", "-o", default="plots",
                   help="directory for output PNGs (default: plots/)")
    p.add_argument("--show", action="store_true",
                   help="display each figure interactively in addition to saving")
    args = p.parse_args()

    if args.show:
        # Interactive backend (matplotlib will pick a GUI if one is available).
        matplotlib.use("TkAgg", force=True)

    csvs = args.csvs or sorted(f for f in os.listdir(".") if f.endswith(".csv"))
    if not csvs:
        print("No CSVs found.", file=sys.stderr)
        return 1

    os.makedirs(args.outdir, exist_ok=True)

    print(f"Plotting {len(csvs)} CSV(s) into {args.outdir}/")
    for csv in csvs:
        if not os.path.exists(csv):
            print(f"  skip (missing): {csv}", file=sys.stderr)
            continue
        try:
            plot_csv(csv, args.outdir)
        except Exception as e:  # noqa: BLE001 - one bad CSV shouldn't kill the batch
            print(f"  error plotting {csv}: {e}", file=sys.stderr)

    print(f"\nDone. PNGs in {args.outdir}/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
