#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# plot_char_reports.py — figures for the STREAM characterization perf report
# (all-fixes bitstream). Consumes the run_characterization.py JSON outputs and
# emits PNGs using the *clean* metrics (on-chip-timer bus throughput + PMU
# datapath utilization), not the UART-contaminated wall throughput.
#
# Handles both JSON shapes the runner emits:
#   - flat matrix:      [ {result-dict}, ... ]
#   - resp-delay sweep: [ {"rd_delay":N,"wr_delay":N,"config":..,"result":{..}}, .. ]
#
# Usage:
#   source env_python
#   python3 host/plot_char_reports.py \
#       --matrix   ../reports/perf/matrix_2026-06-15.json \
#       --chan-delay ../reports/perf/chan_x_delay_2026-06-16.json \
#       --desc-delay ../reports/perf/desc_x_delay_2026-06-16.json \
#       --size      ../reports/perf/size_sweep_2026-06-16.json \
#       --outdir    ../reports/perf/plots
import argparse
import json
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

GREEN = "#228B22"
GRAY = "#404040"


def _row(rec):
    """Normalize one record (flat result or delay-wrapped) into a flat dict."""
    rd_delay = rec.get("rd_delay")
    r = rec.get("result", rec)
    m = r.get("metrics", {}) or {}
    return {
        "channels": r.get("num_channels"),
        "desc": r.get("descriptors_per_channel"),
        "bytes": r.get("transfer_bytes"),
        "total_bytes": r.get("total_bytes"),
        "rd_delay": rd_delay if rd_delay is not None else 0,
        "e2e_util": (m.get("end_to_end_utilization") or 0.0) * 100.0,
        "bus_util": r.get("bus_e2e_util_pct", 0.0),
        "bus_mbps": r.get("bus_throughput_mbps", 0.0),
        "wall_mbps": r.get("throughput_mbps", 0.0),
        "pass": r.get("pass", None),
    }


def load(path):
    if not path or not os.path.exists(path):
        return []
    return [_row(x) for x in json.load(open(path))]


def _save(fig, outdir, name):
    os.makedirs(outdir, exist_ok=True)
    p = os.path.join(outdir, name)
    fig.tight_layout()
    fig.savefig(p, dpi=130, bbox_inches="tight")
    plt.close(fig)
    print(f"  wrote {p}", file=sys.stderr)


# ---------------------------------------------------------------- 1-D sweeps
def line_1d(rows, xkey, xlabel, title, outdir, name, xlog=False, xticklabels=None):
    rows = sorted(rows, key=lambda r: r[xkey])
    xs = [r[xkey] for r in rows]
    fig, ax1 = plt.subplots(figsize=(7, 4.2))
    ax1.plot(xs, [r["bus_mbps"] for r in rows], "-o", color=GREEN,
             label="bus throughput (MB/s)")
    ax1.set_xlabel(xlabel)
    ax1.set_ylabel("bus throughput (MB/s)", color=GREEN)
    ax1.tick_params(axis="y", labelcolor=GREEN)
    if xlog:
        ax1.set_xscale("log", base=2)
    if xticklabels is not None:
        ax1.set_xticks(xs)
        ax1.set_xticklabels(xticklabels, rotation=45, ha="right")
    ax2 = ax1.twinx()
    ax2.plot(xs, [r["e2e_util"] for r in rows], "--s", color=GRAY,
             label="datapath E2E util (%)")
    ax2.set_ylabel("datapath E2E util (%)", color=GRAY)
    ax2.tick_params(axis="y", labelcolor=GRAY)
    ax2.set_ylim(0, 100)
    ax1.set_title(title)
    ax1.grid(True, alpha=0.3)
    _save(fig, outdir, name)


# ---------------------------------------------------------------- 2-D crosses
def _grid(rows, xkey, ykey, vkey):
    xs = sorted({r[xkey] for r in rows})
    ys = sorted({r[ykey] for r in rows})
    Z = np.full((len(ys), len(xs)), np.nan)
    for r in rows:
        Z[ys.index(r[ykey]), xs.index(r[xkey])] = r[vkey]
    return xs, ys, Z


def heatmap(rows, xkey, ykey, vkey, xlabel, ylabel, vlabel, title, outdir, name):
    xs, ys, Z = _grid(rows, xkey, ykey, vkey)
    fig, ax = plt.subplots(figsize=(7.5, 4.6))
    im = ax.imshow(Z, origin="lower", aspect="auto", cmap="viridis")
    ax.set_xticks(range(len(xs))); ax.set_xticklabels(xs)
    ax.set_yticks(range(len(ys))); ax.set_yticklabels(ys)
    ax.set_xlabel(xlabel); ax.set_ylabel(ylabel); ax.set_title(title)
    for i in range(len(ys)):
        for j in range(len(xs)):
            if not np.isnan(Z[i, j]):
                ax.text(j, i, f"{Z[i, j]:.0f}", ha="center", va="center",
                        color="white", fontsize=7)
    fig.colorbar(im, ax=ax, label=vlabel)
    _save(fig, outdir, name)


def line_family(rows, xkey, ykey, vkey, xlabel, vlabel, leg, title, outdir, name,
                xlog=False):
    xs = sorted({r[xkey] for r in rows})
    ys = sorted({r[ykey] for r in rows})
    fig, ax = plt.subplots(figsize=(7, 4.2))
    cmap = plt.cm.viridis(np.linspace(0, 0.9, len(ys)))
    for k, yv in enumerate(ys):
        sub = sorted([r for r in rows if r[ykey] == yv], key=lambda r: r[xkey])
        ax.plot([r[xkey] for r in sub], [r[vkey] for r in sub], "-o",
                color=cmap[k], label=f"{leg}={yv}")
    if xlog:
        ax.set_xscale("symlog")  # symlog keeps the delay=0 point on a log axis
    ax.set_xlabel(xlabel); ax.set_ylabel(vlabel); ax.set_title(title)
    ax.grid(True, alpha=0.3); ax.legend(fontsize=8)
    _save(fig, outdir, name)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--matrix")
    ap.add_argument("--chan-delay")
    ap.add_argument("--desc-delay")
    ap.add_argument("--size")
    ap.add_argument("--outdir", required=True)
    args = ap.parse_args()

    matrix = load(args.matrix)
    chan_delay = load(args.chan_delay)
    desc_delay = load(args.desc_delay)
    size = load(args.size)

    # 1-D channel sweep (1desc row of the matrix, delay 0)
    if matrix:
        ch = [r for r in matrix if r["desc"] == 1]
        if ch:
            line_1d(ch, "channels", "active channels",
                    "Throughput & utilization vs channel count (1 desc, 1 MB)",
                    args.outdir, "channel_sweep.png")
        de = [r for r in matrix if r["channels"] == 1]
        if de:
            line_1d(de, "desc", "descriptors per channel",
                    "Throughput & utilization vs descriptor depth (1 ch, 1 MB)",
                    args.outdir, "desc_sweep.png")
        heatmap(matrix, "channels", "desc", "e2e_util", "channels",
                "descriptors/ch", "datapath E2E util (%)",
                "Datapath utilization — channels x descriptors (1 MB)",
                args.outdir, "channels_x_desc_heatmap.png")
        line_family(matrix, "channels", "desc", "bus_mbps", "channels",
                    "bus throughput (MB/s)", "desc",
                    "Bus throughput — channels x descriptors (1 MB)",
                    args.outdir, "channels_x_desc_lines.png")

    # delay sweep (1-D): 1ch slice of chan_delay
    if chan_delay:
        d1 = [r for r in chan_delay if r["channels"] == 1]
        if d1:
            line_1d(d1, "rd_delay", "memory response delay (cycles)",
                    "Throughput & utilization vs memory latency (1 ch, 1 desc)",
                    args.outdir, "delay_sweep.png")
        heatmap(chan_delay, "rd_delay", "channels", "e2e_util",
                "response delay (cyc)", "channels", "datapath E2E util (%)",
                "Datapath utilization — channels x memory latency",
                args.outdir, "channels_x_delay_heatmap.png")
        line_family(chan_delay, "rd_delay", "channels", "bus_mbps",
                    "response delay (cyc, symlog)", "bus throughput (MB/s)", "ch",
                    "Bus throughput — channels x memory latency",
                    args.outdir, "channels_x_delay_lines.png", xlog=True)

    # desc x delay
    if desc_delay:
        heatmap(desc_delay, "rd_delay", "desc", "e2e_util",
                "response delay (cyc)", "descriptors/ch", "datapath E2E util (%)",
                "Datapath utilization — descriptors x memory latency (1 ch)",
                args.outdir, "desc_x_delay_heatmap.png")
        line_family(desc_delay, "rd_delay", "desc", "bus_mbps",
                    "response delay (cyc, symlog)", "bus throughput (MB/s)", "desc",
                    "Bus throughput — descriptors x memory latency (1 ch)",
                    args.outdir, "desc_x_delay_lines.png", xlog=True)

    # size sweep
    if size:
        for r in size:
            r["size_kb"] = (r["bytes"] or 0) / 1024
        labels = [f"{int(r['size_kb'])}K" if r["size_kb"] < 1024
                  else f"{int(r['size_kb']/1024)}M" for r in
                  sorted(size, key=lambda r: r["size_kb"])]
        line_1d(size, "size_kb", "transfer size per descriptor",
                "Throughput & utilization vs transfer size (1 ch, 1 desc)",
                args.outdir, "size_sweep.png", xlog=True, xticklabels=labels)

    print("plotting done", file=sys.stderr)


if __name__ == "__main__":
    main()
