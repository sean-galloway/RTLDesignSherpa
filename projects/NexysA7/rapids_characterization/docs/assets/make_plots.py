#!/usr/bin/env python3
"""Render the RAPIDS beats characterization report plots to PNG.

Plots:
  10_timing_closure  - 100 MHz setup WNS closure trajectory
  11_utilization     - post-route utilization % (NUM_CHANNELS=4 board build)
  12_suite_grid      - on-silicon suite result grid, read from the latest
                       flows-rapids-beats/reports/rapids_char_suite_*.json

Usage:
  python3 make_plots.py            # auto-locate latest suite JSON
  python3 make_plots.py <suite.json>
"""
import glob
import json
import os
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

HERE = os.path.dirname(os.path.abspath(__file__))
PNG = os.path.join(HERE, "png")
os.makedirs(PNG, exist_ok=True)

FOREST = "#228B22"
GRAY = "#404040"
DPI = 150

REPO_ROOT = os.environ.get(
    "REPO_ROOT",
    os.path.abspath(os.path.join(HERE, "..", "..", "..", "..")),
)
REPORTS = os.path.join(
    REPO_ROOT,
    "projects/NexysA7/rapids_characterization/flows-rapids-beats/reports",
)


def latest_suite_json():
    if len(sys.argv) > 1:
        return sys.argv[1]
    cand = sorted(glob.glob(os.path.join(REPORTS, "rapids_char_suite_*.json")))
    if not cand:
        raise SystemExit("no rapids_char_suite_*.json found in %s" % REPORTS)
    return cand[-1]


def plot_timing_closure():
    stages = ["initial", "post-route\n(fix)", "physopt", "final\n(pulse-fix\nrebuild)"]
    wns = [-0.365, -0.089, 0.051, 0.007]
    colors = [FOREST if v >= 0 else "#b22222" for v in wns]

    fig, ax = plt.subplots(figsize=(8, 4.5))
    bars = ax.bar(stages, wns, color=colors, edgecolor=GRAY, width=0.6)
    ax.axhline(0.0, color=GRAY, linewidth=1.4, linestyle="--", label="0 ns (met)")
    for b, v in zip(bars, wns):
        off = 0.012 if v >= 0 else -0.012
        va = "bottom" if v >= 0 else "top"
        ax.text(b.get_x() + b.get_width() / 2, v + off, f"{v:+.3f}",
                ha="center", va=va, fontsize=10, fontweight="bold", color=GRAY)
    ax.set_ylabel("Setup WNS (ns)")
    ax.set_title("100 MHz setup WNS — closure trajectory", color=GRAY, fontweight="bold")
    ax.set_ylim(-0.45, 0.12)
    ax.legend(loc="lower right", frameon=False)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    fig.tight_layout()
    out = os.path.join(PNG, "10_timing_closure.png")
    fig.savefig(out, dpi=DPI)
    plt.close(fig)
    print("wrote", out)


def plot_utilization():
    labels = ["LUTs", "FF", "BRAM", "DSP"]
    pct = [59.2, 22.6, 16.3, 0.0]
    annot = ["37,555 / 63,400", "28,683 / 126,800", "22 / 135", "0 / 240"]

    fig, ax = plt.subplots(figsize=(8, 4.5))
    bars = ax.bar(labels, pct, color=[FOREST, "#3f9e3f", "#6fb96f", "#a9d6a9"],
                  edgecolor=GRAY, width=0.6)
    for b, p, a in zip(bars, pct, annot):
        ax.text(b.get_x() + b.get_width() / 2, p + 1.2, f"{p:.1f}%",
                ha="center", va="bottom", fontsize=10, fontweight="bold", color=GRAY)
        ax.text(b.get_x() + b.get_width() / 2, max(p / 2, 3.0), a,
                ha="center", va="center", fontsize=8, color="white" if p > 10 else GRAY,
                rotation=90 if p < 10 else 0)
    ax.set_ylabel("Utilization (% of xc7a100t)")
    ax.set_title("Post-route utilization — NUM_CHANNELS=4 board build",
                 color=GRAY, fontweight="bold")
    ax.set_ylim(0, 70)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    fig.tight_layout()
    out = os.path.join(PNG, "11_utilization.png")
    fig.savefig(out, dpi=DPI)
    plt.close(fig)
    print("wrote", out)


def plot_suite_grid(suite_path):
    with open(suite_path) as f:
        data = json.load(f)
    configs = data["configs"]
    total = data["total"]
    passed = data["passed"]
    failed = data["failed"]

    # Rows: (channels, backpressure, seed) ; Cols: beats.
    beats_axis = sorted({c["beats"] for c in configs})
    chans_axis = sorted({c["active_channels"] for c in configs})
    bp_axis = [False, True]
    seed_axis = sorted({c["base_seed_label"] for c in configs})

    def cell_pass(ch, be, bp, seed):
        for c in configs:
            if (c["active_channels"] == ch and c["beats"] == be
                    and c["source_backpressure"] == bp
                    and c["base_seed_label"] == seed):
                return c["pass"], c["sink_pass"], c["source_pass"]
        return None, None, None

    rows = []
    for ch in chans_axis:
        for bp in bp_axis:
            for seed in seed_axis:
                rows.append((ch, bp, seed))

    ncols = len(beats_axis)
    nrows = len(rows)

    fig, ax = plt.subplots(figsize=(9, 0.42 * nrows + 1.8))
    green = "#2e9e2e"
    red = "#b22222"

    for r, (ch, bp, seed) in enumerate(rows):
        y = nrows - 1 - r
        for cix, be in enumerate(beats_axis):
            ok, sink_ok, src_ok = cell_pass(ch, be, bp, seed)
            color = green if ok else (red if ok is False else "#dddddd")
            ax.add_patch(plt.Rectangle((cix, y), 0.92, 0.92, facecolor=color,
                                       edgecolor="white", linewidth=1.5))
            mark = "PASS" if ok else ("FAIL" if ok is False else "-")
            ax.text(cix + 0.46, y + 0.46, mark, ha="center", va="center",
                    fontsize=7, color="white", fontweight="bold")

    ax.set_xticks([i + 0.46 for i in range(ncols)])
    ax.set_xticklabels([f"{b} beat{'s' if b != 1 else ''}" for b in beats_axis], fontsize=8)
    ax.xaxis.tick_top()
    ax.set_yticks([nrows - 1 - r + 0.46 for r in range(nrows)])
    ax.set_yticklabels(
        [f"{ch}ch  bp={'on' if bp else 'off'}  seed={seed}" for (ch, bp, seed) in rows],
        fontsize=7)
    ax.set_xlim(0, ncols)
    ax.set_ylim(0, nrows)
    ax.set_aspect("equal")
    for sp in ax.spines.values():
        sp.set_visible(False)
    ax.tick_params(length=0)

    title = (f"On-silicon suite — {passed}/{total} configs PASS "
             f"(both paths CRC-verified, {failed} fail)")
    ax.set_title(title, color=GRAY, fontweight="bold", pad=26)
    fig.tight_layout()
    out = os.path.join(PNG, "12_suite_grid.png")
    fig.savefig(out, dpi=DPI, bbox_inches="tight")
    plt.close(fig)
    print("wrote", out, "  from", os.path.basename(suite_path))


if __name__ == "__main__":
    plot_timing_closure()
    plot_utilization()
    plot_suite_grid(latest_suite_json())
