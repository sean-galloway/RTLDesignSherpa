#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# plot_compression_report.py — figures for the compression report.
#
# Primary data is the OFFLINE bit-exact half-beat model replayed on the real
# 682-record on-board capture (deterministic, CRC-independent, exactly what the
# synthesized codec emits for that record stream). Produces:
#   - reduction vs stream length (prefix replay) -> warm-up amortization
#   - codec comparison bar (full 64b vs half-beat vs ceilings)
#   - tier composition (half / full / raw)
#   - live on-board desc-sweep confirmation (clean CRC=ok points only)
import argparse
import json
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from monbus_halfbeat_model import classify

GREEN = "#228B22"
GRAY = "#404040"
LIGHT = "#7BC47B"


def _save(fig, outdir, name):
    os.makedirs(outdir, exist_ok=True)
    p = os.path.join(outdir, name)
    fig.tight_layout()
    fig.savefig(p, dpi=130, bbox_inches="tight")
    plt.close(fig)
    print(f"  wrote {p}", file=sys.stderr)


def load_capture(path):
    doc = json.load(open(path))
    recs = doc["records"] if isinstance(doc, dict) else doc
    return [(int(r["packet"], 16), int(r["timestamp"], 16)) for r in recs]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--capture", required=True, help="real monbus capture JSON")
    ap.add_argument("--outdir", required=True)
    args = ap.parse_args()

    recs = load_capture(args.capture)
    full = classify(recs)
    print(f"full: records={full.records} h={full.h:.3f} "
          f"half={full.half} full={full.full} raw={full.raw} "
          f"current={full.red_current*100:.1f}% halfbeat={full.red_halfbeat*100:.1f}%",
          file=sys.stderr)

    # ---- Fig 1: reduction vs stream length (prefix replay) ----
    ns = [n for n in (25, 50, 75, 100, 150, 200, 300, 400, 500, 600, len(recs))
          if n <= len(recs)]
    cur, half = [], []
    for n in ns:
        r = classify(recs[:n])
        cur.append(r.red_current * 100)
        half.append(r.red_halfbeat * 100)
    fig, ax = plt.subplots(figsize=(7, 4.2))
    ax.plot(ns, half, "-o", color=GREEN, label="half-beat (32b slot)")
    ax.plot(ns, cur, "--s", color=GRAY, label="current (64b slot)")
    ax.axhline(83.3, color=GREEN, ls=":", alpha=0.6, label="half-beat ceiling 83.3%")
    ax.axhline(66.7, color=GRAY, ls=":", alpha=0.6, label="64b ceiling 66.7%")
    ax.set_xlabel("records replayed (real desc-axi capture)")
    ax.set_ylabel("reduction vs raw 3-beat (%)")
    ax.set_title("Reduction vs stream length — CAM warm-up amortization")
    ax.set_ylim(0, 90)
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8, loc="lower right")
    _save(fig, args.outdir, "reduction_vs_length.png")

    # ---- Fig 2: codec comparison bar ----
    fig, ax = plt.subplots(figsize=(6, 4.2))
    labels = ["raw\n(baseline)", "current\n64b", "half-beat\n32b"]
    vals = [0.0, full.red_current * 100, full.red_halfbeat * 100]
    bars = ax.bar(labels, vals, color=[GRAY, "#888", GREEN])
    ax.axhline(66.7, color=GRAY, ls=":", alpha=0.6)
    ax.axhline(83.3, color=GREEN, ls=":", alpha=0.6)
    ax.text(1, 67.5, "64b ceiling 66.7%", fontsize=7, color=GRAY)
    ax.text(2, 84.1, "half-beat ceiling 83.3%", fontsize=7, color=GREEN)
    for b, v in zip(bars, vals):
        ax.text(b.get_x() + b.get_width() / 2, v + 1, f"{v:.1f}%",
                ha="center", fontsize=10, fontweight="bold")
    ax.set_ylabel("reduction vs raw 3-beat (%)")
    ax.set_ylim(0, 90)
    ax.set_title(f"Codec reduction on real capture ({full.records} records, h={full.h:.3f})")
    _save(fig, args.outdir, "codec_comparison.png")

    # ---- Fig 3: tier composition ----
    fig, ax = plt.subplots(figsize=(6, 4.2))
    parts = [full.half, full.full, full.raw]
    plabels = [f"half-fit\n{full.half} ({full.half/full.records*100:.0f}%)",
               f"full-only\n{full.full} ({full.full/full.records*100:.0f}%)",
               f"raw escape\n{full.raw} ({full.raw/full.records*100:.0f}%)"]
    ax.pie(parts, labels=plabels, colors=[GREEN, LIGHT, GRAY],
           autopct="", startangle=90, wedgeprops=dict(width=0.45))
    ax.set_title(f"Per-record classification — {full.records} records")
    _save(fig, args.outdir, "tier_composition.png")

    # ---- Fig 4: live on-board desc-sweep confirmation (clean points) ----
    # Clean CRC=ok 1ch desc-sweep points from hb_measure (debug-compl).
    live_desc = [(4, 0.0), (8, 29.2), (16, 52.1), (32, 63.5)]
    fig, ax = plt.subplots(figsize=(7, 4.2))
    xs = [r for r, _ in live_desc]
    ax.plot(xs, [v for _, v in live_desc], "-o", color=GREEN,
            label="live on-board (debug-compl, CRC ok)")
    ax.axhline(full.red_halfbeat * 100, color=GRAY, ls="--", alpha=0.7,
               label=f"offline full-capture {full.red_halfbeat*100:.1f}%")
    ax.set_xlabel("records in trace (1 ch, descriptor count varies)")
    ax.set_ylabel("half-beat reduction (%)")
    ax.set_title("Live HW confirmation — reduction climbs with records")
    ax.set_xscale("log", base=2)
    ax.set_xticks(xs); ax.set_xticklabels(xs)
    ax.grid(True, alpha=0.3); ax.legend(fontsize=8, loc="lower right")
    _save(fig, args.outdir, "live_confirmation.png")

    # Dump the numeric summary for the report text.
    summary = {
        "records": full.records, "h": full.h,
        "half": full.half, "full": full.full, "raw": full.raw,
        "beats_current": full.beats_current, "beats_halfbeat": full.beats_halfbeat,
        "red_current_pct": full.red_current * 100,
        "red_halfbeat_pct": full.red_halfbeat * 100,
    }
    json.dump(summary, open(os.path.join(args.outdir, "summary.json"), "w"), indent=2)
    print("compression plotting done", file=sys.stderr)


if __name__ == "__main__":
    main()
