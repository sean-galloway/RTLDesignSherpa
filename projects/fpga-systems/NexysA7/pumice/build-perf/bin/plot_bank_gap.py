#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Plot a bank_gap_sweep.json as PNGs.

Ported from the STREAM characterization plot library
(Genesys2/stream/bin/plot_char_reports.py), which is the most developed
visualization tooling in the repo. What came across, and why each one earns
its place:

  line_family      bandwidth against gap, one line per generator count. The
                   BEND is the point of the whole sweep and a line family is
                   where a bend is legible. symlog on the x axis, not log:
                   gap 0 is a real measurement and a log axis silently drops
                   it.
  heatmap          the same data as a surface, every cell annotated with its
                   own number, missing points left as NaN holes rather than
                   filled with zero. The surface shows the envelope; the lines
                   show the knee. Both, always -- they answer different
                   questions.
  buckets_stacked  the four-bucket cycle classification, which is what turns a
                   bandwidth shortfall into a named cause. Rising STARVATION
                   means the generators stopped asking, so the gap did it;
                   rising BACKPRESSURE means the controller stopped accepting,
                   so the DRAM did. Colours are semantic: green productive,
                   red blocked, orange starved, grey idle. You read the failure
                   mode off whichever colour grows.
  efficiency_pair  bus bandwidth against the datapath's own productive
                   fraction, with the gap between them shaded. The band IS the
                   overhead, drawn as an area rather than left as a
                   subtraction the reader has to perform.

Every bandwidth axis carries the peak as a dotted reference line in the
series' own colour. A number without its ceiling beside it is not a
measurement, it is a quantity.

Colours are the house pair from stream_char_guide_styles.yaml, so a PNG
dropped into a document matches the prose around it.

    python3 bin/plot_bank_gap.py reports/bank_gap_sweep.json
    python3 bin/plot_bank_gap.py reports/bank_gap_sweep.json --outdir reports/plots
"""
import argparse
import json
import os
import sys

import matplotlib
matplotlib.use("Agg")                  # headless: this runs on a build box
import matplotlib.pyplot as plt        # noqa: E402
import numpy as np                     # noqa: E402

GREEN = "#228B22"      # house colors.primary
GRAY  = "#404040"      # house colors.secondary
RED   = "#c0392b"      # blocked
ORANGE = "#e08a00"     # starved
SILVER = "#999999"     # idle
OVERHEAD = "#cc6600"


def _save(fig, outdir, name):
    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, name)
    fig.tight_layout()
    fig.savefig(path, dpi=130, bbox_inches="tight")
    plt.close(fig)
    print(f"  wrote {path}", file=sys.stderr)
    return path


def _sanity(rows, path):
    """Refuse a record file that cannot have come from the hardware.

    A results file that is silently fiction is worse than a missing one: it
    still plots, and the plot still looks like a measurement. On 2026-09-14 a
    board-less pytest run overwrote this file with mock rows claiming 2280
    MB/s -- 3.8x the part's physical peak -- and nothing anywhere complained.
    Bandwidth above the ceiling stored in the record itself is impossible, so
    check it before drawing anything.
    """
    bad = [r for r in rows
           if any(r.get(k, 0) > r.get("peak_mb_s", float("inf")) * 1.01
                  for k in ("wr", "rd"))]
    if bad:
        r = bad[0]
        raise SystemExit(
            f"{path}: {len(bad)} of {len(rows)} records exceed their own peak "
            f"({r.get('rd'):.0f} / {r.get('wr'):.0f} MB/s against a "
            f"{r.get('peak_mb_s'):.0f} MB/s ceiling). This file did not come "
            f"from the board -- re-run the sweep before plotting it.")


def _sel(rows, **kw):
    return [r for r in rows if all(r.get(k) == v for k, v in kw.items())]


def _axes(rows, key):
    return sorted({r[key] for r in rows})


def line_family(rows, order, series, outdir):
    """Bandwidth vs gap, one line per generator count -- where a bend reads."""
    gens = _axes(rows, "n_gen")
    fig, ax = plt.subplots(figsize=(7, 4.2))
    cmap = plt.cm.viridis(np.linspace(0, 0.9, max(len(gens), 1)))
    peak = rows[0].get("peak_mb_s", 0.0)
    for k, n in enumerate(gens):
        sub = sorted(_sel(rows, n_gen=n, order=order), key=lambda r: r["gap"])
        if not sub:
            continue
        ax.plot([r["gap"] for r in sub], [r[series] for r in sub], "-o",
                color=cmap[k], label=f"{n}+{n} gens")
        # Ring any point whose data did not verify. The bandwidth number is
        # still a real measurement -- those bytes did move -- but the point
        # ran a configuration that returns wrong data (PUMICE-037, reader gap
        # >= 8 with a concurrent writer), and a curve that does not say so
        # invites someone to quote it as a clean operating point.
        bad = [r for r in sub if r.get("mism")]
        if bad:
            ax.plot([r["gap"] for r in bad], [r[series] for r in bad], "o",
                    mfc="none", mec="#B22222", mew=1.6, ms=11, ls="none",
                    label="_nolegend_")
    if peak:
        # A theoretical bound is always a dotted axhline at alpha 0.6.
        ax.axhline(peak, color=GRAY, ls=":", alpha=0.6,
                   label=f"peak {peak:.0f} MB/s")
    # symlog, not log: gap 0 is a real point and log would drop it.
    ax.set_xscale("symlog")
    ax.set_xlabel("inter-burst gap (clocks)")
    ax.set_ylabel(f"{series} bandwidth (MB/s)")
    ax.set_title(f"{order}: {series} bandwidth vs gap")
    ax.grid(True, alpha=0.3)
    if any(r.get("mism") for r in rows):
        ax.plot([], [], "o", mfc="none", mec="#B22222", mew=1.6, ms=11,
                ls="none", label="data did NOT verify")
    ax.legend(fontsize=8)
    return _save(fig, outdir, f"lines_{order}_{series}.png")


def heatmap(rows, order, series, outdir):
    """The same data as a surface. Holes stay holes."""
    gaps = _axes(rows, "gap")
    gens = _axes(rows, "n_gen")
    Z = np.full((len(gens), len(gaps)), np.nan)
    for i, n in enumerate(gens):
        for j, g in enumerate(gaps):
            hit = _sel(rows, n_gen=n, gap=g, order=order)
            if hit:
                Z[i, j] = hit[0][series]
    fig, ax = plt.subplots(figsize=(7.5, 4.6))
    im = ax.imshow(Z, origin="lower", aspect="auto", cmap="viridis",
                   interpolation="nearest")
    ax.set_xticks(range(len(gaps)));  ax.set_xticklabels(gaps)
    ax.set_yticks(range(len(gens)));  ax.set_yticklabels([f"{n}+{n}" for n in gens])
    hi = np.nanmax(Z) if np.isfinite(Z).any() else 0.0
    for i in range(len(gens)):
        for j in range(len(gaps)):
            if not np.isnan(Z[i, j]):
                # Contrast-aware, so the number stays readable at both ends.
                ax.text(j, i, f"{Z[i, j]:.0f}", ha="center", va="center",
                        fontsize=7,
                        color="white" if Z[i, j] < hi / 2 else "black")
    ax.set_xlabel("inter-burst gap (clocks)")
    ax.set_ylabel("generators")
    ax.set_title(f"{order}: {series} bandwidth (MB/s)")
    fig.colorbar(im, ax=ax, label="MB/s")
    return _save(fig, outdir, f"heat_{order}_{series}.png")


def buckets_stacked(rows, order, n_gen, direction, outdir):
    """Four-bucket cycle classification: reads the CAUSE off the colour."""
    sub = sorted(_sel(rows, n_gen=n_gen, order=order), key=lambda r: r["gap"])
    if not sub:
        return None
    xs = [r["gap"] for r in sub]
    b = [r["buckets"][direction] for r in sub]
    parts = [[x[f"{k}_frac"] * 100.0 for x in b]
             for k in ("productive", "backpressure", "starvation", "idle")]
    fig, ax = plt.subplots(figsize=(7, 4.2))
    ax.stackplot(xs, *parts,
                 labels=["productive", "backpressure", "starvation", "idle"],
                 colors=[GREEN, RED, ORANGE, SILVER], alpha=0.85)
    ax.set_ylim(0, 100)
    ax.set_xlabel("inter-burst gap (clocks)")
    ax.set_ylabel("% of cycles")
    ax.set_title(f"{order} {direction} cycle breakdown, {n_gen}+{n_gen} gens")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8, loc="lower left")
    return _save(fig, outdir, f"buckets_{order}_{direction}_g{n_gen}.png")


def efficiency_pair(rows, order, n_gen, outdir):
    """Bus rate against datapath productive fraction; the gap is the overhead."""
    sub = sorted(_sel(rows, n_gen=n_gen, order=order), key=lambda r: r["gap"])
    if not sub:
        return None
    xs = [r["gap"] for r in sub]
    peak = sub[0].get("peak_mb_s") or 1.0
    bus_pct = [r["bus"] / peak * 100.0 for r in sub]
    dp_pct = [(r["buckets"]["rd"]["productive_frac"]
               + r["buckets"]["wr"]["productive_frac"]) / 2 * 100.0 for r in sub]
    fig, ax = plt.subplots(figsize=(7, 4.2))
    ax.plot(xs, dp_pct, "-o", color=GREEN, label="datapath productive (steady state)")
    ax.plot(xs, bus_pct, "--s", color=GRAY, label="bus bandwidth as % of peak")
    ax.fill_between(xs, bus_pct, dp_pct, color=OVERHEAD, alpha=0.15,
                    label="overhead (the gap between them)")
    ax.set_ylim(0, 100)
    ax.set_xlabel("inter-burst gap (clocks)")
    ax.set_ylabel("%")
    ax.set_title(f"{order}: efficiency pair, {n_gen}+{n_gen} gens")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8)
    return _save(fig, outdir, f"effpair_{order}_g{n_gen}.png")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("json", help="bank_gap_sweep.json")
    ap.add_argument("--outdir", default=None,
                    help="default: <json dir>/plots")
    a = ap.parse_args(argv)

    with open(a.json) as f:
        rows = json.load(f)
    if not rows:
        print("no records in that file", file=sys.stderr)
        return 1
    _sanity(rows, a.json)
    outdir = a.outdir or os.path.join(os.path.dirname(a.json) or ".", "plots")

    orders = sorted({r["order"] for r in rows})
    gens = _axes(rows, "n_gen")
    widest = max(gens)
    n = 0
    for order in orders:
        for series in ("bus", "rd", "wr"):
            line_family(rows, order, series, outdir); n += 1
        heatmap(rows, order, "bus", outdir); n += 1
        # The cycle breakdown only needs the widest configuration: it answers
        # "what stopped the bus", and the widest one is where it stops hardest.
        for direction in ("rd", "wr"):
            if buckets_stacked(rows, order, widest, direction, outdir):
                n += 1
        if efficiency_pair(rows, order, widest, outdir):
            n += 1
    print(f"{n} figures -> {outdir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
