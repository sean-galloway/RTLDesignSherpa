#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Plot the controller sweeps (char_<ctrl>_<tag>_<profile>_<date>.csv) as PNGs:
the knees and the side-by-side the owner asked for (2026-10-30), in the STREAM
characterization style (Genesys2/stream/bin/plot_char_reports.py, the repo's
most developed visualization tooling): a line family where a bend has to be
legible, an annotated heatmap for the envelope, grouped bars for the
side-by-side, symlog never -- every x here is a small integer.

Series are named on the command line as label=ctrl:tag:date[:config], e.g.
    granite75=granite:sweep75:2026-10-29:open_page
    litedram75=litedram:sweep75:2026-10-29
    pumice50=pumice:sweep:2026-10-30:open_page
The config picks ONE preset out of a multi-config CSV (LiteDRAM has one).

Figures (all MB/s, each series' peak drawn as a dotted line):
  threads_knee_pair.png / _oct.png   half_threads: bandwidth vs threads 1..8
  gap_knee.png                       half_gap: bandwidth vs fixed idle gap 0..7
  burst_len_<family>.png             every: bandwidth vs burst length 4/8/16
  patterns_bars.png                  every pattern at bl8, grouped by series
  envelope_heatmap.png               every scenario x series, percent of peak
"""
import argparse, csv, os, sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

C = os.path.join(os.environ.get("REPO_ROOT", "/mnt/data/github/RTLDesignSherpa"),
                 "projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/char_results")
PEAK = {"granite": {75.0: 600, 100.0: 800}, "litedram": {75.0: 600, 100.0: 800},
        "pumice": {50.0: 400, 75.0: 600, 100.0: 800}}
COLORS = plt.cm.tab10(np.linspace(0, 1, 10))


def f(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


class Series:
    def __init__(self, spec):
        self.label, rest = spec.split("=", 1)
        parts = rest.split(":")
        self.ctrl, self.tag, self.date = parts[0], parts[1], parts[2]
        self.config = parts[3] if len(parts) > 3 else None
        self.cache = {}
        self.clk = None

    def rows(self, profile):
        if profile in self.cache:
            return self.cache[profile]
        p = os.path.join(C, f"char_{self.ctrl}_{self.tag}_{profile}_{self.date}.csv")
        rows = list(csv.DictReader(open(p))) if os.path.exists(p) else []
        if self.config:
            rows = [r for r in rows if r["config"] == self.config]
        if rows and self.clk is None:
            self.clk = f(rows[0].get("clk_mhz"))
        self.cache[profile] = rows
        return rows

    def peak(self):
        return PEAK.get(self.ctrl, {}).get(self.clk or 0.0)

    def get(self, profile, scenario):
        for r in self.rows(profile):
            if r["scenario"] == scenario:
                return f(r["wr_bw_mb_s"]), f(r["rd_bw_mb_s"])
        return None, None


def save(fig, outdir, name):
    os.makedirs(outdir, exist_ok=True)
    p = os.path.join(outdir, name)
    fig.tight_layout(); fig.savefig(p, dpi=130, bbox_inches="tight"); plt.close(fig)
    print(f"  wrote {p}", file=sys.stderr)
    return name


def knee(series, profile, prefix, xs, xlabel, title, outdir, name, pct=False):
    """pct=True plots percent of each series' own peak, so series at different
    clocks (pumice 50, granite 75, LiteDRAM 100) sit on one axis."""
    fig, ax = plt.subplots(figsize=(7.5, 4.4))
    drew = False
    for k, s in enumerate(series):
        scale = (100.0 / s.peak()) if (pct and s.peak()) else 1.0
        wr, rd = [], []
        for x in xs:
            w, r = s.get(profile, f"{prefix}{x}")
            wr.append(w * scale if w is not None else np.nan); rd.append(r * scale if r is not None else np.nan)
        if all(np.isnan(wr)) and all(np.isnan(rd)):
            continue
        drew = True
        ax.plot(xs, rd, "-o", color=COLORS[k], label=f"{s.label} read")
        ax.plot(xs, wr, "--s", color=COLORS[k], alpha=0.7, label=f"{s.label} write")
        if s.peak() and not pct:
            ax.axhline(s.peak(), color=COLORS[k], ls=":", lw=0.8)
    if not drew:
        plt.close(fig); return None
    ax.set_xticks(xs); ax.set_xlabel(xlabel); ax.set_title(title)
    ax.set_ylabel("percent of each series' peak" if pct else "MB/s")
    if pct:
        ax.set_ylim(0, 100)
    ax.grid(True, alpha=0.3); ax.legend(fontsize=7, ncol=2)
    return save(fig, outdir, name)


def burst_len(series, family, outdir):
    xs = [4, 8, 16]
    fig, ax = plt.subplots(figsize=(7, 4.2))
    drew = False
    for k, s in enumerate(series):
        rd = [s.get("every", f"{family}_bl{b}")[1] for b in xs]
        wr = [s.get("every", f"{family}_bl{b}")[0] for b in xs]
        if all(v is None for v in rd):
            continue
        drew = True
        ax.plot(xs, [v if v is not None else np.nan for v in rd], "-o", color=COLORS[k], label=f"{s.label} read")
        ax.plot(xs, [v if v is not None else np.nan for v in wr], "--s", color=COLORS[k], alpha=0.7, label=f"{s.label} write")
        if s.peak():
            ax.axhline(s.peak(), color=COLORS[k], ls=":", lw=0.8)
    if not drew:
        plt.close(fig); return None
    ax.set_xscale("log", base=2); ax.set_xticks(xs); ax.set_xticklabels([str(x) for x in xs])
    ax.set_xlabel("host burst length (beats)"); ax.set_ylabel("MB/s")
    ax.set_title(f"{family}: bandwidth vs burst length"); ax.grid(True, alpha=0.3); ax.legend(fontsize=7, ncol=2)
    return save(fig, outdir, f"burst_len_{family}.png")


PATTERNS = [("every", "incremental_bl8", "incremental"), ("every", "row_major_bl8", "row_major"),
            ("every", "col_major_bl8", "col_major"), ("every", "col_major_interleaved_bl8", "col_major\ninterleaved"),
            ("windows", "mixed_bl8", "mixed"), ("windows", "row_thrash_bl8", "row_thrash"), ("windows", "random_bl8", "random"),
            ("half_threads", "half_pair_thr1", "half_pair\n1 thread"), ("half_threads", "half_pair_thr4", "half_pair\n4 threads"),
            ("half_threads", "half_oct_thr4", "half_oct\n4 threads"), ("concurrent", "incremental_bl8", "concurrent\n1w+1r incr"),
            ("concurrent", "col_major_bl8", "concurrent\n1w+1r col_major")]


def bars(series, outdir):
    fig, axes = plt.subplots(2, 1, figsize=(12, 7.5), sharex=True)
    n = len(series); width = 0.8 / n
    xs = np.arange(len(PATTERNS))
    for k, s in enumerate(series):
        wr = [s.get(p, sc)[0] for p, sc, _ in PATTERNS]
        rd = [s.get(p, sc)[1] for p, sc, _ in PATTERNS]
        off = (k - (n - 1) / 2) * width
        axes[0].bar(xs + off, [v if v is not None else 0 for v in wr], width, color=COLORS[k], label=s.label)
        axes[1].bar(xs + off, [v if v is not None else 0 for v in rd], width, color=COLORS[k], label=s.label)
        if s.peak():
            for ax in axes:
                ax.axhline(s.peak(), color=COLORS[k], ls=":", lw=0.8)
    axes[0].set_ylabel("write MB/s"); axes[1].set_ylabel("read MB/s")
    axes[1].set_xticks(xs); axes[1].set_xticklabels([lab for _, _, lab in PATTERNS], fontsize=8)
    axes[0].set_title("every pattern at bl8, side by side (dotted = each series' peak)")
    for ax in axes:
        ax.grid(True, axis="y", alpha=0.3)
    axes[0].legend(fontsize=8, ncol=min(n, 5))
    return save(fig, outdir, "patterns_bars.png")


def envelope(series, outdir):
    scen = list(dict.fromkeys(r["scenario"] for s in series for r in s.rows("every")))
    if not scen:
        return None
    Z = np.full((len(scen), len(series)), np.nan)
    for j, s in enumerate(series):
        pk = s.peak() or np.nan
        for i, sc in enumerate(scen):
            w, r = s.get("every", sc)
            if r is not None:
                Z[i, j] = 100.0 * max(w or 0, r or 0) / pk
    fig, ax = plt.subplots(figsize=(2.2 + 1.3 * len(series), 0.42 * len(scen) + 1.5))
    im = ax.imshow(Z, aspect="auto", cmap="viridis", vmin=0, vmax=100)
    ax.set_xticks(range(len(series))); ax.set_xticklabels([s.label for s in series], fontsize=8)
    ax.set_yticks(range(len(scen))); ax.set_yticklabels(scen, fontsize=7)
    for i in range(len(scen)):
        for j in range(len(series)):
            if not np.isnan(Z[i, j]):
                ax.text(j, i, f"{Z[i, j]:.0f}", ha="center", va="center", color="white", fontsize=7)
    fig.colorbar(im, ax=ax, label="best of write/read, percent of peak")
    ax.set_title("the envelope: every scenario, percent of each series' peak")
    return save(fig, outdir, "envelope_heatmap.png")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("series", nargs="+", help="label=ctrl:tag:date[:config]")
    ap.add_argument("--out", default=os.path.join(C, "plots"))
    a = ap.parse_args()
    series = [Series(x) for x in a.series]
    for s in series:
        s.rows("every"); s.rows("half_threads")
        print(f"series {s.label}: {s.ctrl} {s.tag} clk {s.clk} MHz peak {s.peak()} MB/s", file=sys.stderr)
    made = []
    made.append(knee(series, "half_threads", "half_pair_thr", list(range(1, 9)), "injector threads",
                     "half_pair (l0 h0 l1 h1 ...): bandwidth vs threads", a.out, "threads_knee_pair.png"))
    made.append(knee(series, "half_threads", "half_oct_thr", list(range(1, 9)), "injector threads",
                     "half_oct (l0..l7 h0..h7): bandwidth vs threads", a.out, "threads_knee_oct.png"))
    made.append(knee(series, "half_gap", "half_pair_gap", list(range(0, 8)), "idle clocks between transactions",
                     "half_pair at a fixed gap: bandwidth vs gap", a.out, "gap_knee.png"))
    made.append(knee(series, "half_threads", "half_pair_thr", list(range(1, 9)), "injector threads",
                     "half_pair: percent of peak vs threads", a.out, "threads_knee_pair_pct.png", pct=True))
    made.append(knee(series, "half_gap", "half_pair_gap", list(range(0, 8)), "idle clocks between transactions",
                     "half_pair at a fixed gap: percent of peak vs gap", a.out, "gap_knee_pct.png", pct=True))
    for fam in ("incremental", "row_major", "col_major", "col_major_interleaved"):
        made.append(burst_len(series, fam, a.out))
    made.append(bars(series, a.out))
    made.append(envelope(series, a.out))
    print("\n".join(f"![{m}](plots/{m})" for m in made if m))


if __name__ == "__main__":
    main()
