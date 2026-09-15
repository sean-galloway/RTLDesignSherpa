#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# plot_char_reports.py — figures for the RAPIDS beats characterization perf
# report. Consumes the run_characterization.py --results JSON (per-config
# perf.ifaces from the on-chip axi_bus_meter / axis_bus_meter) and emits PNGs.
# Mirrors the STREAM char plot script's house look (forest-green/gray, dpi 130).
#
# Usage:
#   source env_python
#   python3 host/plot_char_reports.py \
#       --size   ../reports/perf/json/genesys_8ch_size_sweep.json \
#       --outdir ../reports/perf/plots
import argparse
import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# House palette (matches perf_styles.yaml + STREAM plots).
GREEN = "#228B22"   # AXI4 (the memory-bus side)
GRAY = "#404040"
BLUE = "#1f6fb4"    # AXIS (the network/stream side)
ORANGE = "#cc6600"
BYTES_PER_BEAT = 64
PEAK_GB_S = BYTES_PER_BEAT * 100e6 / 1e9   # 6.4 GB/s at 100 MHz

# iface key -> (display label, colour, marker)
IFACE = {
    "sin":  ("AXIS-in (sink ingress)",  BLUE,   "-o"),
    "wr":   ("AXI4-wr (sink egress)",   GREEN,  "-s"),
    "rd":   ("AXI4-rd (source ingress)", GRAY,  "-^"),
    "sout": ("AXIS-out (source egress)", ORANGE, "-d"),
}


def load(path):
    with open(path) as fh:
        return json.load(fh)


def _save(fig, outdir, name):
    os.makedirs(outdir, exist_ok=True)
    p = os.path.join(outdir, name)
    fig.savefig(p, dpi=130, bbox_inches="tight")
    plt.close(fig)
    print(f"  wrote {p}")


def _max_channels(configs):
    return max((r.get("active_channels", 1) for r in configs if r.get("pass")),
               default=1)


def _series(configs, channels=None):
    """Return {iface: [(bytes_per_ch, util, eff_bw), ...]} over passing configs.
    If `channels` is set, keep only that active-channel count (so the size sweep
    is a single clean curve when the matrix also sweeps channels)."""
    out = {k: [] for k in IFACE}
    for r in configs:
        if not r.get("pass"):
            continue
        if channels is not None and r.get("active_channels") != channels:
            continue
        xb = r["beats"] * BYTES_PER_BEAT
        for pathkey in ("sink", "source"):
            ifs = ((r.get(pathkey) or {}).get("perf") or {}).get("ifaces") or {}
            for key, rec in ifs.items():
                if key in out:
                    out[key].append((xb, rec["util"] * 100.0,
                                     rec.get("eff_bw_gb_s", 0.0)))
    for k in out:
        out[k].sort()
    return out


def size_util(series, outdir, name="size_util.png"):
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for key, (label, color, mk) in IFACE.items():
        pts = series.get(key) or []
        if not pts:
            continue
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        ax.plot(xs, ys, mk, color=color, label=label, linewidth=1.8, markersize=6)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_xscale("log", base=2)
    ax.set_xlabel("transfer size per channel (bytes, 64 B/beat, log scale)")
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 105)
    ax.set_title("RAPIDS beats — engaged utilization vs transfer size (Genesys 2, 8 ch)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8, loc="lower right")
    _save(fig, outdir, name)


def size_bw(series, outdir, name="size_bw.png"):
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for key, (label, color, mk) in IFACE.items():
        pts = series.get(key) or []
        if not pts:
            continue
        xs = [p[0] for p in pts]
        ys = [p[2] for p in pts]
        ax.plot(xs, ys, mk, color=color, label=label, linewidth=1.8, markersize=6)
    ax.axhline(PEAK_GB_S, color=ORANGE, ls="--", lw=1,
               label=f"line rate {PEAK_GB_S:.1f} GB/s")
    ax.set_xscale("log", base=2)
    ax.set_xlabel("transfer size per channel (bytes, 64 B/beat, log scale)")
    ax.set_ylabel("effective bandwidth per direction (GB/s)")
    ax.set_ylim(0, PEAK_GB_S * 1.08)
    ax.set_title("RAPIDS beats — effective bandwidth vs transfer size (Genesys 2, 8 ch)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8, loc="lower right")
    _save(fig, outdir, name)


def headline_bar(configs, outdir, name="headline_8ch.png"):
    """Bar of the four interfaces at the largest passing transfer size."""
    best = None
    for r in configs:
        if r.get("pass"):
            best = r if (best is None or r["beats"] > best["beats"]) else best
    if best is None:
        return
    vals, labels, colors = [], [], []
    for pathkey in ("sink", "source"):
        ifs = ((best.get(pathkey) or {}).get("perf") or {}).get("ifaces") or {}
        for key, rec in ifs.items():
            if key in IFACE:
                vals.append(rec["util"] * 100.0)
                labels.append(IFACE[key][0].split(" (")[0])
                colors.append(IFACE[key][1])
    fig, ax = plt.subplots(figsize=(7, 4.2))
    bars = ax.bar(labels, vals, color=colors, alpha=0.88)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 108)
    kb = best["beats"] * BYTES_PER_BEAT / 1024
    ax.set_title(f"RAPIDS beats — 8-channel line-rate ({kb:.0f} KB/ch transfer, Genesys 2)")
    for b, v in zip(bars, vals):
        ax.text(b.get_x() + b.get_width() / 2, v + 1, f"{v:.1f}%",
                ha="center", va="bottom", fontsize=8)
    _save(fig, outdir, name)


def size_buckets(configs, outdir, name="size_buckets.png"):
    """Productive vs (starvation+idle) share of the AXI4-wr window vs size —
    shows the one-time startup overhead shrinking as transfers amortize."""
    xs, prod, over = [], [], []
    for r in sorted((c for c in configs if c.get("pass")), key=lambda c: c["beats"]):
        ifs = ((r.get("sink") or {}).get("perf") or {}).get("ifaces") or {}
        rec = ifs.get("wr")
        if not rec:
            continue
        b = rec["buckets"]
        tot = max(1, b["prod"] + b["bp"] + b["starv"] + b["idle"])
        xs.append(r["beats"] * BYTES_PER_BEAT)
        prod.append(100.0 * b["prod"] / tot)
        over.append(100.0 * (b["bp"] + b["starv"] + b["idle"]) / tot)
    if not xs:
        return
    fig, ax = plt.subplots(figsize=(7, 4.2))
    ax.bar([str(x) for x in xs], prod, color=GREEN, label="productive")
    ax.bar([str(x) for x in xs], over, bottom=prod, color=ORANGE, alpha=0.75,
           label="startup / bubble (bp+starv+idle)")
    ax.set_xlabel("transfer size per channel (bytes)")
    ax.set_ylabel("AXI4-wr window cycles (%)")
    ax.set_ylim(0, 100)
    ax.set_title("RAPIDS beats — where the cycles go vs transfer size (sink write)")
    ax.legend(fontsize=8, loc="lower right")
    _save(fig, outdir, name)


def channel_scaling(configs, outdir, name="channel_scaling.png"):
    """Engaged utilization vs active channel count at the largest transfer —
    shows per-channel independence (the engine holds line rate 1→8 ch)."""
    passing = [c for c in configs if c.get("pass")]
    if not passing:
        return
    big = max(c["beats"] for c in passing)
    rows = sorted((c for c in passing if c["beats"] == big),
                  key=lambda c: c["active_channels"])
    if len({c["active_channels"] for c in rows}) < 2:
        return  # not a channel sweep
    data = {k: ([], []) for k in IFACE}   # iface -> (channels[], util[])
    for r in rows:
        for pathkey in ("sink", "source"):
            ifs = ((r.get(pathkey) or {}).get("perf") or {}).get("ifaces") or {}
            for key, rec in ifs.items():
                if key in data:
                    data[key][0].append(r["active_channels"])
                    data[key][1].append(rec["util"] * 100.0)
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for key, (label, color, mk) in IFACE.items():
        xs, ys = data[key]
        if xs:
            ax.plot(xs, ys, mk, color=color, label=label, linewidth=1.8, markersize=6)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_xlabel("active DMA channels")
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 105)
    ax.set_xticks(sorted({c["active_channels"] for c in rows}))
    kb = big * BYTES_PER_BEAT / 1024
    ax.set_title(f"RAPIDS beats — utilization vs channel count ({kb:.0f} KB/ch, Genesys 2)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8, loc="lower right")
    _save(fig, outdir, name)


def main():
    ap = argparse.ArgumentParser(description="RAPIDS beats perf report figures")
    ap.add_argument("--size", required=True, help="merged size-sweep / matrix JSON")
    ap.add_argument("--outdir", required=True)
    args = ap.parse_args()

    d = load(args.size)
    configs = d.get("configs", [])
    nch = _max_channels(configs)   # size plots use the widest (8ch) curve
    series = _series(configs, channels=nch)
    print(f"plotting {sum(1 for c in configs if c.get('pass'))}/{len(configs)} "
          f"passing configs (size curves at {nch} ch) -> {args.outdir}")
    size_util(series, args.outdir)
    size_bw(series, args.outdir)
    headline_bar([c for c in configs if c.get("active_channels") == nch], args.outdir)
    size_buckets([c for c in configs if c.get("active_channels") == nch], args.outdir)
    channel_scaling(configs, args.outdir)


if __name__ == "__main__":
    main()
