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


# ---------------------------------------------------------------------------
# Interface OBSERVERS (USE_OBSERVERS=1 builds, rapids TASK-001). Same window as
# the bare meters, measured by the shared instrument: perf.observers[iface].
# ---------------------------------------------------------------------------

def _obs_series(configs, channels=None):
    """{iface: [(bytes_per_ch, util%, eff_bw, byte_bw|None), ...]} from the
    observers, over passing configs (optionally one channel count)."""
    out = {k: [] for k in IFACE}
    for r in configs:
        if not r.get("pass"):
            continue
        if channels is not None and r.get("active_channels") != channels:
            continue
        xb = r["beats"] * BYTES_PER_BEAT
        for pathkey in ("sink", "source"):
            obs = ((r.get(pathkey) or {}).get("perf") or {}).get("observers") or {}
            for key, rec in obs.items():
                if key in out:
                    out[key].append((xb, rec["util"] * 100.0,
                                     rec.get("eff_bw_gb_s", 0.0),
                                     rec.get("byte_bw_gb_s")))
    for k in out:
        out[k].sort()
    return out


def _has_observers(configs):
    return any(((r.get(pk) or {}).get("perf") or {}).get("observers")
               for r in configs for pk in ("sink", "source"))


def obs_size_util(obs_series, meter_series, outdir, name="obs_size_util.png"):
    """Observer engaged utilization vs size; the bare meter as a faint overlay,
    so any disagreement between the two instruments is visible on the plot."""
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for key, (label, color, mk) in IFACE.items():
        pts = obs_series.get(key) or []
        if pts:
            ax.plot([p[0] for p in pts], [p[1] for p in pts], mk, color=color,
                    label=f"{label} [observer]", linewidth=1.8, markersize=6)
        mpts = meter_series.get(key) or []
        if mpts:
            ax.plot([p[0] for p in mpts], [p[1] for p in mpts], ":", color=color,
                    alpha=0.45, linewidth=1.2)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_xscale("log", base=2)
    ax.set_xlabel("transfer size per channel (bytes, 64 B/beat, log scale)")
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 105)
    ax.set_title("RAPIDS beats — observer utilization vs transfer size (dotted: bare meter)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=7, loc="lower right")
    _save(fig, outdir, name)


def obs_size_bw(obs_series, outdir, name="obs_size_bw.png"):
    """Observer effective bandwidth vs size against the 6.40 GB/s line rate;
    AXIS byte-derived throughput (exact tstrb bytes / window) as hollow markers."""
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for key, (label, color, mk) in IFACE.items():
        pts = obs_series.get(key) or []
        if not pts:
            continue
        ax.plot([p[0] for p in pts], [p[2] for p in pts], mk, color=color,
                label=f"{label} [observer]", linewidth=1.8, markersize=6)
        bb = [(p[0], p[3]) for p in pts if p[3] is not None]
        if bb:
            ax.plot([b[0] for b in bb], [b[1] for b in bb], mk[-1], color=color,
                    markerfacecolor="none", markersize=9, linestyle="none",
                    label=f"{label.split(' (')[0]} byte-derived")
    ax.axhline(PEAK_GB_S, color=ORANGE, ls="--", lw=1,
               label=f"line rate {PEAK_GB_S:.1f} GB/s")
    ax.set_xscale("log", base=2)
    ax.set_xlabel("transfer size per channel (bytes, 64 B/beat, log scale)")
    ax.set_ylabel("effective bandwidth per direction (GB/s)")
    ax.set_ylim(0, PEAK_GB_S * 1.08)
    ax.set_title("RAPIDS beats — observer bandwidth vs transfer size (Genesys 2)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=7, loc="lower right")
    _save(fig, outdir, name)


def obs_latency(configs, channels, outdir, name="obs_latency.png"):
    """AXI transaction latency from the observer histograms vs transfer size:
    mean AR->first R, AR->RLAST (source read) and AW->B (sink write), cycles."""
    rows = sorted((c for c in configs if c.get("pass")
                   and c.get("active_channels") == channels), key=lambda c: c["beats"])
    series = {"rd/ar_first_r": ([], [], GRAY, "-^"), "rd/ar_rlast": ([], [], GRAY, "--^"),
              "wr/aw_b": ([], [], GREEN, "-s")}
    for r in rows:
        for pathkey, iface in (("source", "rd"), ("sink", "wr")):
            obs = ((r.get(pathkey) or {}).get("perf") or {}).get("observers") or {}
            lat = (obs.get(iface) or {}).get("latency") or {}
            for mname, ld in lat.items():
                k = f"{iface}/{mname}"
                if k in series and ld.get("samples"):
                    series[k][0].append(r["beats"] * BYTES_PER_BEAT)
                    series[k][1].append(ld["mean_cyc"])
    if not any(v[0] for v in series.values()):
        return
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for k, (xs, ys, color, mk) in series.items():
        if xs:
            ax.plot(xs, ys, mk, color=color, label=k, linewidth=1.8, markersize=6)
    ax.set_xscale("log", base=2)
    ax.set_yscale("log", base=2)
    ax.set_xlabel("transfer size per channel (bytes, 64 B/beat, log scale)")
    ax.set_ylabel("mean transaction latency (aclk cycles, log scale)")
    ax.set_title(f"RAPIDS beats — AXI latency from the observer histograms ({channels} ch)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8, loc="upper left")
    _save(fig, outdir, name)


def obs_channel_scaling(configs, outdir, name="obs_channel_scaling.png"):
    """Observer utilization vs active channel count at the largest transfer."""
    passing = [c for c in configs if c.get("pass")]
    if not passing:
        return
    big = max(c["beats"] for c in passing)
    rows = sorted((c for c in passing if c["beats"] == big), key=lambda c: c["active_channels"])
    if len({c["active_channels"] for c in rows}) < 2:
        return
    data = {k: ([], []) for k in IFACE}
    for r in rows:
        for pathkey in ("sink", "source"):
            obs = ((r.get(pathkey) or {}).get("perf") or {}).get("observers") or {}
            for key, rec in obs.items():
                if key in data:
                    data[key][0].append(r["active_channels"])
                    data[key][1].append(rec["util"] * 100.0)
    if not any(v[0] for v in data.values()):
        return
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for key, (label, color, mk) in IFACE.items():
        xs, ys = data[key]
        if xs:
            ax.plot(xs, ys, mk, color=color, label=f"{label} [observer]", linewidth=1.8, markersize=6)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_xlabel("active DMA channels")
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 105)
    ax.set_xticks(sorted({c["active_channels"] for c in rows}))
    kb = big * BYTES_PER_BEAT / 1024
    ax.set_title(f"RAPIDS beats — observer utilization vs channel count ({kb:.0f} KB/ch)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=7, loc="lower right")
    _save(fig, outdir, name)


def _obs_util(r, pathkey, iface):
    rec = (((r.get(pathkey) or {}).get("perf") or {}).get("observers") or {}).get(iface)
    return rec["util"] * 100.0 if rec else None


def obs_desc_matrix(configs, outdir, name="obs_desc_matrix.png"):
    """STREAM's descriptor x channel matrix, from the observers: utilization vs
    descriptors per channel, one line per active-channel count (AXI4-wr sink
    egress solid, AXIS-out source egress dashed), at the matrix's beats/desc."""
    rows = [c for c in configs if c.get("pass") and c.get("descs")]
    if len({c["descs"] for c in rows}) < 2:
        return
    beats = max(rows, key=lambda c: c["descs"])["beats"]
    rows = [c for c in rows if c["beats"] == beats]
    chans = sorted({c["active_channels"] for c in rows})
    fig, ax = plt.subplots(figsize=(7, 4.2))
    shades = ["#9ccc9c", "#5fa85f", "#2e7d2e", "#0f4f0f"]
    for i, nch in enumerate(chans):
        sub = sorted((c for c in rows if c["active_channels"] == nch), key=lambda c: c["descs"])
        col = shades[min(i, len(shades) - 1)]
        for pathkey, iface, ls in (("sink", "wr", "-s"), ("source", "sout", "--d")):
            pts = [(c["descs"], _obs_util(c, pathkey, iface)) for c in sub
                   if _obs_util(c, pathkey, iface) is not None]
            if pts:
                ax.plot([x for x, _ in pts], [y for _, y in pts], ls, color=col,
                        label=f"{nch} ch {IFACE[iface][0].split(' (')[0]}", linewidth=1.6, markersize=5)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_xscale("log", base=2)
    ax.set_xlabel("descriptors per channel (chain length)")
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 105)
    kb = beats * BYTES_PER_BEAT / 1024
    ax.set_title(f"RAPIDS beats — descriptors x channels matrix ({kb:.0f} KB/desc, observers)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=6, loc="lower right", ncol=2)
    _save(fig, outdir, name)


def obs_xfer_knee(configs, outdir, name="obs_xfer_knee.png"):
    """STREAM knob 1: utilization vs AXI burst length (beats per transaction),
    from the observers, at the sweep's channel count and size."""
    rows = [c for c in configs if c.get("pass") and c.get("xfer_beats")]
    if len({c["xfer_beats"] for c in rows}) < 2:
        return
    nch = max(c["active_channels"] for c in rows)
    tb = max(c.get("total_beats", c["beats"]) for c in rows if c["active_channels"] == nch)
    rows = sorted((c for c in rows if c["active_channels"] == nch
                   and c.get("total_beats", c["beats"]) == tb), key=lambda c: c["xfer_beats"])
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for pathkey, iface in (("sink", "sin"), ("sink", "wr"), ("source", "rd"), ("source", "sout")):
        pts = [(c["xfer_beats"], _obs_util(c, pathkey, iface)) for c in rows
               if _obs_util(c, pathkey, iface) is not None]
        if pts:
            label, color, mk = IFACE[iface]
            ax.plot([x for x, _ in pts], [y for _, y in pts], mk, color=color,
                    label=f"{label} [observer]", linewidth=1.8, markersize=6)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_xscale("log", base=2)
    ax.set_xlabel("AXI burst length (beats per transaction, AxLEN+1)")
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 105)
    ax.set_title(f"RAPIDS beats — utilization vs burst length ({nch} ch, {tb * BYTES_PER_BEAT // 1024} KB/ch)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=7, loc="lower right")
    _save(fig, outdir, name)


def obs_latency_knee(configs, outdir, name="obs_latency_knee.png"):
    """STREAM knob 5: utilization vs injected memory latency (RESP_DELAY),
    from the observers, at the sweep's channel count and size. The knee is
    where the DUT's in-flight window (outstanding x burst) stops covering the
    round trip."""
    rows = [c for c in configs if c.get("pass") and c.get("resp_delay") is not None]
    if len({c["resp_delay"] for c in rows}) < 2:
        return
    nch = max(c["active_channels"] for c in rows)
    tb = max(c.get("total_beats", c["beats"]) for c in rows if c["active_channels"] == nch)
    rows = sorted((c for c in rows if c["active_channels"] == nch
                   and c.get("total_beats", c["beats"]) == tb), key=lambda c: c["resp_delay"])
    fig, ax = plt.subplots(figsize=(7, 4.2))
    for pathkey, iface in (("sink", "sin"), ("sink", "wr"), ("source", "rd"), ("source", "sout")):
        pts = [(c["resp_delay"], _obs_util(c, pathkey, iface)) for c in rows
               if _obs_util(c, pathkey, iface) is not None]
        if pts:
            label, color, mk = IFACE[iface]
            ax.plot([x for x, _ in pts], [y for _, y in pts], mk, color=color,
                    label=f"{label} [observer]", linewidth=1.8, markersize=6)
    ax.axhline(100, color="#999999", ls=":", lw=1)
    ax.set_xlabel("injected response latency (aclk cycles, R and B)")
    ax.set_ylabel("engaged utilization (%)")
    ax.set_ylim(0, 105)
    ax.set_title(f"RAPIDS beats — utilization vs memory latency ({nch} ch, {tb * BYTES_PER_BEAT // 1024} KB/ch)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=7, loc="lower left")
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
    if _has_observers(configs):
        oseries = _obs_series(configs, channels=nch)
        obs_size_util(oseries, series, args.outdir)
        obs_size_bw(oseries, args.outdir)
        obs_latency(configs, nch, args.outdir)
        obs_channel_scaling(configs, args.outdir)
        obs_desc_matrix(configs, args.outdir)
        obs_xfer_knee(configs, args.outdir)
        obs_latency_knee(configs, args.outdir)


if __name__ == "__main__":
    main()
