# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Extended-addressing characterization for STREAM (row/col x row/col).

Sweeps the four traversal modes (row/row, row/col, col/row, col/col) over a set
of WxH tiles and measures RD/WR datapath throughput + bus utilization via the
NAMED RDMON_PERF / WRMON_PERF windows (stream_regmap). One program, board + sim.

Emits one record per (mode, size) with the raw perf buckets and derived metrics,
so the report generator produces the same tables/curves from sim or board data.

Requires the DUT built with USE_ROW_COL_MAJOR_ADDRESSING=1. STREAM must already
be configured (GLOBAL_EN + scheduler + descriptor engine + AXI); the caller does
that once (the board main() below, or the sim TB) before run_sweep().
"""

from __future__ import annotations

import json
import os
import sys
from typing import List, Tuple

_here = os.path.dirname(os.path.abspath(__file__))
# One bootstrap to reach the area's env module; stream_env owns every other
# path (shared FPGA layer, this area's bin/, this build's host/). Replaces the
# hand-counted walks to a sibling flow and to converters/bin.
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)

from harness_kick import HARNESS_CSR_BASE, batch_kick
from harness_addrs import H, harness_regs  # noqa: E402  (by-name harness CSR access)
from bus_meters import read_meter, R_METER_BASE, W_METER_BASE  # noqa: E402
from stream_ext_suite import CASES, CH_ERROR, CH_IDLE, program_case, wait_done  # noqa: E402

# Observer histogram CSRs (burst counts) -- mirrors stream_harness_tb.py.
CSR_OBS_HIST_SEL   = H("OBS_HIST_SEL")
CSR_OBS_HIST_DATA  = H("OBS_HIST_DATA")
CSR_OBS_HIST_TOTAL = H("OBS_HIST_TOTAL")

# Default sweep: throughput-vs-size per mode. row modes burst; col modes are
# single-beat, so col/col at the large sizes dominates board runtime.
DEFAULT_SIZES: List[Tuple[int, int]] = [(64, 64), (256, 256), (1024, 1024), (2048, 2048)]

def _obs_burst_count(bridge, bus: int, metric: int) -> int:
    """Observer per-metric transaction (burst) total. bus 0=read, 1=write;
    metric read 1=AR->RLAST, write 0=AW->B. The TOTAL counts completed
    transactions = bursts on that side (bin index is don't-care for the total)."""
    bridge.write(CSR_OBS_HIST_SEL, ((metric & 1) << 1) | (bus & 1))
    return bridge.read(CSR_OBS_HIST_TOTAL) & 0xFFFF_FFFF


def _read_obs(stream) -> tuple:
    """Read the EXTERNAL DMA observer's aggregate R/W buckets + burst counts.
    Utilization = prod/(prod+bp+starv+idle); the harness auto-windows the
    observer around the DMA (frozen by read time). Independent of the DUT's
    internal monitors -- the same instrument the legacy char now uses, so ext
    and legacy numbers are apples-to-apples."""
    br = stream.bridge
    ra = read_meter(br, R_METER_BASE, 1, 'R').aggregate
    wa = read_meter(br, W_METER_BASE, 1, 'W').aggregate
    rd_bursts = _obs_burst_count(br, bus=0, metric=1)   # AR->RLAST = read bursts
    wr_bursts = _obs_burst_count(br, bus=1, metric=0)   # AW->B    = write bursts

    def mk(a, bursts):
        return {"prod": a.productive, "bp": a.backpressure,
                "starv": a.starvation, "idle": a.idle,
                "total": a.total, "bursts": bursts}
    return mk(ra, rd_bursts), mk(wa, wr_bursts)


def measure_mode(stream, channel: int, case: str, W: int, H: int,
                 *, reset_fn=None, poll_max: int = 20000) -> dict:
    """Run one (mode, size) on `channel`; read the external observer.

    reset_fn (soft-reset + reconfigure STREAM) re-arms the observer's auto-window
    per case -- the window opens on DMA-busy only after obs_started clears on the
    unit soft-reset, so each measured case needs a fresh reset. Descriptors are
    (re)programmed after the reset."""
    if reset_fn:
        reset_fn()
    kick = program_case(stream, channel, case, W, H)
    stream.enable_channel(channel, True)
    batch_kick(stream.bridge, {channel: kick})   # harness KICK_GO fast path
    res = wait_done(stream, channel, poll_max=poll_max)

    rd, wr = _read_obs(stream)
    return _derive({
        "case": case, "W": W, "H": H, "beats": W * H,
        "bytes_per_beat": stream.desc.bytes_per_beat,
        "ok": res["ok"], "reason": res["reason"], "rd": rd, "wr": wr,
    })


def _derive(rec: dict) -> dict:
    """Add per-direction utilization + throughput + bucket fractions from the
    observer aggregate. util = productive fraction; starv_frac is the tell for
    per-beat (single-beat) modes (bus starved between beats). Throughput is
    dimensionless bytes/cycle -- the report multiplies by the clock for GB/s."""
    bs = rec.get("bytes_per_beat", 16)
    beats = rec["beats"]
    for d in ("rd", "wr"):
        p = rec[d]
        tot = p["total"] or 1
        p["util"] = p["prod"] / tot                 # productive fraction
        p["starv_frac"] = p["starv"] / tot          # per-beat starvation tell
        p["bp_frac"] = p["bp"] / tot
        p["beats"] = beats
        p["bytes"] = beats * bs
        p["bytes_per_cycle"] = p["bytes"] / tot
        p["avg_burst_beats"] = (beats / p["bursts"]) if p.get("bursts") else 0.0
    return rec


def run_sweep(stream, *, channel: int = 0, sizes=DEFAULT_SIZES, cases=CASES,
              reset_fn=None, poll_max: int = 20000, progress=None) -> List[dict]:
    """Sweep cases x sizes; return one record per (mode, size). reset_fn re-arms
    the observer window per case (see measure_mode)."""
    records = []
    for (W, H) in sizes:
        for case in cases:
            if progress:
                progress(f"{case} {W}x{H}")
            records.append(measure_mode(stream, channel, case, W, H,
                                        reset_fn=reset_fn, poll_max=poll_max))
    return records


# ---------------------------------------------------------------------------
# Channel-count scaling: aggregate bus utilization vs. number of channels.
#
# The transpose cases (row/col, col/row) run one direction per-beat (single-beat
# AXI). A single channel there is latency-bound -- the shared bus idles between
# beats. Firing N channels back-to-back (KICK_GO) lets the shared read/write
# engine interleave them, hiding per-beat latency, so aggregate utilization is
# expected to rise 1 -> 8 (with a knee where outstanding transactions cover the
# latency). Burst cases (row/row) already saturate at N=1 and are included only
# as the control that should stay flat.
# ---------------------------------------------------------------------------
DEFAULT_CHANNEL_COUNTS = (1, 2, 4, 8)
SCALING_CASES = ("row/col", "col/row")     # the transpose (per-beat) modes
SCALING_SIZE = (256, 256)                  # fixed tile; big enough to hide poll latency


def _wait_all(stream, channels, poll_max: int) -> dict:
    """Wait for every channel in `channels` to return to IDLE. Fails fast on any
    channel entering CH_ERROR."""
    pending = set(channels)
    for _ in range(poll_max):
        for ch in list(pending):
            st = stream.channel_state(ch)
            if st == CH_ERROR:
                return dict(ok=False, reason=f"CH_ERROR ch{ch}")
            if st == CH_IDLE:
                pending.discard(ch)
        if not pending:
            return dict(ok=True, reason="idle")
    return dict(ok=False, reason=f"timeout pending={sorted(pending)}")


def measure_scaling(stream, case: str, W: int, H: int, nch: int,
                    *, reset_fn=None, poll_max: int = 40000) -> dict:
    """Run one (mode, size) across `nch` channels concurrently; read the external
    observer aggregate. reset_fn re-arms the observer window per point.

    All nch channels run the SAME tile config (the synthetic peers ignore the
    src/dst addresses, so per-channel descriptors may overlap). Channels are
    kicked back-to-back via the harness KICK_GO fast path so they actually
    overlap on the shared bus rather than serializing on the transport."""
    if reset_fn:
        reset_fn()
    channels = list(range(nch))
    kicks = {}
    for ch in channels:
        kicks[ch] = program_case(stream, ch, case, W, H)
        stream.enable_channel(ch, True)

    batch_kick(stream.bridge, kicks)  # fire all nch channels on one aclk cycle
    res = _wait_all(stream, channels, poll_max=poll_max)

    rd, wr = _read_obs(stream)
    return _derive({
        "case": case, "W": W, "H": H, "nch": nch, "beats": nch * W * H,
        "bytes_per_beat": stream.desc.bytes_per_beat,
        "ok": res["ok"], "reason": res["reason"], "rd": rd, "wr": wr,
    })


def run_channel_scaling(stream, *, cases=SCALING_CASES, size=SCALING_SIZE,
                        channel_counts=DEFAULT_CHANNEL_COUNTS, reset_fn=None,
                        poll_max: int = 40000, progress=None) -> List[dict]:
    """For each transpose case, sweep channel count and record aggregate util.
    Returns one record per (case, nch)."""
    W, H = size
    records = []
    for case in cases:
        for nch in channel_counts:
            if progress:
                progress(f"{case} {W}x{H} x{nch}ch")
            records.append(measure_scaling(stream, case, W, H, nch,
                                           reset_fn=reset_fn, poll_max=poll_max))
    return records


# ---------------------------------------------------------------------------
# FPGA entry point
# ---------------------------------------------------------------------------
def _configure(stream, harness_csr_base: int) -> None:
    """One-time STREAM config by name (+ harness soft-reset). Mirrors the sim
    TB's _configure_stream_for_ext, board-side."""
    # Harness soft-reset pulse (CTRL.SOFT_RESET, bit3 == 0x08), by name.
    harness_regs(stream.bridge, harness_csr_base).CTRL.write(soft_reset=1)
    stream.write("GLOBAL_CTRL", GLOBAL_EN=1)             # was 0x01
    # SCHED_CONFIG: en+timeout+err+compl, PLUS RD_PREFETCH_EN (regmap default-on;
    # the old bare 0x0F silently DISABLED read-ahead -- compose == 0x2F now).
    stream.write("SCHED_CONFIG", SCHED_EN=1, TIMEOUT_EN=1, ERR_EN=1,
                 COMPL_EN=1, RD_PREFETCH_EN=1)           # was 0x0F -> now 0x2F
    stream.write("SCHED_TIMEOUT_CYCLES", TIMEOUT_CYCLES=0xFFFF_FFFF)
    stream.write("DESCENG_CONFIG", DESCENG_EN=1, PREFETCH_EN=1, FIFO_THRESH=8)  # was 0x23
    stream.write("DESCENG_ADDR0_BASE", ADDR0_BASE=0x0000_0000)
    stream.write("DESCENG_ADDR0_LIMIT", ADDR0_LIMIT=0xFFFF_FFFF)
    stream.write("DESCENG_ADDR1_BASE", ADDR1_BASE=0x0000_0000)
    stream.write("DESCENG_ADDR1_LIMIT", ADDR1_LIMIT=0xFFFF_FFFF)
    stream.write("AXI_XFER_CONFIG", RD_XFER_BEATS=15, WR_XFER_BEATS=15)  # was 0x0F0F


def main(argv=None) -> int:
    import argparse
    import os
    import sys

    from uart_axi_bridge import UARTAxiBridge   # shared FPGA layer (stream_env)
    from stream_device import Stream
    from descriptor_builder import STREAM_APB_BASE, DESC_RAM_BASE, HARNESS_CSR_BASE
    from harness_addrs import autodetect_port

    ap = argparse.ArgumentParser(description="STREAM extended-addressing characterization")
    ap.add_argument("--port", default="auto",
                    help="Serial port. Default 'auto' probes every /dev/ttyUSB* "
                         "for the stream harness (SCRATCH round-trip) since the "
                         "USB-UART re-enumerates. Pass an explicit path to force it.")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--out", default="ext_char.json")
    ap.add_argument("--sizes", default="64x64,256x256,1024x1024,2048x2048")
    ap.add_argument("--scale-channels", default="1,2,4,8",
                    help="channel counts for the util-vs-channels sweep (transpose modes); empty to skip")
    ap.add_argument("--scale-size", default="256x256",
                    help="fixed tile for the channel-scaling sweep")
    args = ap.parse_args(argv)

    # Resolve the serial port (auto-probes /dev/ttyUSB* for the harness).
    args.port = autodetect_port(args.baud, want=args.port)

    sizes = [tuple(int(x) for x in s.split("x")) for s in args.sizes.split(",")]
    scale_channels = tuple(int(x) for x in args.scale_channels.split(",") if x.strip())
    scale_w, scale_h = (int(x) for x in args.scale_size.split("x"))

    with UARTAxiBridge(args.port, args.baud) as bridge:
        stream = Stream(bridge, "stream0",
                        regs_base=STREAM_APB_BASE, desc_ram_base=DESC_RAM_BASE)
        # reset_fn soft-resets + reconfigures STREAM, which also re-arms the
        # external observer's auto-window; it runs before every measured case so
        # each case gets a fresh, frozen observer window.
        reset_fn = lambda: _configure(stream, HARNESS_CSR_BASE)  # noqa: E731
        records = run_sweep(stream, channel=args.channel, sizes=sizes,
                            reset_fn=reset_fn, progress=lambda s: print(f"  {s}"))
        scaling = []
        if scale_channels:
            scaling = run_channel_scaling(stream, size=(scale_w, scale_h),
                                          channel_counts=scale_channels,
                                          reset_fn=reset_fn,
                                          progress=lambda s: print(f"  scale {s}"))

    with open(args.out, "w") as f:
        json.dump({"records": records, "sizes": [list(s) for s in sizes],
                   "scaling": scaling, "scale_channels": list(scale_channels),
                   "scale_size": [scale_w, scale_h]}, f, indent=2)
    print(f"wrote {len(records)} records + {len(scaling)} scaling records -> {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
