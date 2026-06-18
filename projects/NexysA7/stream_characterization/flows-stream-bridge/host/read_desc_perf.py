#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: read_desc_perf
# Purpose: UART-side reader for the descriptor-fetch AXI monitor's perf-window
#          CSRs (RFC Stage E CSR route). These surface the descriptor monitor's
#          four-bucket cycle classification + beat/byte/burst counts directly
#          from the STREAM regblock, with NO MonBus packets.
#
# This measures the DESCRIPTOR-FETCH R bus only. Datapath R/W utilization is
# measured separately by the stream_char harness axi_bus_meter blocks (see
# read_bus_meters.py).
#
# Software flow:
#   1. open_window(bridge)   -> DAXMON_PERF_CTRL.RUN = 1 (clears + starts)
#   2. run the workload (descriptor fetches)
#   3. close_window(bridge)  -> DAXMON_PERF_CTRL.RUN = 0 (freezes counters)
#   4. read_desc_perf(bridge) -> snapshot + utilization
#
# The four buckets PROD/BP/STARV/IDLE sum to WINDOW_CYCLES by construction
# (DMA_UTILIZATION_MEASUREMENT.md Section 3). Counters are 32-bit (window
# cycles + buckets); byte count is 64-bit (LO/HI). At 100 MHz the 32-bit
# window counter wraps after ~42.9 s -- plenty for a single run.
#
# Register map (STREAM regblock, base = 0x0; see stream_regmap.py):
#   0x2D0 DAXMON_PERF_CTRL    RUN[0]
#   0x2D4 DAXMON_PERF_STATUS  WIN_ACTIVE[0]
#   0x2D8 WINDOW_CYCLES
#   0x2DC PROD_CYCLES
#   0x2E0 BP_CYCLES
#   0x2E4 STARV_CYCLES
#   0x2E8 IDLE_CYCLES
#   0x2EC BEAT_COUNT
#   0x2F0 BYTE_COUNT_LO
#   0x2F4 BYTE_COUNT_HI
#   0x2F8 BURST_COUNT

import argparse
import os
import sys
from dataclasses import dataclass

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    _cand = HERE
    while _cand != "/" and not os.path.isdir(os.path.join(_cand, ".git")):
        _cand = os.path.dirname(_cand)
    if os.path.isdir(os.path.join(_cand, ".git")):
        _repo_root = _cand
if _repo_root:
    sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))

# STREAM regblock lives at bridge slave 0 (base 0x0). Offsets mirror
# projects/components/stream/rtl/stream_regmap.py (RFC Stage E block).
STREAM_APB_BASE        = 0x0000_0000
OFF_PERF_CTRL          = 0x2D0
OFF_PERF_STATUS        = 0x2D4
OFF_PERF_WINDOW_CYCLES = 0x2D8
OFF_PERF_PROD_CYCLES   = 0x2DC
OFF_PERF_BP_CYCLES     = 0x2E0
OFF_PERF_STARV_CYCLES  = 0x2E4
OFF_PERF_IDLE_CYCLES   = 0x2E8
OFF_PERF_BEAT_COUNT    = 0x2EC
OFF_PERF_BYTE_COUNT_LO = 0x2F0
OFF_PERF_BYTE_COUNT_HI = 0x2F4
OFF_PERF_BURST_COUNT   = 0x2F8

PERF_CTRL  = STREAM_APB_BASE + OFF_PERF_CTRL
PERF_RUN_BIT = 1 << 0


@dataclass(frozen=True)
class DescPerfSnapshot:
    win_active: int
    window_cycles: int
    productive: int
    backpressure: int
    starvation: int
    idle: int
    beats: int
    bytes_moved: int
    bursts: int

    @property
    def bucket_total(self) -> int:
        return self.productive + self.backpressure + self.starvation + self.idle

    @property
    def window_length(self) -> int:
        """Authoritative closed-window length. WINDOW_CYCLES is a LIVE counter
        the monitor zeroes on close, so after close we use the bucket sum
        (which holds). While the window is still active, prefer WINDOW_CYCLES."""
        if self.win_active and self.window_cycles:
            return self.window_cycles
        return self.bucket_total

    @property
    def datapath_utilization(self) -> float:
        """Productive cycles / window length (descriptor-fetch R bus)."""
        denom = self.window_length
        return self.productive / denom if denom > 0 else 0.0


def open_window(bridge) -> None:
    """Clear + start the descriptor-monitor perf window (RUN rising edge)."""
    bridge.write(PERF_CTRL, PERF_RUN_BIT)


def close_window(bridge) -> None:
    """Close + freeze the descriptor-monitor perf window."""
    bridge.write(PERF_CTRL, 0)


def read_desc_perf(bridge) -> DescPerfSnapshot:
    """Read the descriptor-monitor perf-window counters. Pure data."""
    r = lambda off: bridge.read(STREAM_APB_BASE + off) & 0xFFFF_FFFF
    byte_lo = r(OFF_PERF_BYTE_COUNT_LO)
    byte_hi = r(OFF_PERF_BYTE_COUNT_HI)
    return DescPerfSnapshot(
        win_active    = r(OFF_PERF_STATUS) & 0x1,
        window_cycles = r(OFF_PERF_WINDOW_CYCLES),
        productive    = r(OFF_PERF_PROD_CYCLES),
        backpressure  = r(OFF_PERF_BP_CYCLES),
        starvation    = r(OFF_PERF_STARV_CYCLES),
        idle          = r(OFF_PERF_IDLE_CYCLES),
        beats         = r(OFF_PERF_BEAT_COUNT),
        bytes_moved   = (byte_hi << 32) | byte_lo,
        bursts        = r(OFF_PERF_BURST_COUNT),
    )


def _pct(num: int, den: int) -> str:
    return "  n/a" if den == 0 else f"{(100.0 * num / den):5.1f}%"


def format_snapshot(s: DescPerfSnapshot, file=sys.stdout) -> None:
    wl = s.window_length
    print("=== descriptor-fetch AXI monitor perf window ===", file=file)
    print(f"  window_active   = {s.win_active}", file=file)
    print(f"  window_cycles   = {s.window_cycles}  (live counter; 0 after close)",
          file=file)
    print(f"  window_length   = {wl}  (~{wl * 10e-9 * 1e6:.1f} us at 100 MHz; "
          f"bucket sum after close)", file=file)
    print(f"    productive    {s.productive:>10d}  ({_pct(s.productive, wl)})", file=file)
    print(f"    backpressure  {s.backpressure:>10d}  ({_pct(s.backpressure, wl)})", file=file)
    print(f"    starvation    {s.starvation:>10d}  ({_pct(s.starvation, wl)})", file=file)
    print(f"    idle          {s.idle:>10d}  ({_pct(s.idle, wl)})", file=file)
    print(f"  beats           = {s.beats}", file=file)
    print(f"  bytes_moved     = {s.bytes_moved}", file=file)
    print(f"  bursts          = {s.bursts}", file=file)
    print(f"  datapath_util   = {s.datapath_utilization * 100:5.1f}%  "
          f"(productive / window length, descriptor-fetch R bus)", file=file)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Read the STREAM descriptor-fetch monitor perf-window CSRs "
                    "via UART AXIL bridge (RFC Stage E CSR route)."
    )
    p.add_argument("--port", required=True, help="UART device path, e.g. /dev/ttyUSB2")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--open", action="store_true",
                   help="write RUN=1 (clear+start window) and exit")
    p.add_argument("--close", action="store_true",
                   help="write RUN=0 (freeze window) before reading")
    args = p.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        if args.open:
            open_window(bridge)
            print("# DAXMON_PERF_CTRL.RUN = 1 (window opened, counters cleared)",
                  file=sys.stderr)
            return 0
        if args.close:
            close_window(bridge)
        snap = read_desc_perf(bridge)
    format_snapshot(snap)
    return 0


if __name__ == "__main__":
    sys.exit(main())
