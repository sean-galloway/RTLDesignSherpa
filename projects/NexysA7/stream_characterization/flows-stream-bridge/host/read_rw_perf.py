#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: read_rw_perf
# Purpose: UART-side reader for the data-READ and data-WRITE datapath AXI
#          monitors' perf-window CSRs (RFC Stage E option 2, CSR route). These
#          surface each datapath monitor's four-bucket cycle classification +
#          beat/byte/burst counts directly from the STREAM regblock, with NO
#          MonBus packets. This is the in-core replacement for the FPGA-char
#          axi_bus_meter blocks (see read_bus_meters.py).
#
#   RDMON_PERF (0x300 block): data-read R bus utilization
#   WRMON_PERF (0x330 block): data-write W bus utilization
#
# Software flow (mirrors read_desc_perf.py):
#   1. open_windows(bridge)  -> RDMON/WRMON_PERF_CTRL.RUN = 1 (clears + starts)
#   2. run the workload (the DMA datapath traffic)
#   3. close_windows(bridge) -> RUN = 0 (freezes counters)
#   4. read_rw_perf(bridge)  -> {'r': snapshot, 'w': snapshot}
#
# The four buckets PROD/BP/STARV/IDLE sum to the closed-window length (the LIVE
# WINDOW_CYCLES counter is zeroed at close; the buckets HOLD -- see
# DMA_UTILIZATION_MEASUREMENT.md Section 3). Counters are 32-bit; byte count is
# 64-bit (LO/HI).
#
# Register map (STREAM regblock, base = 0x0; see stream_regmap.py). Both blocks
# share an identical 11-register layout at 0x04 stride, so one base + offset
# table reads either:
#   +0x00 PERF_CTRL    RUN[0]
#   +0x04 PERF_STATUS  WIN_ACTIVE[0]
#   +0x08 WINDOW_CYCLES
#   +0x0C PROD_CYCLES
#   +0x10 BP_CYCLES
#   +0x14 STARV_CYCLES
#   +0x18 IDLE_CYCLES
#   +0x1C BEAT_COUNT
#   +0x20 BYTE_COUNT_LO
#   +0x24 BYTE_COUNT_HI
#   +0x28 BURST_COUNT
# RDMON_PERF base = 0x300, WRMON_PERF base = 0x330.

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

# STREAM regblock lives at bridge slave 0 (base 0x0). Block bases + the shared
# per-register offsets mirror projects/components/stream/rtl/stream_regmap.py.
STREAM_APB_BASE = 0x0000_0000
RDMON_PERF_BASE = STREAM_APB_BASE + 0x300
WRMON_PERF_BASE = STREAM_APB_BASE + 0x330

OFF_CTRL          = 0x00
OFF_STATUS        = 0x04
OFF_WINDOW_CYCLES = 0x08
OFF_PROD_CYCLES   = 0x0C
OFF_BP_CYCLES     = 0x10
OFF_STARV_CYCLES  = 0x14
OFF_IDLE_CYCLES   = 0x18
OFF_BEAT_COUNT    = 0x1C
OFF_BYTE_COUNT_LO = 0x20
OFF_BYTE_COUNT_HI = 0x24
OFF_BURST_COUNT   = 0x28

PERF_RUN_BIT = 1 << 0

# Per-channel bucket readout (RFC Stage C, indexed). Select a channel via
# PERF_CH_SEL, then read the packed {bp,prod}/{idle,starv} regs. Overflow masks
# expose all channels at once ({prod,bp,starv,idle} sticky per channel).
PERF_CH_SEL              = STREAM_APB_BASE + 0x35C
RDMON_PERF_CH_PROD_BP    = STREAM_APB_BASE + 0x360
RDMON_PERF_CH_STARV_IDLE = STREAM_APB_BASE + 0x364
WRMON_PERF_CH_PROD_BP    = STREAM_APB_BASE + 0x368
WRMON_PERF_CH_STARV_IDLE = STREAM_APB_BASE + 0x36C
RDMON_PERF_CH_OVERFLOW   = STREAM_APB_BASE + 0x370
WRMON_PERF_CH_OVERFLOW   = STREAM_APB_BASE + 0x374


@dataclass(frozen=True)
class RwPerfSnapshot:
    bus: str  # 'read' or 'write'
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
        """Productive cycles / window length."""
        denom = self.window_length
        return self.productive / denom if denom > 0 else 0.0


def open_windows(bridge) -> None:
    """Clear + start both datapath perf windows (RUN rising edge)."""
    bridge.write(RDMON_PERF_BASE + OFF_CTRL, PERF_RUN_BIT)
    bridge.write(WRMON_PERF_BASE + OFF_CTRL, PERF_RUN_BIT)


def close_windows(bridge) -> None:
    """Close + freeze both datapath perf windows."""
    bridge.write(RDMON_PERF_BASE + OFF_CTRL, 0)
    bridge.write(WRMON_PERF_BASE + OFF_CTRL, 0)


def _read_window(bridge, base: int, bus: str) -> RwPerfSnapshot:
    r = lambda off: bridge.read(base + off) & 0xFFFF_FFFF
    byte_lo = r(OFF_BYTE_COUNT_LO)
    byte_hi = r(OFF_BYTE_COUNT_HI)
    return RwPerfSnapshot(
        bus           = bus,
        win_active    = r(OFF_STATUS) & 0x1,
        window_cycles = r(OFF_WINDOW_CYCLES),
        productive    = r(OFF_PROD_CYCLES),
        backpressure  = r(OFF_BP_CYCLES),
        starvation    = r(OFF_STARV_CYCLES),
        idle          = r(OFF_IDLE_CYCLES),
        beats         = r(OFF_BEAT_COUNT),
        bytes_moved   = (byte_hi << 32) | byte_lo,
        bursts        = r(OFF_BURST_COUNT),
    )


def read_rw_perf(bridge) -> dict:
    """Read both datapath monitor perf windows. Returns {'r': snap, 'w': snap}."""
    return {
        'r': _read_window(bridge, RDMON_PERF_BASE, 'read'),
        'w': _read_window(bridge, WRMON_PERF_BASE, 'write'),
    }


def _decode_packed(pb: int, si: int) -> dict:
    """Decode {bp[31:16], prod[15:0]} + {idle[31:16], starv[15:0]} -> 16-bit buckets."""
    return {
        'prod':  pb & 0xFFFF,
        'bp':    (pb >> 16) & 0xFFFF,
        'starv': si & 0xFFFF,
        'idle':  (si >> 16) & 0xFFFF,
    }


def read_rw_perf_channels(bridge, num_channels: int) -> dict:
    """Read per-channel datapath buckets (RFC Stage C) for both buses.

    Returns {'r': [per-channel dict, ...], 'w': [...],
             'r_overflow': mask, 'w_overflow': mask}. Each per-channel dict has
    16-bit prod/bp/starv/idle. Overflow masks pack {prod,bp,starv,idle} (4 bits)
    per channel, channel 0 in the low nibble.
    """
    rd, wr = [], []
    for ch in range(num_channels):
        bridge.write(PERF_CH_SEL, ch)
        rd.append(_decode_packed(bridge.read(RDMON_PERF_CH_PROD_BP) & 0xFFFF_FFFF,
                                 bridge.read(RDMON_PERF_CH_STARV_IDLE) & 0xFFFF_FFFF))
        wr.append(_decode_packed(bridge.read(WRMON_PERF_CH_PROD_BP) & 0xFFFF_FFFF,
                                 bridge.read(WRMON_PERF_CH_STARV_IDLE) & 0xFFFF_FFFF))
    return {
        'r': rd,
        'w': wr,
        'r_overflow': bridge.read(RDMON_PERF_CH_OVERFLOW) & 0xFFFF_FFFF,
        'w_overflow': bridge.read(WRMON_PERF_CH_OVERFLOW) & 0xFFFF_FFFF,
    }


def _pct(num: int, den: int) -> str:
    return "  n/a" if den == 0 else f"{(100.0 * num / den):5.1f}%"


def format_snapshot(s: RwPerfSnapshot, file=sys.stdout) -> None:
    wl = s.window_length
    print(f"=== data-{s.bus} datapath AXI monitor perf window ===", file=file)
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
          f"(productive / window length)", file=file)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Read the STREAM data-read/data-write datapath monitor "
                    "perf-window CSRs via UART AXIL bridge (RFC Stage E option 2)."
    )
    p.add_argument("--port", required=True, help="UART device path, e.g. /dev/ttyUSB2")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--open", action="store_true",
                   help="write RUN=1 (clear+start both windows) and exit")
    p.add_argument("--close", action="store_true",
                   help="write RUN=0 (freeze both windows) before reading")
    p.add_argument("--channels", type=int, default=0,
                   help="also print per-channel buckets for this many channels")
    args = p.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        if args.open:
            open_windows(bridge)
            print("# RDMON/WRMON_PERF_CTRL.RUN = 1 (windows opened, counters cleared)",
                  file=sys.stderr)
            return 0
        if args.close:
            close_windows(bridge)
        snaps = read_rw_perf(bridge)
        per_ch = read_rw_perf_channels(bridge, args.channels) if args.channels else None
    format_snapshot(snaps['r'])
    format_snapshot(snaps['w'])
    if per_ch:
        for bus, key in (('read', 'r'), ('write', 'w')):
            print(f"=== data-{bus} per-channel buckets (overflow=0x{per_ch[key[0] + '_overflow']:X}) ===")
            for ch, c in enumerate(per_ch[key]):
                print(f"  ch{ch}: prod={c['prod']:6d} bp={c['bp']:6d} "
                      f"starv={c['starv']:6d} idle={c['idle']:6d}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
