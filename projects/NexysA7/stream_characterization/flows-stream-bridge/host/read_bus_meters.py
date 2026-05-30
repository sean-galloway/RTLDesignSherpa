#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: read_bus_meters
# Purpose: UART-side reader for stream_char's axi_bus_meter CSRs.
#
# After a characterization run, the host calls into this script (or imports
# read_bus_meters() directly) to:
#   1. Read the R-meter and W-meter aggregate counters (4 buckets each)
#   2. Read all per-channel counters (4 buckets x NUM_CHANNELS each)
#   3. Read the per-channel overflow mask (sticky bits for 16-bit wraparound)
#   4. Compute and print:
#       - Aggregate datapath utilization (per methodology doc Section 2.1)
#       - 4-bucket cycle breakdown (productive/backpressure/starvation/idle)
#       - Per-channel productive/backpressure split with overflow flagging
#
# All cycle counts are in aclk cycles (10 ns at 100 MHz). Aggregate
# counters are 32-bit; they accumulate for 42.9 s before wrapping. Per-
# channel counters are 16-bit; they wrap at 655 us. The overflow mask
# in the CSR records exactly which (channel, bucket) pairs wrapped.
#
# The meter CSRs live in harness_csr at:
#   R-meter:  HARNESS_CSR_BASE + 0x100
#   W-meter:  HARNESS_CSR_BASE + 0x180
# See projects/NexysA7/stream_characterization/stream_char_framework/rtl/
# harness_csr.sv (top-of-file docblock) for the per-meter offset map.

import argparse
import os
import sys
import time
from dataclasses import dataclass
from typing import List

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

# Also add converters/bin so `from uart_axi_bridge import UARTAxiBridge`
# resolves in main(). Mirror what dump_monbus_sram.py does -- walk up
# until we find the repo root (the dir with a .git child).
_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    _cand = HERE
    while _cand != "/" and not os.path.isdir(os.path.join(_cand, ".git")):
        _cand = os.path.dirname(_cand)
    if os.path.isdir(os.path.join(_cand, ".git")):
        _repo_root = _cand
if _repo_root:
    sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))

from descriptor_builder import HARNESS_CSR_BASE  # noqa: E402


# ---------------------------------------------------------------------------
# CSR offsets within a single meter block. R-meter base = HARNESS_CSR_BASE +
# 0x100; W-meter base = HARNESS_CSR_BASE + 0x180.
# ---------------------------------------------------------------------------

OFF_AGG_PRODUCTIVE   = 0x00
OFF_AGG_BACKPRESSURE = 0x04
OFF_AGG_STARVATION   = 0x08
OFF_AGG_IDLE         = 0x0C
OFF_CH_OVERFLOW      = 0x10
OFF_CH_PROD_BP_BASE  = 0x20  # +4*ch -> {bp[15:0], productive[15:0]}
OFF_CH_STARV_IDLE_BASE = 0x40  # +4*ch -> {idle[15:0], starvation[15:0]}

R_METER_BASE = HARNESS_CSR_BASE + 0x100
W_METER_BASE = HARNESS_CSR_BASE + 0x180


@dataclass(frozen=True)
class BucketCounts:
    productive: int
    backpressure: int
    starvation: int
    idle: int

    @property
    def total(self) -> int:
        return self.productive + self.backpressure + self.starvation + self.idle

    @property
    def datapath_utilization(self) -> float:
        """Productive cycles divided by (productive + backpressure + starvation
        + idle), i.e. the fraction of measurement-window cycles that delivered
        data. Returns 0 if the meter saw no cycles at all (window not open)."""
        t = self.total
        return self.productive / t if t > 0 else 0.0


@dataclass(frozen=True)
class ChannelBuckets(BucketCounts):
    channel: int
    overflow: int  # 4-bit mask {prod, bp, starv, idle}; bit set = wrapped

    @property
    def any_overflow(self) -> bool:
        return self.overflow != 0


@dataclass(frozen=True)
class MeterSnapshot:
    name: str
    aggregate: BucketCounts
    per_channel: List[ChannelBuckets]


# ---------------------------------------------------------------------------
# Reader
# ---------------------------------------------------------------------------

def read_meter(bridge, meter_base: int, num_channels: int, name: str) -> MeterSnapshot:
    """Read one meter (R or W) from a UARTAxiBridge-like object.

    `bridge.read(addr)` must return a 32-bit int (UARTAxiBridge.read's
    signature). The function performs 5 + 2*num_channels reads.
    """
    agg = BucketCounts(
        productive   = bridge.read(meter_base + OFF_AGG_PRODUCTIVE),
        backpressure = bridge.read(meter_base + OFF_AGG_BACKPRESSURE),
        starvation   = bridge.read(meter_base + OFF_AGG_STARVATION),
        idle         = bridge.read(meter_base + OFF_AGG_IDLE),
    )
    ovf_word = bridge.read(meter_base + OFF_CH_OVERFLOW)

    per_channel: List[ChannelBuckets] = []
    for ch in range(num_channels):
        pb = bridge.read(meter_base + OFF_CH_PROD_BP_BASE + 4 * ch)
        si = bridge.read(meter_base + OFF_CH_STARV_IDLE_BASE + 4 * ch)
        prod  = pb & 0xFFFF
        bp    = (pb >> 16) & 0xFFFF
        starv = si & 0xFFFF
        idle  = (si >> 16) & 0xFFFF
        ch_ovf = (ovf_word >> (4 * ch)) & 0xF
        per_channel.append(ChannelBuckets(
            channel=ch,
            productive=prod, backpressure=bp,
            starvation=starv, idle=idle,
            overflow=ch_ovf,
        ))

    return MeterSnapshot(name=name, aggregate=agg, per_channel=per_channel)


def read_bus_meters(bridge, num_channels: int) -> dict:
    """Read both R-meter and W-meter, return {'r': MeterSnapshot, 'w': MeterSnapshot}.
    Pure data; formatting is up to the caller."""
    return {
        'r': read_meter(bridge, R_METER_BASE, num_channels, 'R'),
        'w': read_meter(bridge, W_METER_BASE, num_channels, 'W'),
    }


# ---------------------------------------------------------------------------
# Pretty-printing
# ---------------------------------------------------------------------------

def _format_pct(num: int, den: int) -> str:
    if den == 0:
        return "  n/a"
    return f"{(100.0 * num / den):5.1f}%"


def format_meter(snap: MeterSnapshot, file=sys.stdout) -> None:
    """Render one meter snapshot in human-readable form."""
    agg = snap.aggregate
    print(f"=== {snap.name}-bus meter ===", file=file)
    print(f"  Aggregate over {agg.total} cycles "
          f"(~{agg.total * 10e-9 * 1e6:.1f} us at 100 MHz):", file=file)
    print(f"    productive     {agg.productive:>10d}  ({_format_pct(agg.productive, agg.total)})", file=file)
    print(f"    backpressure   {agg.backpressure:>10d}  ({_format_pct(agg.backpressure, agg.total)})", file=file)
    print(f"    starvation     {agg.starvation:>10d}  ({_format_pct(agg.starvation, agg.total)})", file=file)
    print(f"    idle           {agg.idle:>10d}  ({_format_pct(agg.idle, agg.total)})", file=file)
    print(f"    datapath_util  {agg.datapath_utilization * 100:5.1f}%  "
          f"(productive / total cycles in window)", file=file)

    print(f"  Per-channel breakdown:", file=file)
    print(f"    ch  prod   bp    starv idle  overflow", file=file)
    for c in snap.per_channel:
        ovf_flag = "*" if c.any_overflow else " "
        ovf_decode = ""
        if c.any_overflow:
            ovf_bits = []
            if c.overflow & 0b1000: ovf_bits.append("PROD")
            if c.overflow & 0b0100: ovf_bits.append("BP")
            if c.overflow & 0b0010: ovf_bits.append("STARV")
            if c.overflow & 0b0001: ovf_bits.append("IDLE")
            ovf_decode = "  (" + "|".join(ovf_bits) + " wrapped)"
        print(f"    {c.channel:<2d}  {c.productive:<5d} {c.backpressure:<5d} "
              f"{c.starvation:<5d} {c.idle:<5d} {ovf_flag}{ovf_decode}", file=file)


def format_snapshot(snaps: dict, file=sys.stdout) -> None:
    """Pretty-print the {'r', 'w'} dict returned by read_bus_meters()."""
    format_meter(snaps['r'], file=file)
    print("", file=file)
    format_meter(snaps['w'], file=file)


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Read stream_char's axi_bus_meter CSRs via UART AXIL "
                    "bridge, decode, and print aggregate + per-channel "
                    "utilization."
    )
    p.add_argument("--port", required=True, help="UART device path, e.g. /dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--channels", type=int, default=8,
                   help="NUM_CHANNELS the bitfile was built with (default 8)")
    args = p.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        snaps = read_bus_meters(bridge, args.channels)
    format_snapshot(snaps)
    return 0


if __name__ == "__main__":
    sys.exit(main())
