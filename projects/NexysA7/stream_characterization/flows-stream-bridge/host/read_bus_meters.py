#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: read_bus_meters
# Purpose: Compatibility shim -- reads the IN-CORE STREAM datapath perf monitors
#          and presents them through the legacy axi_bus_meter API.
#
# RFC Stage E option 2 (Stage E.4) retired the harness-side axi_bus_meter blocks
# (their CSRs at HARNESS_CSR_BASE + 0x100 / 0x180 were removed). Datapath
# utilization is now measured IN-CORE by stream_core's RDMON/WRMON perf monitors
# + per-channel axi_bus_meter, surfaced through the STREAM regblock perf CSRs.
#
# This module keeps the historical read_meter()/read_bus_meters() interface
# (and the BucketCounts / ChannelBuckets / MeterSnapshot dataclasses) so callers
# like run_characterization.py keep working -- it just sources the numbers from
# the in-core CSRs (via read_rw_perf) instead of the deleted harness meters.
#
# Window control: the in-core monitor accumulates while RDMON/WRMON_PERF_CTRL.RUN
# is 1. The caller opens the window before the workload and closes it right after
# completion (open_windows/close_windows are re-exported from read_rw_perf). The
# aggregate buckets are 32-bit; per-channel are 16-bit with a sticky overflow
# mask, exactly as the legacy meter.

import argparse
import os
import sys
from dataclasses import dataclass
from typing import List

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

# In-core CSR offsets (STREAM regblock; mirror stream_regmap.py). RDMON_PERF and
# WRMON_PERF aggregate buckets are 32-bit separate registers; per-channel is read
# via the PERF_CH_SEL indexed mechanism.
from read_rw_perf import (  # noqa: E402
    RDMON_PERF_BASE, WRMON_PERF_BASE,
    OFF_PROD_CYCLES, OFF_BP_CYCLES, OFF_STARV_CYCLES, OFF_IDLE_CYCLES,
    PERF_CH_SEL, RDMON_PERF_CH_PROD_BP, RDMON_PERF_CH_STARV_IDLE,
    WRMON_PERF_CH_PROD_BP, WRMON_PERF_CH_STARV_IDLE,
    RDMON_PERF_CH_OVERFLOW, WRMON_PERF_CH_OVERFLOW,
    open_windows, close_windows,  # re-exported so the sweep can bracket the run
)

# Legacy sentinels. run_characterization passes these to read_meter(); they now
# select the in-core bus rather than a harness CSR base address.
R_METER_BASE = 'R'
W_METER_BASE = 'W'


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
        """Productive / (productive + backpressure + starvation + idle): the
        fraction of in-window cycles that delivered data. 0 if the window saw
        no cycles (never opened)."""
        t = self.total
        return self.productive / t if t > 0 else 0.0


@dataclass(frozen=True)
class ChannelBuckets(BucketCounts):
    channel: int
    overflow: int  # 4-bit mask {prod, bp, starv, idle}; bit set = 16-bit wrap


@dataclass(frozen=True)
class MeterSnapshot:
    name: str
    aggregate: BucketCounts
    per_channel: List[ChannelBuckets]


# ---------------------------------------------------------------------------
# Reader (in-core CSRs, legacy API)
# ---------------------------------------------------------------------------

def read_meter(bridge, which: str, num_channels: int, name: str) -> MeterSnapshot:
    """Read one in-core datapath monitor (R or W) and present it as a legacy
    MeterSnapshot. `which` is R_METER_BASE ('R') or W_METER_BASE ('W')."""
    is_read = (which == R_METER_BASE) or (name.upper().startswith('R'))
    agg_base = RDMON_PERF_BASE if is_read else WRMON_PERF_BASE
    ch_prod_bp    = RDMON_PERF_CH_PROD_BP    if is_read else WRMON_PERF_CH_PROD_BP
    ch_starv_idle = RDMON_PERF_CH_STARV_IDLE if is_read else WRMON_PERF_CH_STARV_IDLE
    ch_overflow   = RDMON_PERF_CH_OVERFLOW   if is_read else WRMON_PERF_CH_OVERFLOW

    r = lambda a: bridge.read(a) & 0xFFFF_FFFF
    agg = BucketCounts(
        productive   = r(agg_base + OFF_PROD_CYCLES),
        backpressure = r(agg_base + OFF_BP_CYCLES),
        starvation   = r(agg_base + OFF_STARV_CYCLES),
        idle         = r(agg_base + OFF_IDLE_CYCLES),
    )
    ovf_word = r(ch_overflow)

    per_channel: List[ChannelBuckets] = []
    for ch in range(num_channels):
        bridge.write(PERF_CH_SEL, ch)
        pb = r(ch_prod_bp)
        si = r(ch_starv_idle)
        per_channel.append(ChannelBuckets(
            channel=ch,
            productive=pb & 0xFFFF,
            backpressure=(pb >> 16) & 0xFFFF,
            starvation=si & 0xFFFF,
            idle=(si >> 16) & 0xFFFF,
            overflow=(ovf_word >> (4 * ch)) & 0xF,
        ))
    return MeterSnapshot(name=name, aggregate=agg, per_channel=per_channel)


def read_bus_meters(bridge, num_channels: int) -> dict:
    """Read both R and W in-core monitors -> {'r': MeterSnapshot, 'w': ...}."""
    return {
        'r': read_meter(bridge, R_METER_BASE, num_channels, 'R'),
        'w': read_meter(bridge, W_METER_BASE, num_channels, 'W'),
    }


# ---------------------------------------------------------------------------
# Pretty-printing (unchanged)
# ---------------------------------------------------------------------------

def _format_pct(num: int, den: int) -> str:
    if den == 0:
        return "  n/a"
    return f"{(100.0 * num / den):5.1f}%"


def format_meter(snap: MeterSnapshot, file=sys.stdout) -> None:
    agg = snap.aggregate
    print(f"=== {snap.name}-bus monitor (in-core) ===", file=file)
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
        ovf_flag = "*" if c.overflow else " "
        ovf_decode = ""
        if c.overflow:
            ovf_bits = []
            if c.overflow & 0b1000: ovf_bits.append("PROD")
            if c.overflow & 0b0100: ovf_bits.append("BP")
            if c.overflow & 0b0010: ovf_bits.append("STARV")
            if c.overflow & 0b0001: ovf_bits.append("IDLE")
            ovf_decode = "  (" + "|".join(ovf_bits) + " wrapped)"
        print(f"    {c.channel:<2d}  {c.productive:<5d} {c.backpressure:<5d} "
              f"{c.starvation:<5d} {c.idle:<5d} {ovf_flag}{ovf_decode}", file=file)


def format_snapshot(snaps: dict, file=sys.stdout) -> None:
    format_meter(snaps['r'], file=file)
    print("", file=file)
    format_meter(snaps['w'], file=file)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="Read the STREAM in-core datapath perf monitors via UART "
                    "AXIL bridge (legacy axi_bus_meter-compatible view; RFC "
                    "Stage E option 2)."
    )
    p.add_argument("--port", required=True, help="UART device path, e.g. /dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--channels", type=int, default=8,
                   help="NUM_CHANNELS the bitfile was built with (default 8)")
    p.add_argument("--close", action="store_true",
                   help="freeze the windows (RUN=0) before reading")
    args = p.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        if args.close:
            close_windows(bridge)
        snaps = read_bus_meters(bridge, args.channels)
    format_snapshot(snaps)
    return 0


if __name__ == "__main__":
    sys.exit(main())
