#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: read_bus_meters
# Purpose: Read the EXTERNAL axi4_dma_observer aggregate bus meter (harness-side,
#          inline on STREAM's shared AXI masters) through the historical
#          read_meter()/read_bus_meters() API.
#
# Why external: the observer meters the bus independently of the DUT's internal
# monitors, so the SAME instrument measures STREAM, RAPIDS, or any third-party IP
# -- apples-to-apples. The DUT needs no monitors of its own (STREAM's in-core
# monitors are compiled out on the FPGA build to fit + close timing). The observer
# buckets are surfaced at harness CSR 0x100-0x11C (see above).
#
# Window control: the harness auto-windows the observer -- it opens+clears the
# meter when the DMA goes busy (after the per-config soft-reset that run_config
# issues) and freezes it 16 idle cycles after the last beat, so the frozen buckets
# bracket exactly one workload. There is nothing for the host to open/close, so
# open_windows()/close_windows() are no-ops kept for call-site compatibility.
#
# The observer taps the shared bus, so the meter is aggregate-only (no per-channel
# breakdown -- per_channel is empty). BucketCounts / ChannelBuckets / MeterSnapshot
# dataclasses are unchanged so callers like run_characterization.py keep working.

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

# External DMA-observer aggregate bus-meter CSRs (harness-side; independent of the
# DUT's internal monitors -- apples-to-apples across ANY IP under test). The
# observer taps STREAM's shared read/write AXI masters inline; the harness auto-
# windows it (opens+clears on DMA busy after a soft-reset, freezes 16 idle cycles
# after the last beat) and surfaces the aggregate buckets here. Read-decode layout
# in harness_csr.sv (0x100-0x11C):
#   0x100 rd_prod  0x104 rd_bp  0x108 rd_starv  0x10C rd_idle
#   0x110 wr_prod  0x114 wr_bp  0x118 wr_starv  0x11C wr_idle
from harness_kick import HARNESS_CSR_BASE  # noqa: E402  (single source of the base)
from harness_addrs import H  # noqa: E402  (by-name harness CSR access)

CSR_OBS_RD_BASE = H("OBS_RD_PROD") # rd prod/bp/starv/idle at +0/4/8/C
CSR_OBS_WR_BASE = H("OBS_WR_PROD") # wr prod/bp/starv/idle at +0/4/8/C
OFF_PROD, OFF_BP, OFF_STARV, OFF_IDLE = 0x0, 0x4, 0x8, 0xC

# Sentinels: run_characterization passes these to read_meter() to pick R vs W.
R_METER_BASE = 'R'
W_METER_BASE = 'W'


# The observer auto-windows in hardware (opens on DMA busy after the per-config
# soft-reset, freezes 16 idle cycles after the last beat), so the historical
# open/close-window calls -- which drove the now-removed in-core monitor RUN bit
# -- are no-ops. Kept so callers that bracket a run keep working unchanged.
def open_windows(bridge):   # noqa: ARG001
    return None


def close_windows(bridge):  # noqa: ARG001
    return None


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
    """Read one side (R or W) of the external DMA-observer aggregate bus meter and
    present it as a MeterSnapshot. `which` is R_METER_BASE ('R') or W_METER_BASE
    ('W'). The observer taps the shared AXI bus, so the meter is aggregate-only --
    there is no per-channel breakdown at a shared-bus tap, so per_channel is empty.
    `num_channels` is accepted for API compatibility and ignored."""
    is_read = (which == R_METER_BASE) or (name.upper().startswith('R'))
    base = CSR_OBS_RD_BASE if is_read else CSR_OBS_WR_BASE
    r = lambda a: bridge.read(a) & 0xFFFF_FFFF
    agg = BucketCounts(
        productive   = r(base + OFF_PROD),
        backpressure = r(base + OFF_BP),
        starvation   = r(base + OFF_STARV),
        idle         = r(base + OFF_IDLE),
    )
    return MeterSnapshot(name=name, aggregate=agg, per_channel=[])


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
    print(f"=== {snap.name}-bus monitor (external DMA observer) ===", file=file)
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
