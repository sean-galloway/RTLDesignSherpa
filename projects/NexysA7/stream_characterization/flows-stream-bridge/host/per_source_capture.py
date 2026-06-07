#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: per_source_capture.py
# Purpose: Per-source isolation runner for the compression-dataset
#          collection (item #2 in the agent-coordination plan).
#
# Workflow:
#   1. Zero every monitor cone enable on every source the harness can
#      drive (currently just the desc-bus monitor inside stream_top_ch8;
#      bridge-mon ports come online once the bridge_stream_char_axil
#      "mon" variant gets wired through stream_char_harness.sv).
#   2. Configure ONE source's cfg_*_enable knobs.
#   3. Hand control to a workload kick (either a subprocess call to
#      run_characterization.py or a small built-in kick pattern).
#   4. After the workload settles, dump_monbus_sram drains the trace
#      SRAM into a per-source file tagged with the source name and
#      timestamp.
#   5. Loop to the next source.
#
# Output: one text file per source under --output-dir, named
#         per_source_<source>_<YYYYMMDD_HHMMSS>.txt. Each line is one
#         decoded record (packet + 64-bit timestamp). Same format as
#         dump_monbus_sram.format_timestamped() so downstream tooling
#         can reuse the existing parsers.
#
# Usage:
#   source $REPO_ROOT/env_python
#   python3 per_source_capture.py \
#       --port /dev/ttyUSB1 \
#       --output-dir /tmp/compression_dataset \
#       --workload-cmd "python3 run_characterization.py --configs 1desc_1ch"
#
#   # Just one source, baseline (no workload kick — only ambient traffic):
#   python3 per_source_capture.py \
#       --port /dev/ttyUSB1 --sources desc_axi \
#       --output-dir /tmp/compression_dataset \
#       --no-kick
#
# Sources today:
#   desc_axi   - The axi4_master_rd_mon inside scheduler_group_array
#                that monitors the descriptor-fetch bus. Cones drive
#                via STREAM_APB's DAXMON registers (offset 0x240..).
#
# Sources reserved (not yet wired through the harness):
#   host_bridge_<port> - per-adapter monitors on bridge_stream_char_axil
#                        once the harness consumes the "mon" variant.
#                        Each adapter (host, stream_apb, harness_csr,
#                        desc_ram, stream_err, debug_sram, dma_axil)
#                        becomes its own source. CFG path will come
#                        from #114 (cfg_*_enable as wrapper ports).
#
# Authors: sean galloway

from __future__ import annotations

import argparse
import datetime
import os
import shlex
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence

# Reuse the existing SRAM dump primitives.
THIS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(THIS_DIR))

from dump_monbus_sram import (  # noqa: E402
    dump_json as dump_sram_to_json,
)

# Address constants — sourced from harness_csr.sv + stream_regs.sv via
# ADDRESS_MAP.md. Re-derived here so the script doesn't depend on the
# run_characterization import chain.
STREAM_APB_BASE = 0x0000_0000  # bridge slave 0
HARNESS_CSR_BASE = 0x0001_0000  # bridge slave 1
DEBUG_SRAM_BASE = 0x0004_0000  # bridge slave 4 (256 KB monbus trace)
DEBUG_SRAM_BYTES = 0x40000     # full 256 KB

# STREAM APB register offsets — desc-bus monitor (DAXMON_*).
# See projects/components/stream/regs/generated/rtl/stream_regs.sv:
#   0x240 DAXMON_ENABLE    [MON_EN, ERR_EN, COMPL_EN, TIMEOUT_EN, PERF_EN]
#   0x244 DAXMON_TIMEOUT   cycles
#   0x248 DAXMON_LATENCY_THRESH
#   0x24c DAXMON_PKT_MASK
DAXMON_ENABLE = STREAM_APB_BASE + 0x240
DAXMON_TIMEOUT = STREAM_APB_BASE + 0x244
DAXMON_LATENCY_THRESH = STREAM_APB_BASE + 0x248
DAXMON_PKT_MASK = STREAM_APB_BASE + 0x24C

# Bit layout of DAXMON_ENABLE (single-bit fields). The PeakRDL block
# packs each enable into the LSB of a 32b register slot, so the
# canonical "all on" value is 0x1F (5 bits).
DAXMON_BITS = {
    "mon":     0,
    "error":   1,
    "compl":   2,
    "timeout": 3,
    "perf":    4,
    # debug doesn't have a runtime knob yet — gated inside the wrapper
    # at synthesis (cfg_debug_enable hardwired to 1'b0 today). #114
    # exposes it; until then, debug traffic depends solely on
    # ENABLE_DEBUG_LOGIC at the wrapper level.
}


@dataclass
class Source:
    """One monitorable packet source on the FPGA.

    setup() programs the cfg knobs so this source's monitor starts
    emitting packets. teardown() is implicit — clear_all_sources()
    zeroes everything before the next iteration."""
    name: str
    description: str
    setup: Callable[["BridgeIO"], None]


class BridgeIO:
    """Thin wrapper around UARTAxiBridge so this script's setup helpers
    don't have to know about the import path. Use as a context manager."""

    def __init__(self, port: str, baud: int):
        self._port = port
        self._baud = baud
        self._bridge = None

    def __enter__(self):
        from uart_axi_bridge import UARTAxiBridge  # noqa: E402
        self._bridge = UARTAxiBridge(port=self._port, baudrate=self._baud)
        self._bridge.__enter__()
        return self

    def __exit__(self, *args):
        self._bridge.__exit__(*args)

    def write(self, addr: int, value: int) -> None:
        self._bridge.write(addr, value)

    def read(self, addr: int) -> Optional[int]:
        return self._bridge.read(addr)


# --- Source setup helpers --------------------------------------------------

def _setup_desc_axi(bridge: BridgeIO) -> None:
    """Configure the desc-bus monitor for full-cone emission.

    Programs DAXMON_ENABLE = 0x1F (all 5 runtime-controllable cones on)
    plus generous timeout/threshold so the cones can actually fire.
    Mask register is left at the default 0 (no packet types dropped)."""
    enable_val = (
        (1 << DAXMON_BITS["mon"])
        | (1 << DAXMON_BITS["error"])
        | (1 << DAXMON_BITS["compl"])
        | (1 << DAXMON_BITS["timeout"])
        | (1 << DAXMON_BITS["perf"])
    )
    bridge.write(DAXMON_ENABLE, enable_val)
    # Timeout: 1 ms at 100 MHz = 100_000 cycles. Generous so we don't
    # generate timeout packets from short workloads.
    bridge.write(DAXMON_TIMEOUT, 100_000)
    # Latency threshold: 1 us at 100 MHz = 100 cycles. Tight so the
    # cone actually fires on real DMA accesses.
    bridge.write(DAXMON_LATENCY_THRESH, 100)
    # No packet types masked out.
    bridge.write(DAXMON_PKT_MASK, 0)


SOURCES: Dict[str, Source] = {
    "desc_axi": Source(
        name="desc_axi",
        description=(
            "axi4_master_rd_mon inside scheduler_group_array. Covers the "
            "descriptor-fetch read path between scheduler_group_array and "
            "desc_ram. Emits error / compl / timeout / perf packets via "
            "DAXMON_* registers."
        ),
        setup=_setup_desc_axi,
    ),
}


# --- Orchestration ---------------------------------------------------------

def clear_all_sources(bridge: BridgeIO) -> None:
    """Zero every monitor enable on every source. Run before each
    isolation iteration so the previous source's cones don't bleed
    into the next trace."""
    # desc_axi: bare cfg_mon_enable wipe shuts every cone off.
    bridge.write(DAXMON_ENABLE, 0)
    # Reset the trace SRAM write pointer + clear sticky overflow so each
    # source's trace starts clean. CTRL bit[1] = clear_stats_pulse.
    bridge.write(HARNESS_CSR_BASE + 0x00, 0x2)
    # Hardware clears auto — give it a few UART roundtrips before we
    # start programming the next source.
    time.sleep(0.05)


def run_workload(workload_cmd: Optional[str], dry_run: bool) -> int:
    """Kick whatever workload is supposed to exercise the source's
    monitor. workload_cmd is a shell command (e.g.
    "python3 run_characterization.py --configs 1desc_1ch"). Returns the
    exit code of the workload, or 0 if no workload was requested."""
    if workload_cmd is None:
        print("  [workload] none requested (--no-kick)", file=sys.stderr)
        return 0
    if dry_run:
        print(f"  [workload] dry-run: {workload_cmd}", file=sys.stderr)
        return 0
    print(f"  [workload] {workload_cmd}", file=sys.stderr)
    return subprocess.run(
        shlex.split(workload_cmd), check=False,
    ).returncode


def capture_one(
    bridge: BridgeIO,
    source: Source,
    output_dir: Path,
    workload_cmd: Optional[str],
    dump_base: int,
    dump_bytes: int,
    workload_settle_s: float,
    dry_run: bool,
) -> Path:
    """Configure one source, kick the workload, dump the trace SRAM.
    Returns the path of the per-source trace file."""
    print(f"\n=== source: {source.name} ===", file=sys.stderr)
    print(f"  {source.description}", file=sys.stderr)

    if not dry_run:
        clear_all_sources(bridge)
        source.setup(bridge)

    rc = run_workload(workload_cmd, dry_run)
    if rc != 0:
        print(f"  [workload] non-zero exit {rc}; capturing anyway",
              file=sys.stderr)
    # Let in-flight packets drain to the SRAM before reading it back.
    if not dry_run:
        time.sleep(workload_settle_s)

    ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    out_path = output_dir / f"per_source_{source.name}_{ts}.json"
    if dry_run:
        print(f"  [dump] dry-run: would write {out_path}", file=sys.stderr)
        return out_path

    # JSON schema matches sniffer.MonbusSniffer.dump_json -> load_capture
    # round-trip — feeds straight into the compression encoder model.
    extra_meta = {
        "label": source.name,
        "description": source.description,
        "captured": ts,
        "workload_cmd": workload_cmd,
        "dump_base": f"0x{dump_base:08x}",
        "dump_bytes": f"0x{dump_bytes:x}",
    }
    n = dump_sram_to_json(
        bridge._bridge, dump_base, dump_bytes,
        str(out_path), extra_meta=extra_meta,
    )
    print(f"  [dump] {n} record(s) -> {out_path}", file=sys.stderr)
    return out_path


def main(argv: Optional[Sequence[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description=(
            "Per-source isolation runner: zero every monitor enable, "
            "configure one source, kick a workload, dump the trace "
            "SRAM, label by source. Loop."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--port", required=True,
                   help="UART device path, e.g. /dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--output-dir", type=Path, required=True,
                   help="Directory for per-source trace files. Created "
                        "if it doesn't exist.")
    p.add_argument("--sources", nargs="+",
                   choices=sorted(SOURCES.keys()) + ["all"],
                   default=["all"],
                   help="Which packet source(s) to capture. 'all' loops "
                        "every defined source. Default: all.")
    p.add_argument("--workload-cmd",
                   help="Shell command that exercises the FPGA so the "
                        "monitor has something to report. Typically "
                        "'python3 run_characterization.py --configs "
                        "<cfg>' or characterize.py.")
    p.add_argument("--no-kick", action="store_true",
                   help="Skip workload kick; capture only ambient/idle "
                        "traffic on each source. Useful for baseline.")
    p.add_argument("--dump-base", type=lambda s: int(s, 0),
                   default=DEBUG_SRAM_BASE,
                   help=f"Base address of the monbus capture SRAM "
                        f"(default 0x{DEBUG_SRAM_BASE:08X}).")
    p.add_argument("--dump-bytes", type=lambda s: int(s, 0),
                   default=DEBUG_SRAM_BYTES,
                   help=f"Bytes to drain from the capture SRAM "
                        f"(default 0x{DEBUG_SRAM_BYTES:X}).")
    p.add_argument("--workload-settle-s", type=float, default=0.25,
                   help="Seconds to wait after the workload returns "
                        "before draining the SRAM. Lets in-flight "
                        "packets land.")
    p.add_argument("--dry-run", action="store_true",
                   help="Print the orchestration plan without touching "
                        "the FPGA. Skips UART connect entirely.")
    args = p.parse_args(argv)

    if "all" in args.sources:
        source_names: List[str] = list(SOURCES.keys())
    else:
        source_names = list(args.sources)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    workload_cmd = None if args.no_kick else args.workload_cmd

    if args.dry_run:
        print(f"[dry-run] would capture sources: {source_names}",
              file=sys.stderr)
        print(f"[dry-run] output dir: {args.output_dir}", file=sys.stderr)
        print(f"[dry-run] workload: {workload_cmd!r}", file=sys.stderr)
        for name in source_names:
            capture_one(
                bridge=None,  # not used in dry-run
                source=SOURCES[name],
                output_dir=args.output_dir,
                workload_cmd=workload_cmd,
                dump_base=args.dump_base,
                dump_bytes=args.dump_bytes,
                workload_settle_s=args.workload_settle_s,
                dry_run=True,
            )
        return 0

    with BridgeIO(args.port, args.baud) as bridge:
        for name in source_names:
            capture_one(
                bridge=bridge,
                source=SOURCES[name],
                output_dir=args.output_dir,
                workload_cmd=workload_cmd,
                dump_base=args.dump_base,
                dump_bytes=args.dump_bytes,
                workload_settle_s=args.workload_settle_s,
                dry_run=False,
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
