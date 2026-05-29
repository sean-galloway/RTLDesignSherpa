#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: dump_monbus_sram
# Purpose: UART-side dump of the bridge's monbus capture SRAM region.
#
# Companion to dump_monbus.py. The two scripts target the two output
# paths of monbus_axil_group:
#
#   dump_monbus.py      <- drains the CPU IRQ-facing err_fifo via the
#                          s_mon_axil_* slave read port (3 beats per
#                          packet, slice-counter drain semantics).
#
#   dump_monbus_sram.py <- this script. Reads a memory region that
#                          collected the m_mon_axil_* MASTER writes
#                          (the bulk monitor-trace dump path used by
#                          stream_char's debug_sram).
#
# In stream_char today, monbus_axil_group is configured with
# cfg_ts_append_enable=1 and cfg_ts_append_mode=2'b11 (both source AND
# arrival timestamps appended), so each record is 32 bytes:
#
#     +0x00:  packet[63:0]      (low 64 bits of the 128-bit monbus packet)
#     +0x08:  packet[127:64]    (high 64 bits)
#     +0x10:  source_ts[63:0]   (sampled at the producing wrapper)
#     +0x18:  arrival_ts[63:0]  (sampled at monbus_axil_group input)
#
# That's 8 × 32-bit UART reads per record. The on-FPGA capture is
# circular within [cfg_mon_base_addr, cfg_mon_limit_addr] -- if the
# window fills, writes wrap to base_addr and overwrite the oldest
# records. The dump tool reads the whole window once and parses every
# non-zero record it finds.
#
# Usage:
#     env_python
#     python3 dump_monbus_sram.py --port /dev/ttyUSB1 \
#         --base 0x00040000 --bytes 0x40000
#
# Library functions (read_sram_region, parse_records) are split out so
# the parse path unit-tests without hardware.

import argparse
import os
import sys
from typing import Callable, Iterable, List, Optional

# Same import shim every host script uses.
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    candidate = HERE
    while candidate != "/" and not os.path.isdir(os.path.join(candidate, ".git")):
        candidate = os.path.dirname(candidate)
    if os.path.isdir(os.path.join(candidate, ".git")):
        _repo_root = candidate
    else:
        raise RuntimeError(
            "REPO_ROOT not set and no .git ancestor found. "
            "Source env_python or export REPO_ROOT before running."
        )

sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))
sys.path.insert(0, os.path.join(_repo_root, "bin"))

from TBClasses.monbus import (  # noqa: E402
    parse_stream,
    MonitorPacket,
    MONBUS_TS_WIDTH,
)

# Re-use the formatter from the FIFO drain script -- the two scripts
# decode different transport layers but agree on the on-the-wire
# representation, so the print format stays identical.
from dump_monbus import format_record  # noqa: E402


# ---------------------------------------------------------------------------
# Record-size knobs corresponding to monbus_axil_group's cfg_ts_append_mode.
# Pre-canned constants so the CLI / callers don't have to remember the
# mode-to-stride translation:
#     mode 0:  packet only          -> 16 bytes / 4 words
#     mode 1:  packet + source_ts   -> 24 bytes / 6 words
#     mode 2:  packet + arrival_ts  -> 24 bytes / 6 words
#     mode 3:  packet + both ts     -> 32 bytes / 8 words   (stream_char default)
# ---------------------------------------------------------------------------

MODE_TO_STRIDE_BYTES = {0: 16, 1: 24, 2: 24, 3: 32}


# ---------------------------------------------------------------------------
# Pure functions -- unit-testable without hardware
# ---------------------------------------------------------------------------

def words32_to_words64(words32: Iterable[int]) -> List[int]:
    """Pack consecutive 32-bit words into 64-bit beats (little-endian:
    low 32 bits first). Length must be even."""
    ws = list(words32)
    if len(ws) % 2 != 0:
        raise ValueError(
            f"words32_to_words64 needs an even count, got {len(ws)}"
        )
    return [
        ((ws[i + 1] & 0xFFFF_FFFF) << 32) | (ws[i] & 0xFFFF_FFFF)
        for i in range(0, len(ws), 2)
    ]


def read_sram_region(
    reader: Callable[[int], Optional[int]],
    base_addr: int,
    n_bytes: int,
) -> List[int]:
    """Read `n_bytes` worth of 32-bit words starting at `base_addr`.
    Returns the list of 32-bit words in linear order. `reader` is any
    callable with UARTAxiBridge.read's signature."""
    if n_bytes % 4 != 0:
        raise ValueError(
            f"n_bytes must be a multiple of 4 (32-bit words), got {n_bytes}"
        )
    n_words = n_bytes // 4
    out: List[int] = []
    for i in range(n_words):
        addr = base_addr + (i * 4)
        val = reader(addr)
        if val is None:
            raise IOError(
                f"reader returned None at addr 0x{addr:08X} "
                f"(word {i} of {n_words})"
            )
        out.append(val & 0xFFFF_FFFF)
    return out


def parse_records(
    words32: Iterable[int],
    ts_mode: int = 3,
) -> List:
    """Pack the input 32-bit words into 64-bit beats, then feed to
    parse_stream() with the matching `stride_bytes`. Returns the list
    of decoded records.

    `ts_mode`:
        0 - packet only (16-byte records)
        1 - packet + source_ts (24-byte)
        2 - packet + arrival_ts (24-byte)
        3 - packet + both timestamps (32-byte)   <-- stream_char default

    Returns:
        MonitorPacket objects when ts_mode == 0; otherwise
        TimestampedPacket objects with source_ts/arrival_ts populated
        per mode. Zero-padding records (all-zero packet body) are
        skipped by parse_stream itself.
    """
    if ts_mode not in MODE_TO_STRIDE_BYTES:
        raise ValueError(
            f"ts_mode must be one of {sorted(MODE_TO_STRIDE_BYTES)}, "
            f"got {ts_mode}"
        )
    stride = MODE_TO_STRIDE_BYTES[ts_mode]
    beats = words32_to_words64(words32)
    return list(parse_stream(beats, stride_bytes=stride, ts_mode=ts_mode))


def format_timestamped(rec) -> str:
    """Render a TimestampedPacket as a one-line log entry. Falls back
    to the bare-packet formatter when the record carries no timestamps
    (ts_mode=0)."""
    if isinstance(rec, MonitorPacket):
        # ts_mode == 0 path: bare packet, no timestamp at all.
        return format_record(rec, 0)
    # TimestampedPacket
    src = rec.source_ts if rec.source_ts is not None else 0
    arr = rec.arrival_ts if rec.arrival_ts is not None else 0
    base = format_record(rec.packet, src)
    if rec.arrival_ts is not None and rec.source_ts is not None:
        base += f"  arr=0x{arr:016x}  drift={(arr - src) & ((1 << 64) - 1):d}"
    elif rec.arrival_ts is not None:
        base += f"  arr=0x{arr:016x}"
    return base


# ---------------------------------------------------------------------------
# main loop
# ---------------------------------------------------------------------------

def dump(
    bridge,
    base_addr: int,
    n_bytes: int,
    ts_mode: int,
    out=sys.stdout,
) -> int:
    """Read the SRAM region and decode every non-zero record. Returns
    the count of records emitted."""
    words = read_sram_region(bridge.read, base_addr, n_bytes)
    records = parse_records(words, ts_mode=ts_mode)
    for rec in records:
        print(format_timestamped(rec), file=out)
    return len(records)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[3])
    p.add_argument("--port", required=True,
                   help="UART device path, e.g. /dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--base", type=lambda s: int(s, 0), required=True,
                   help="SoC address of the SRAM region holding the "
                        "monbus capture (in stream_char: 0x00040000)")
    p.add_argument("--bytes", dest="n_bytes",
                   type=lambda s: int(s, 0), required=True,
                   help="Number of bytes to read (in stream_char: 0x40000 "
                        "for the full 256 KB debug_sram)")
    p.add_argument("--ts-mode", type=int, default=3,
                   choices=sorted(MODE_TO_STRIDE_BYTES),
                   help="monbus_axil_group cfg_ts_append_mode value the "
                        "FPGA was configured with (default 3: both "
                        "source + arrival timestamps; stream_char's "
                        "current setting)")
    args = p.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        n = dump(bridge, args.base, args.n_bytes, args.ts_mode)
        print(f"# {n} record(s) dumped", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
