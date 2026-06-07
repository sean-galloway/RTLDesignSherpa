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
# Record layout is fixed at 24 bytes (3 × 64-bit beats):
#
#     +0x00:  packet[63:0]      (low 64 bits of the 128-bit monbus packet)
#     +0x08:  packet[127:64]    (high 64 bits)
#     +0x10:  source_ts[63:0]   (sampled by monbus_axil_group's counter)
#
# That's 6 × 32-bit UART reads per record. The capture is circular within
# [cfg_mon_base_addr, cfg_mon_limit_addr] -- if the window fills, writes
# wrap to base_addr and overwrite the oldest records. The dump tool reads
# the whole window once and parses every non-zero record it finds.
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
# Fixed record geometry. The variable-mode append knob was removed from
# monbus_axil_group; every record is now 24 bytes (3 × 64-bit beats):
# {packet[63:0], packet[127:64], source_ts[63:0]}.
# ---------------------------------------------------------------------------

RECORD_BYTES = 24
RECORD_BEATS = 3   # 64-bit beats
RECORD_WORDS = 6   # 32-bit UART reads per record


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
    *,
    progress: bool = True,
    progress_every: int = 256,
    progress_label: str = "sram",
) -> List[int]:
    """Read `n_bytes` worth of 32-bit words starting at `base_addr`.
    Returns the list of 32-bit words in linear order. `reader` is any
    callable with UARTAxiBridge.read's signature.

    When `progress=True` (default), prints a `\\r`-updated counter to
    stderr every `progress_every` words so the operator sees the drain
    progressing. A full 256 KB drain over UART is many seconds; sitting
    silent makes it look hung.
    """
    if n_bytes % 4 != 0:
        raise ValueError(
            f"n_bytes must be a multiple of 4 (32-bit words), got {n_bytes}"
        )
    n_words = n_bytes // 4
    out: List[int] = []
    show = progress and n_words > progress_every
    for i in range(n_words):
        addr = base_addr + (i * 4)
        val = reader(addr)
        if val is None:
            raise IOError(
                f"reader returned None at addr 0x{addr:08X} "
                f"(word {i} of {n_words})"
            )
        out.append(val & 0xFFFF_FFFF)
        if show and (i % progress_every == 0):
            pct = 100.0 * i / n_words
            sys.stderr.write(
                f"\r  [{progress_label}] read {i:>7}/{n_words} words "
                f"({pct:5.1f}%)"
            )
            sys.stderr.flush()
    if show:
        sys.stderr.write(
            f"\r  [{progress_label}] read {n_words}/{n_words} words "
            f"(100.0%) done\n"
        )
        sys.stderr.flush()
    return out


def parse_records(words32: Iterable[int]) -> List:
    """Pack 32-bit words into 64-bit beats and parse fixed 24-byte
    records (packet[63:0], packet[127:64], source_ts[63:0]) via
    parse_stream. Zero-padding records (all-zero packet body) are
    skipped by parse_stream itself.

    Returns TimestampedPacket objects with source_ts populated and
    arrival_ts set to None (the group no longer captures a separate
    arrival timestamp).
    """
    beats = words32_to_words64(words32)
    # ts_mode=1 = packet + source_ts (24-byte records, matches the
    # group's fixed output format).
    return list(parse_stream(beats, stride_bytes=RECORD_BYTES, ts_mode=1))


def format_timestamped(rec) -> str:
    """Render a TimestampedPacket as a one-line log entry."""
    if isinstance(rec, MonitorPacket):
        # Defensive: should not happen now that ts_mode is locked to 1,
        # but the parser may legitimately return MonitorPacket if the
        # caller wires up parse_stream with ts_mode=0 directly.
        return format_record(rec, 0)
    src = rec.source_ts if rec.source_ts is not None else 0
    return format_record(rec.packet, src)


# ---------------------------------------------------------------------------
# main loop
# ---------------------------------------------------------------------------

def dump(
    bridge,
    base_addr: int,
    n_bytes: int,
    out=sys.stdout,
) -> int:
    """Read the SRAM region and decode every non-zero record. Returns
    the count of records emitted."""
    words = read_sram_region(bridge.read, base_addr, n_bytes)
    records = parse_records(words)
    for rec in records:
        print(format_timestamped(rec), file=out)
    return len(records)


def _rec_to_raw_pair(rec):
    """Reconstruct (packet_128bit_int, timestamp_64bit_int) from a
    TimestampedPacket. Mirrors MonbusSniffer.records semantics so the
    JSON / CSV output formats are byte-identical to sniffer.dump_*().

    Uses MonitorPacket.raw_packet (the as-captured int) rather than
    .to_raw() — the latter reconstructs from parsed fields and silently
    drops bits not in the field spec, which corrupts the bytes the
    compression encoder needs to see verbatim.
    """
    if hasattr(rec.packet, "raw_packet"):
        pkt_raw = rec.packet.raw_packet
    elif hasattr(rec.packet, "to_raw"):
        pkt_raw = rec.packet.to_raw()
    else:
        pkt_raw = int(rec.packet)
    ts = rec.source_ts if rec.source_ts is not None else 0
    return pkt_raw, ts


def dump_json(
    bridge,
    base_addr: int,
    n_bytes: int,
    path: str,
    extra_meta: Optional[dict] = None,
) -> int:
    """Read the SRAM region and write records as the JSON schema that
    `bin/TBClasses/monbus/sniffer.load_capture()` round-trips into the
    compression encoder. Schema (see sniffer.MonbusSniffer.dump_json):

        {
          "meta": {"label": ..., "schema_version": 1, "record_count": N, ...},
          "records": [
              {"packet": "0x<32 hex>", "timestamp": "0x<16 hex>"},
              ...
          ]
        }

    extra_meta is merged into the meta block — caller typically provides
    a {"label": "<source_name>", ...} dict so the run is identifiable.
    """
    import json
    words = read_sram_region(bridge.read, base_addr, n_bytes)
    records = parse_records(words)
    pairs = [_rec_to_raw_pair(r) for r in records]

    meta = {
        "label": "monbus_sram_dump",
        "schema_version": 1,
        "record_count": len(pairs),
        "source_format": "monbus_axil_group_24B_ts_mode_1",
        "dump_base_addr": f"0x{base_addr:08x}",
        "dump_n_bytes": f"0x{n_bytes:x}",
    }
    if extra_meta:
        meta.update(extra_meta)

    doc = {
        "meta": meta,
        "records": [
            {"packet": f"0x{p:032x}", "timestamp": f"0x{ts:016x}"}
            for p, ts in pairs
        ],
    }
    os.makedirs(os.path.dirname(os.path.abspath(path)) or ".", exist_ok=True)
    with open(path, "w") as f:
        json.dump(doc, f, indent=2)
    return len(pairs)


def dump_csv(
    bridge,
    base_addr: int,
    n_bytes: int,
    path: str,
) -> int:
    """Read the SRAM region and write records as a 2-column CSV
    (packet_hex, timestamp_hex). Matches sniffer.MonbusSniffer.dump_csv()
    so `load_capture()` picks it up unchanged."""
    import csv
    words = read_sram_region(bridge.read, base_addr, n_bytes)
    records = parse_records(words)
    pairs = [_rec_to_raw_pair(r) for r in records]

    os.makedirs(os.path.dirname(os.path.abspath(path)) or ".", exist_ok=True)
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["packet_hex", "timestamp_hex"])
        for p, ts in pairs:
            w.writerow([f"0x{p:032x}", f"0x{ts:016x}"])
    return len(pairs)


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
    p.add_argument("--format", dest="fmt",
                   choices=("text", "json", "csv"), default="text",
                   help="Output format. text (default) prints one "
                        "human-readable line per record to --output (or "
                        "stdout). json/csv write the schema accepted by "
                        "bin/TBClasses/monbus/sniffer.load_capture() — "
                        "drop-in input to the compression encoder.")
    p.add_argument("--output", "-o",
                   help="Output file path. Required for --format=json|csv; "
                        "optional for --format=text (defaults to stdout).")
    p.add_argument("--label",
                   help="JSON-only: 'label' string written into the meta "
                        "block (typically the source/run name).")
    args = p.parse_args(argv)

    if args.fmt in ("json", "csv") and not args.output:
        p.error(f"--format={args.fmt} requires --output")

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        if args.fmt == "text":
            out_stream = sys.stdout
            close_after = False
            if args.output:
                out_stream = open(args.output, "w")
                close_after = True
            try:
                n = dump(bridge, args.base, args.n_bytes, out=out_stream)
            finally:
                if close_after:
                    out_stream.close()
        elif args.fmt == "json":
            extra = {"label": args.label} if args.label else None
            n = dump_json(bridge, args.base, args.n_bytes,
                          args.output, extra_meta=extra)
        else:  # csv
            n = dump_csv(bridge, args.base, args.n_bytes, args.output)
        print(f"# {n} record(s) dumped ({args.fmt})", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
