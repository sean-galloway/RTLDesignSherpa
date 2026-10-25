#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: dump_monbus
# Purpose: UART-side reader of STREAM's in-core monbus ERROR window.
#
# stream_top_ch8 carries monbus_axil4_group_1wr (write-only). Packets whose
# type is selected in <MON>_ERR_CFG.ERR_SELECT are written as raw 3-beat
# records into the ERROR window [MON_GROUP_ERR_BASE_ADDR, MON_GROUP_ERR_LIMIT_ADDR]
# (the top 4 KB of comp_sram on the Genesys 2 bridge, bridge_windows.
# monbus_err_window()), one irq_out pulse per record, and MON_ERR_REC_COUNT
# counts them. Everything else goes to the trace window (dump_monbus_sram.py).
# This tool reads the records back out of that memory and decodes them via
# the shared TBClasses.monbus parser library, one human-readable line each.
#
# Record layout is fixed at 24 bytes (3 x 64-bit beats), TS, HI, LO order
# (the monitor package spec, docs/markdown/rtl-amba/includes/ocelus_package_spec.md):
#
#     +0x00:  {tag[3:0], source_ts[59:0]}   (timestamp slice, tag=0 raw)
#     +0x08:  packet[127:64]                (high half of the monbus packet)
#     +0x10:  packet[63:0]                  (low half)
#
# Since uart_axi_bridge only does 32-bit reads, each 64-bit beat becomes
# two consecutive 32-bit reads (little-endian: low 32 bits first). One
# record = 6 x 32-bit UART reads. The window is a ring: the burst writer
# rewinds to base when the next record would cross the limit (it never
# splits a record across the wrap), so with 4 KB the 171st record
# overwrites the first.
#
# Usage:
#     env_python && \
#     python3 dump_monbus.py --port /dev/ttyUSB3            # window + count by name
#     python3 dump_monbus.py --port /dev/ttyUSB3 --base 0x1AF000 --count 10
#
# Pure functions (words32_to_beats64, beats_to_packet, read_one_record,
# drain_loop) are split out from the UART loop so they unit-test without
# hardware (bin/tests/test_dump_monbus.py).
import argparse
import os
import sys
import time
from typing import Callable, Iterable, List, Optional, Tuple

# Repo-relative imports. Mirror the import shim every other host script
# in this directory uses (uart_axi_bridge lives outside the host tree).
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    # Best-effort fallback: walk up to the repo root.
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

sys.path.insert(0, os.path.join(_repo_root, "projects/components/utility-ip/converters/bin"))
sys.path.insert(0, os.path.join(_repo_root, "bin"))

# Library imports (no hardware required).
from TBClasses.monbus import (  # noqa: E402
    parse,
    MonitorPacket,
    MONBUS_PKT_WIDTH,
    MONBUS_TS_WIDTH,
)


# =============================================================================
# Constants
# =============================================================================

# Number of 64-bit beats per record: fixed at 3 (source_ts, packet_hi,
# packet_lo -- TS, HI, LO order) by the group's record format.
BEATS_PER_RECORD = 3
WORDS_PER_RECORD = BEATS_PER_RECORD * 2  # 6 × 32-bit
RECORD_BYTES = BEATS_PER_RECORD * 8      # 24


# =============================================================================
# Pure functions -- unit-testable without hardware
# =============================================================================

def words32_to_beats64(words32: Iterable[int]) -> List[int]:
    """Pack consecutive 32-bit words into 64-bit beats, little-endian
    (low 32 bits first). Length must be even."""
    ws = list(words32)
    if len(ws) % 2 != 0:
        raise ValueError(
            f"words32_to_beats64 needs an even count, got {len(ws)}"
        )
    return [
        ((ws[i + 1] & 0xFFFF_FFFF) << 32) | (ws[i] & 0xFFFF_FFFF)
        for i in range(0, len(ws), 2)
    ]


def beats_to_packet(beats_64: List[int]) -> Tuple[MonitorPacket, int]:
    """Reassemble three 64-bit beats into a parsed packet + source
    timestamp. Beat ordering is the group's record format (TS, HI, LO),
    rtl/amba/ocelus/monbus_group_core_1wr.sv:
        beats_64[0] = {tag[3:0], source_ts[59:0]}   (timestamp slice)
        beats_64[1] = packet[127:64]                (high half)
        beats_64[2] = packet[63:0]                  (low half)
    """
    if len(beats_64) != BEATS_PER_RECORD:
        raise ValueError(
            f"beats_to_packet expects {BEATS_PER_RECORD} beats, "
            f"got {len(beats_64)}"
        )
    raw_pkt = ((beats_64[1] & ((1 << 64) - 1)) << 64) \
            | (beats_64[2] & ((1 << 64) - 1))
    # beat 0 carries {tag[3:0], source_ts[59:0]}; strip the 4-bit encoding tag.
    source_ts = beats_64[0] & ((1 << 60) - 1)
    return parse(raw_pkt), source_ts


def read_one_record(
    reader: Callable[[int], Optional[int]],
    base_addr: int,
) -> Tuple[MonitorPacket, int]:
    """Issue WORDS_PER_RECORD consecutive 32-bit reads starting at
    `base_addr` via the supplied `reader` callable (signature: addr -> int)
    and return the decoded packet + source timestamp. `base_addr` is the
    record's slot in the error window (base + n * RECORD_BYTES)."""
    words: List[int] = []
    for i in range(WORDS_PER_RECORD):
        addr = base_addr + (i * 4)
        val = reader(addr)
        if val is None:
            raise IOError(
                f"reader returned None on word {i} at addr 0x{addr:08X}"
            )
        words.append(val)
    beats = words32_to_beats64(words)
    return beats_to_packet(beats)


def format_record(pkt: MonitorPacket, source_ts: int) -> str:
    """One-line human summary of a decoded record. Format matches the
    sim-side log convention to make grep-across-sources easy:
        @0x<ts>  [<protocol>_<type>]  <event_name>  Agent:XX Unit:Y Ch:ZZ
                                                     Data:0x<event_data>
    """
    return (
        f"@0x{source_ts:016x}  "
        f"[{pkt.get_protocol_name()}_{pkt.get_packet_type_name()}]  "
        f"{pkt.get_event_code_name()}  "
        f"Agent:{pkt.agent_id:02X} Unit:{pkt.unit_id:X} "
        f"Ch:{pkt.channel_id:02X}  "
        f"Data:0x{pkt.event_data:016x}"
    )


# =============================================================================
# Main loop -- needs the UART bridge
# =============================================================================

def drain_loop(
    bridge,
    base_addr: int,
    count: Optional[int],
    follow: bool,
    poll_interval: float,
    out=sys.stdout,
    capacity: Optional[int] = None,
) -> int:
    """Read `count` records from the error window starting at `base_addr`
    (record n at base_addr + n * RECORD_BYTES, wrapping at `capacity`
    records when given) and print one line each. Returns the number
    printed. `bridge` is anything with a `.read(addr)` method matching
    UARTAxiBridge.

    An all-zero slot is one the writer has not reached yet: without
    --follow that ends the read; with --follow the slot is re-polled
    until a record lands in it (the window is zeroed per run by the host,
    so a stale record cannot pose as a fresh one)."""
    drained = 0
    slot = 0
    while True:
        if count is not None and drained >= count:
            break
        if capacity is not None and slot >= capacity:
            slot = 0
        addr = base_addr + slot * RECORD_BYTES
        try:
            pkt, source_ts = read_one_record(bridge.read, addr)
        except IOError as e:
            print(f"# read error: {e}", file=sys.stderr)
            if not follow:
                return drained
            time.sleep(poll_interval)
            continue
        if pkt.raw_packet == 0 and source_ts == 0:
            if not follow:
                break
            time.sleep(poll_interval)
            continue
        print(format_record(pkt, source_ts), file=out)
        drained += 1
        slot += 1
    return drained


def main(argv=None) -> int:
    p = argparse.ArgumentParser(
        description="UART-side reader of STREAM's in-core monbus error window.")
    p.add_argument("--port", required=True,
                   help="UART device path, e.g. /dev/ttyUSB3 (Genesys 2 FT232R)")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--base", type=lambda s: int(s, 0), default=None,
                   help="Error window base (default: bridge_windows."
                        "monbus_err_window(), the top 4 KB of comp_sram)")
    p.add_argument("--count", type=int, default=None,
                   help="Records to read (default: MON_ERR_REC_COUNT from the "
                        "DUT, by name; capped at the window's capacity)")
    p.add_argument("--follow", action="store_true",
                   help="Keep polling an empty slot until a record lands in it")
    p.add_argument("--poll-interval", type=float, default=0.1,
                   help="Seconds between polls when --follow hits an empty slot")
    args = p.parse_args(argv)

    from bridge_windows import monbus_err_window  # noqa: E402
    from stream_addrs import A                    # noqa: E402  (by name, never offsets)
    err_base, err_limit = monbus_err_window()
    capacity = (err_limit + 1 - err_base) // RECORD_BYTES
    base_addr = err_base if args.base is None else args.base

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        count = args.count
        if count is None:
            landed = bridge.read(A("MON_ERR_REC_COUNT")) & 0xFFFF
            count = min(landed, capacity)
            print(f"# MON_ERR_REC_COUNT={landed} (window holds {capacity}); "
                  f"reading {count} from 0x{base_addr:08X}", file=sys.stderr)
        return 0 if drain_loop(
            bridge,
            base_addr=base_addr,
            count=count,
            follow=args.follow,
            poll_interval=args.poll_interval,
            capacity=capacity,
        ) >= 0 else 1


if __name__ == "__main__":
    sys.exit(main())
