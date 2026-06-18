#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: dump_monbus
# Purpose: UART-side drainer for the bridge's monbus AXIL error FIFO.
#
# Drains the s_mon_axil_* slave port of a monitored bridge over the UART
# AXI bridge, decodes the 192-bit records ({packet[127:0], source_ts[63:0]})
# via the shared TBClasses.monbus parser library, and prints one human-
# readable line per packet.
#
# Each error-FIFO record drains as three 64-bit beats per the
# monbus_axil_axil_group slice-counter read path (and the monitor package
# spec, docs/markdown/RTLAmba/includes/monitor_package_spec.md) -- TS, HI, LO:
#
#     beat 0:  {tag[3:0], source_ts[59:0]}   (timestamp slice, tag=0 raw)
#     beat 1:  packet[127:64]                (high half of the monbus packet)
#     beat 2:  packet[63:0]                  (low half)
#
# Since uart_axi_bridge only does 32-bit reads, each 64-bit beat becomes
# two consecutive 32-bit reads (little-endian: low 32 bits first). One
# full packet = 6 × 32-bit UART reads = 3 × 64-bit beats = 1 record. With a
# 32-bit err-drain (monbus_axil_axil_group S_AXIL_DATA_WIDTH=32, as wired in
# stream_top_ch8) the group's 2:1 read serializer presents the low then high
# 32-bit half of each slice, so the same 6-read sequence applies.
#
# Usage:
#     env_python && \
#     python3 dump_monbus.py --port /dev/ttyUSB1 --base 0xC0000000 --count 10
#
# Pure functions (words32_to_beats64, beats_to_packet, read_one_record)
# are split out from the UART loop so they unit-test without hardware.

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

sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))
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

# Number of 64-bit beats per error-FIFO record. The monbus_axil_axil_group
# slicer is fixed at 3 (source_ts, packet_hi, packet_lo -- TS, HI, LO order).
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
    timestamp. Beat ordering matches the slicer in
    rtl/amba/shared/monbus_axil_axil_group.sv (TS, HI, LO):
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
    word_stride: int = 0,
) -> Tuple[MonitorPacket, int]:
    """Issue WORDS_PER_RECORD 32-bit reads via the supplied `reader`
    callable (signature: addr -> int) and return the decoded packet +
    source timestamp.

    `word_stride`:
        0 - read every word at the same address (drain semantics
            against an internal slice counter; the bridge's
            monbus_axil_axil_group slicer ignores address)
        4 - read at incrementing 32-bit word offsets (works through
            standard SoC width converters that increment per beat)
    """
    if word_stride not in (0, 4):
        raise ValueError(f"word_stride must be 0 or 4, got {word_stride}")
    words: List[int] = []
    for i in range(WORDS_PER_RECORD):
        addr = base_addr + (i * word_stride)
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
    word_stride: int,
    count: Optional[int],
    follow: bool,
    poll_interval: float,
    out=sys.stdout,
) -> int:
    """Drain `count` packets (or forever if follow). Returns the number
    drained. `bridge` is anything with a `.read(addr)` method matching
    UARTAxiBridge."""
    drained = 0
    while True:
        if count is not None and drained >= count:
            break
        try:
            pkt, source_ts = read_one_record(bridge.read, base_addr, word_stride)
        except IOError as e:
            print(f"# read error: {e}", file=sys.stderr)
            if not follow:
                return drained
            time.sleep(poll_interval)
            continue
        # If the packet is all-zero, the FIFO was empty and the slicer
        # returned zeros. Don't print empties.
        if pkt.raw_packet == 0 and source_ts == 0:
            if not follow:
                break
            time.sleep(poll_interval)
            continue
        print(format_record(pkt, source_ts), file=out)
        drained += 1
    return drained


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[3])
    p.add_argument("--port", required=True,
                   help="UART device path, e.g. /dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--base", type=lambda s: int(s, 0), required=True,
                   help="SoC AXIL base address of the bridge's "
                        "s_mon_axil_* slave port")
    p.add_argument("--word-stride", type=int, default=4, choices=(0, 4),
                   help="32-bit address stride between reads (default 4: "
                        "standard SoC width-converter behaviour; 0: same "
                        "address every time, relies on bridge's internal "
                        "slice counter)")
    p.add_argument("--count", type=int, default=None,
                   help="Stop after draining N packets (default: until "
                        "FIFO drains empty or --follow keeps polling)")
    p.add_argument("--follow", action="store_true",
                   help="Keep polling after the FIFO drains empty")
    p.add_argument("--poll-interval", type=float, default=0.1,
                   help="Seconds between polls when --follow and FIFO is empty")
    args = p.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge  # noqa: E402
    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        return 0 if drain_loop(
            bridge,
            base_addr=args.base,
            word_stride=args.word_stride,
            count=args.count,
            follow=args.follow,
            poll_interval=args.poll_interval,
        ) >= 0 else 1


if __name__ == "__main__":
    sys.exit(main())
