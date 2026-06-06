# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Public API for the monbus packet library.
#
# Two layers:
#   * Standalone parser (no cocotb dependency) -- use these in regular
#     Python scripts, log post-processors, or anywhere you have a raw
#     128-bit packet you want to decode:
#         from TBClasses.monbus import parse, MonitorPacket
#         pkt = parse(0x0042c08000000000_0000000000123456)
#         print(pkt.get_event_code_name())   # e.g. 'AXI_ERR_DATA_ORPHAN'
#         print(pkt)                          # human-readable summary
#         for p in pkt_stream:
#             if p.matches(packet_type=PktType.PktTypeError, unit_id=2):
#                 ...
#
#   * cocotb-aware classes -- use these inside cocotb tests where you
#     already have a GAXIPacket sitting in a slave's recvQ:
#         from TBClasses.monbus.monbus_packet import MonbusPacket
#         pkt = MonbusPacket(gaxi_packet)
#
# The cocotb-aware MonbusPacket is intentionally NOT re-exported here so
# the standalone parser side stays free of cocotb / BFM imports and is
# usable from plain scripts and CI tooling.

from .monbus_types import (
    # Width constants
    MONBUS_PKT_WIDTH, MONBUS_TS_WIDTH,
    # Enums
    ProtocolType,
    PktType,
    # ARB
    ARBErrorCode, ARBTimeoutCode, ARBCompletionCode,
    ARBThresholdCode, ARBPerformanceCode, ARBDebugCode,
    # AXI4
    AXIErrorCode, AXITimeoutCode, AXICompletionCode,
    AXIThresholdCode, AXIPerformanceCode, AXIAddrMatchCode, AXIDebugCode,
    # APB
    APBErrorCode, APBTimeoutCode, APBCompletionCode,
    APBThresholdCode, APBPerformanceCode, APBDebugCode,
    # AXIS
    AXISErrorCode, AXISTimeoutCode, AXISCompletionCode,
    AXISCreditCode, AXISChannelCode, AXISStreamCode,
    # Standalone parser (no cocotb dep)
    MonitorPacket,
    # Field accessors (work on raw int)
    get_packet_type, get_protocol, get_event_code,
    get_channel_id, get_unit_id, get_agent_id, get_event_data,
    get_reserved,
    create_monitor_packet,
    # Name lookups
    get_protocol_name, get_packet_type_name, get_event_code_name,
    get_event_code_enum,
    # Validation
    is_valid_protocol_type, is_valid_packet_type, is_valid_event_code,
    validate_monitor_packet,
    # Debug helpers
    debug_packet_bits, format_packet_fields,
)

from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class TimestampedPacket:
    """A monitor packet paired with its captured timestamps.

    Emitted by `parse_stream` when `ts_mode` is non-zero. `source_ts` /
    `arrival_ts` are None when the corresponding append slot is not in
    use for the requested mode.
    """
    packet: 'MonitorPacket'
    source_ts: Optional[int]
    arrival_ts: Optional[int]


def parse(raw_packet):
    """Top-level convenience: parse a raw 128-bit int into a MonitorPacket.

    >>> p = parse(0x0042c08000000000_0000000000123456)
    >>> p.get_packet_type_name()
    'PktTypeError'
    """
    if not isinstance(raw_packet, int):
        raise TypeError(f"parse() expects int, got {type(raw_packet).__name__}")
    return MonitorPacket.from_raw(raw_packet & ((1 << MONBUS_PKT_WIDTH) - 1))


def parse_stream(raw_words, stride_bytes: int = 24, ts_mode: int = 1):
    """Parse a memory dump produced by monbus_axil_group.

    The capture region is written by a 64-bit AXIL master in fixed-size
    records. The canonical bulk-trace format is **24 bytes / 3 beats**:

        beat 0 = {tag[3:0], source_ts[59:0]}   tag = 4'h0 means "raw, no compression"
        beat 1 = packet[127:64]
        beat 2 = packet[63:0]

    The top 4 bits of beat 0 are an on-the-wire encoding tag reserved
    for a future compression block sitting upstream of monbus_axil_group;
    today every record arrives with tag = 0 (raw). Non-zero tags are
    treated as unrecognised and the record is skipped with a warning
    (see `unknown_tags` below) — once the compressor lands, a follow-up
    decoder will handle them and emit reconstructed records.

      | stride | ts_mode | record contents (beat order, low → high addr) |
      | ------ | ------- | ---------------------------------------------- |
      |     16 |       0 | packet[127:64], packet[63:0]                   |
      |     24 |       1 | {tag, source_ts[59:0]}, packet[127:64], packet[63:0] |
      |     24 |       2 | {tag, arrival_ts[59:0]}, packet[127:64], packet[63:0] |
      |     32 |       3 | {tag, source_ts[59:0]}, {tag, arrival_ts[59:0]}, packet[127:64], packet[63:0] |

    `raw_words` is an iterable of 64-bit ints (each one AXIL beat).
    Yields `MonitorPacket` when ts_mode == 0, otherwise `TimestampedPacket`.

    Records whose packet body is all-zero are skipped (uninitialised
    SRAM / write-FIFO padding).
    """
    beats_per_record = stride_bytes // 8
    if beats_per_record not in (2, 3, 4):
        raise ValueError(f"unsupported stride_bytes={stride_bytes}")

    TAG_RAW = 0x0
    TS_MASK = (1 << 60) - 1
    TAG_SHIFT = 60

    def _split_tagged_ts(beat):
        """Return (tag, ts_60bit) from a 64-bit timestamp beat."""
        return ((beat >> TAG_SHIFT) & 0xF, beat & TS_MASK)

    buf = []
    for word in raw_words:
        buf.append(word & ((1 << 64) - 1))
        if len(buf) < beats_per_record:
            continue

        if ts_mode == 0:
            # No timestamp beats — packet is high-then-low across 2 beats.
            pkt_hi, pkt_lo = buf[0], buf[1]
            raw_pkt = (pkt_hi << 64) | pkt_lo
            if raw_pkt == 0:
                buf.clear()
                continue
            yield parse(raw_pkt)
        else:
            # Timestamp beat(s) come first, then packet high, then packet low.
            ts_beats = ts_mode if ts_mode in (1, 2) else 2  # 1 ts beat or 2
            tags = []
            tss = []
            for i in range(ts_beats):
                tag, ts = _split_tagged_ts(buf[i])
                tags.append(tag)
                tss.append(ts)
            pkt_hi = buf[ts_beats]
            pkt_lo = buf[ts_beats + 1]
            raw_pkt = (pkt_hi << 64) | pkt_lo
            if raw_pkt == 0:
                buf.clear()
                continue
            # Today only TAG_RAW (0) is defined. Non-zero tags reserved for
            # the upcoming compression encoder — skip with no decode.
            if any(t != TAG_RAW for t in tags):
                buf.clear()
                continue
            pkt = parse(raw_pkt)
            if ts_mode == 1:
                yield TimestampedPacket(pkt, source_ts=tss[0], arrival_ts=None)
            elif ts_mode == 2:
                yield TimestampedPacket(pkt, source_ts=None, arrival_ts=tss[0])
            elif ts_mode == 3:
                yield TimestampedPacket(pkt, source_ts=tss[0], arrival_ts=tss[1])
            else:
                raise ValueError(f"ts_mode={ts_mode} out of range [0..3]")

        buf.clear()


__all__ = [
    # Public API
    "parse", "parse_stream",
    "TimestampedPacket",
    "MONBUS_PKT_WIDTH", "MONBUS_TS_WIDTH",
    # Standalone parser
    "MonitorPacket",
    # Enums
    "ProtocolType", "PktType",
    "ARBErrorCode", "ARBTimeoutCode", "ARBCompletionCode",
    "ARBThresholdCode", "ARBPerformanceCode", "ARBDebugCode",
    "AXIErrorCode", "AXITimeoutCode", "AXICompletionCode",
    "AXIThresholdCode", "AXIPerformanceCode", "AXIAddrMatchCode",
    "AXIDebugCode",
    "APBErrorCode", "APBTimeoutCode", "APBCompletionCode",
    "APBThresholdCode", "APBPerformanceCode", "APBDebugCode",
    "AXISErrorCode", "AXISTimeoutCode", "AXISCompletionCode",
    "AXISCreditCode", "AXISChannelCode", "AXISStreamCode",
    # Raw accessors
    "get_packet_type", "get_protocol", "get_event_code",
    "get_channel_id", "get_unit_id", "get_agent_id", "get_event_data",
    "get_reserved",
    "create_monitor_packet",
    # Name lookups
    "get_protocol_name", "get_packet_type_name", "get_event_code_name",
    "get_event_code_enum",
    # Validation
    "is_valid_protocol_type", "is_valid_packet_type",
    "is_valid_event_code", "validate_monitor_packet",
    # Debug helpers
    "debug_packet_bits", "format_packet_fields",
]
