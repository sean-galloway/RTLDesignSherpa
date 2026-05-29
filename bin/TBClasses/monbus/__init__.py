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


def parse_stream(raw_words, stride_bytes: int = 16, ts_mode: int = 0):
    """Parse a memory dump produced by monbus_axil_group.

    The capture region is written by a 64-bit AXIL master in fixed-size
    records. Use `stride_bytes` + `ts_mode` to describe the record shape:

      | stride | ts_mode | record contents                  |
      | ------ | ------- | -------------------------------- |
      |     16 |       0 | packet[127:0]                    |
      |     24 |       1 | packet, source_ts                |
      |     24 |       2 | packet, arrival_ts               |
      |     32 |       3 | packet, source_ts, arrival_ts    |

    `raw_words` is an iterable of 64-bit ints (each one AXIL beat).
    Yields `MonitorPacket` when ts_mode == 0, otherwise `TimestampedPacket`.

    Records whose packet body is all-zero are skipped (uninitialised
    SRAM / write-FIFO padding).
    """
    beats_per_record = stride_bytes // 8
    if beats_per_record not in (2, 3, 4):
        raise ValueError(f"unsupported stride_bytes={stride_bytes}")

    buf = []
    for word in raw_words:
        buf.append(word & ((1 << 64) - 1))
        if len(buf) < beats_per_record:
            continue

        # Reassemble 128-bit packet from low+high 64-bit beats.
        pkt_lo, pkt_hi = buf[0], buf[1]
        raw_pkt = (pkt_hi << 64) | pkt_lo
        if raw_pkt == 0:
            buf.clear()
            continue

        pkt = parse(raw_pkt)

        if ts_mode == 0:
            yield pkt
        elif ts_mode == 1:
            yield TimestampedPacket(pkt, source_ts=buf[2], arrival_ts=None)
        elif ts_mode == 2:
            yield TimestampedPacket(pkt, source_ts=None, arrival_ts=buf[2])
        elif ts_mode == 3:
            yield TimestampedPacket(pkt, source_ts=buf[2], arrival_ts=buf[3])
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
