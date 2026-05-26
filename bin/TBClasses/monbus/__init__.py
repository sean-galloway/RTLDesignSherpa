# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Public API for the monbus packet library.
#
# Two layers:
#   * Standalone parser (no cocotb dependency) -- use these in regular
#     Python scripts, log post-processors, or anywhere you have a raw
#     64-bit packet you want to decode:
#         from TBClasses.monbus import parse, MonitorPacket
#         pkt = parse(0x0042c08000123456)
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


def parse(raw_packet):
    """Top-level convenience: parse a raw 64-bit int into a MonitorPacket.

    >>> p = parse(0x0042c08000123456)
    >>> p.get_packet_type_name()
    'PktTypeError'
    """
    if not isinstance(raw_packet, int):
        raise TypeError(f"parse() expects int, got {type(raw_packet).__name__}")
    return MonitorPacket.from_raw(raw_packet & ((1 << 64) - 1))


def parse_stream(raw_packets):
    """Parse an iterable of raw 64-bit ints (e.g. a memory dump from the
    bridge's m_mon_axil master-write region) into MonitorPacket objects.
    Packets equal to 0 are skipped -- those are uninitialised SRAM /
    write-FIFO padding, not legitimate packets."""
    for raw in raw_packets:
        if raw == 0:
            continue
        yield parse(raw)


__all__ = [
    # Public API
    "parse", "parse_stream",
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
