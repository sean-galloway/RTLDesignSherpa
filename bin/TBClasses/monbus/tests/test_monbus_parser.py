# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Standalone unit tests for the monbus parser. No cocotb dependency --
# these run as plain pytest, and the test process imports nothing from
# the BFM-coupled side of bin/TBClasses/monbus/.

import sys
from pathlib import Path

import pytest

# Make `from TBClasses.monbus import ...` work without a global install.
HERE = Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[3]))  # repo/bin

from TBClasses.monbus import (  # noqa: E402
    parse, parse_stream, create_monitor_packet,
    MonitorPacket,
    ProtocolType, PktType,
    AXIErrorCode, AXITimeoutCode, AXICompletionCode,
    AXIPerformanceCode, AXIDebugCode,
    APBErrorCode, AXISErrorCode,
    ARBErrorCode,
    get_packet_type, get_protocol, get_event_code,
    get_channel_id, get_unit_id, get_agent_id, get_event_data,
    get_event_code_name, is_valid_event_code,
)


# ---------------------------------------------------------------------------
# Field-extraction helpers (work directly on raw 64-bit ints)
# ---------------------------------------------------------------------------

def test_field_widths_match_sv_packet_layout():
    """Verify the bit slices match monitor_common_pkg.sv exactly:
    [63:60] pkt_type, [59:57] protocol, [56:53] event_code,
    [52:47] channel_id, [46:43] unit_id, [42:35] agent_id,
    [34:0] event_data."""
    # Set every field to its max value -- catches off-by-one slice bugs.
    raw = create_monitor_packet(
        packet_type=0xF, protocol=0x7, event_code=0xF,
        channel_id=0x3F, unit_id=0xF, agent_id=0xFF,
        event_data=0x7FFFFFFFF,
    )
    assert get_packet_type(raw) == 0xF
    assert get_protocol(raw)    == 0x7
    assert get_event_code(raw)  == 0xF
    assert get_channel_id(raw)  == 0x3F
    assert get_unit_id(raw)     == 0xF
    assert get_agent_id(raw)    == 0xFF
    assert get_event_data(raw)  == 0x7FFFFFFFF


def test_field_widths_zero_packet():
    raw = create_monitor_packet(0, 0, 0, 0, 0, 0, 0)
    assert raw == 0
    p = parse(raw)
    assert p.packet_type == 0 and p.protocol == 0 and p.event_code == 0


def test_event_data_is_35_bits_not_36():
    """Regression: event_data is 35 bits ([34:0]), not 36. The 36-bit
    mask 0xFFFFFFFFF (= 2**36-1) would clobber agent_id's LSB."""
    # Set the bit just outside the event_data field; it must NOT
    # appear in event_data.
    raw = 1 << 35  # bit 35 belongs to agent_id, not event_data
    p = parse(raw)
    assert p.event_data == 0
    assert p.agent_id == 1


# ---------------------------------------------------------------------------
# MonitorPacket dataclass + parse() entry point
# ---------------------------------------------------------------------------

def test_parse_round_trip_axi_error():
    """Build an AXI ERROR packet via create_monitor_packet, parse it,
    and confirm every field round-trips."""
    raw = create_monitor_packet(
        packet_type=PktType.PktTypeError,
        protocol=ProtocolType.PROTOCOL_AXI,
        event_code=AXIErrorCode.AXI_ERR_RESP_SLVERR,
        channel_id=0x3,
        unit_id=2,
        agent_id=0x01,
        event_data=0xDEADBEEF,
    )
    p = parse(raw)
    assert p.packet_type == PktType.PktTypeError
    assert p.protocol == ProtocolType.PROTOCOL_AXI
    assert p.event_code == AXIErrorCode.AXI_ERR_RESP_SLVERR
    assert p.channel_id == 0x3
    assert p.unit_id == 2
    assert p.agent_id == 0x01
    assert p.event_data == 0xDEADBEEF
    assert p.raw_packet == raw
    assert p.to_raw() == raw


def test_event_code_zero_is_not_unknown():
    """Regression: every event-code group's first entry is value 0, and
    IntEnum members with value 0 are falsy under bool(). The name
    lookup must use `is not None`, not truthiness."""
    raw = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_RESP_SLVERR,  # value 0
        0, 0, 0, 0,
    )
    p = parse(raw)
    assert p.get_event_code_name() == "AXI_ERR_RESP_SLVERR"


@pytest.mark.parametrize("proto,pkt_type,code_enum,code_member", [
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeError,
     AXIErrorCode, AXIErrorCode.AXI_ERR_DATA_ORPHAN),
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeTimeout,
     AXITimeoutCode, AXITimeoutCode.AXI_TIMEOUT_RESP),
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeCompletion,
     AXICompletionCode, AXICompletionCode.AXI_COMPL_READ_COMPLETE),
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypePerf,
     AXIPerformanceCode, AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY),
    (ProtocolType.PROTOCOL_AXI,  PktType.PktTypeDebug,
     AXIDebugCode, AXIDebugCode.AXI_DEBUG_BACKPRESSURE),
    (ProtocolType.PROTOCOL_APB,  PktType.PktTypeError,
     APBErrorCode, APBErrorCode.APB_ERR_PSLVERR),
    (ProtocolType.PROTOCOL_AXIS, PktType.PktTypeError,
     AXISErrorCode, AXISErrorCode.AXIS_ERR_LAST_MISSING),
    (ProtocolType.PROTOCOL_ARB,  PktType.PktTypeError,
     ARBErrorCode, ARBErrorCode.ARB_ERR_STARVATION),
])
def test_event_code_name_lookup(proto, pkt_type, code_enum, code_member):
    raw = create_monitor_packet(pkt_type, proto, code_member, 0, 0, 0, 0)
    p = parse(raw)
    assert p.get_event_code_name() == code_member.name
    assert p.is_valid()
    assert is_valid_event_code(proto, pkt_type, code_member)


def test_unknown_event_code_returns_descriptive_string():
    """An invalid event code for a known (protocol, packet_type) pair
    should produce a fallback string, not raise."""
    # AXIS doesn't define a Threshold enum; any code under that
    # combo should fall back to UNKNOWN_EVENT_*.
    raw = create_monitor_packet(
        PktType.PktTypeThreshold, ProtocolType.PROTOCOL_AXIS,
        event_code=5, channel_id=0, unit_id=0, agent_id=0, event_data=0,
    )
    p = parse(raw)
    name = p.get_event_code_name()
    assert name.startswith("UNKNOWN_EVENT_"), name


# ---------------------------------------------------------------------------
# matches() filter helper
# ---------------------------------------------------------------------------

def test_matches_with_enum_or_int_argument():
    raw = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_RESP_SLVERR, 0, 2, 0x01, 0,
    )
    p = parse(raw)
    # Enum and raw-int forms must both match.
    assert p.matches(packet_type=PktType.PktTypeError)
    assert p.matches(packet_type=int(PktType.PktTypeError))
    assert p.matches(unit_id=2, agent_id=0x01)
    assert not p.matches(unit_id=1)


def test_matches_unknown_attribute_raises():
    p = parse(0)
    with pytest.raises(AttributeError):
        p.matches(totally_made_up=1)


# ---------------------------------------------------------------------------
# parse_stream: post-processing a memory dump of monbus packets
# ---------------------------------------------------------------------------

def test_parse_stream_filters_zero_padding():
    """The bridge's m_mon_axil writes packets into a 32-bit-word
    memory region; words that haven't been written yet remain 0. The
    stream parser must skip those rather than emit a flood of bogus
    PktTypeError/PROTOCOL_AXI/event_code=0 packets."""
    raw_err = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x10, 0xCAFE,
    )
    raw_perf = create_monitor_packet(
        PktType.PktTypePerf, ProtocolType.PROTOCOL_AXI,
        AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY, 0, 1, 0x00, 0x42,
    )
    stream = [0, 0, raw_err, 0, raw_perf, 0]
    parsed = list(parse_stream(stream))
    assert len(parsed) == 2
    assert parsed[0].get_event_code_name() == "AXI_ERR_DATA_ORPHAN"
    assert parsed[1].get_event_code_name() == "AXI_PERF_TOTAL_LATENCY"


# ---------------------------------------------------------------------------
# Bridge per-port identity round-trip
# ---------------------------------------------------------------------------

def test_bridge_unit_agent_id_decoding():
    """Stage 2 of the bridge generator assigns:
       UNIT_ID = 2 (master-side wrappers)
       UNIT_ID = 1 (slave-side wrappers)
       AGENT_ID = (port_idx << 4) | (1 if wr else 0)
    The parser must round-trip these so downstream tooling can map a
    packet back to which port_idx + channel emitted it."""
    # dma (master idx=1), wr channel -> UNIT_ID=2, AGENT_ID=0x11
    raw = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_RESP_SLVERR,
        channel_id=0, unit_id=2, agent_id=(1 << 4) | 1, event_data=0,
    )
    p = parse(raw)
    assert p.unit_id == 2
    port_idx = (p.agent_id >> 4) & 0xF
    is_wr   = bool(p.agent_id & 0x1)
    assert port_idx == 1
    assert is_wr is True
