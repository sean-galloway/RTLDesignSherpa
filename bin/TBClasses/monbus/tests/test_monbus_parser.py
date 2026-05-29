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
# Field-extraction helpers (work directly on raw 128-bit ints)
# ---------------------------------------------------------------------------

def test_field_widths_match_sv_packet_layout():
    """Verify the bit slices match monitor_common_pkg.sv exactly:
    [127:124] pkt_type, [123:109] reserved, [108:105] protocol,
    [104:97] event_code, [96:88] channel_id, [87:72] agent_id,
    [71:64] unit_id, [63:0] event_data."""
    # Set every field to its max value -- catches off-by-one slice bugs.
    raw = create_monitor_packet(
        packet_type=0xF, protocol=0xF, event_code=0xFF,
        channel_id=0x1FF, unit_id=0xFF, agent_id=0xFFFF,
        event_data=(1 << 64) - 1,
    )
    assert get_packet_type(raw) == 0xF
    assert get_protocol(raw)    == 0xF
    assert get_event_code(raw)  == 0xFF
    assert get_channel_id(raw)  == 0x1FF
    assert get_unit_id(raw)     == 0xFF
    assert get_agent_id(raw)    == 0xFFFF
    assert get_event_data(raw)  == (1 << 64) - 1


def test_field_widths_zero_packet():
    raw = create_monitor_packet(0, 0, 0, 0, 0, 0, 0)
    assert raw == 0
    p = parse(raw)
    assert p.packet_type == 0 and p.protocol == 0 and p.event_code == 0


def test_event_data_is_64_bits_now():
    """Regression: event_data is 64 bits ([63:0]) in the widened
    packet. The bit just above (bit 64) belongs to unit_id, not
    event_data."""
    raw = 1 << 64  # bit 64 belongs to unit_id, not event_data
    p = parse(raw)
    assert p.event_data == 0
    assert p.unit_id == 1


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

def _split128(raw: int):
    """Split a 128-bit packet into (lo64, hi64) — the order
    monbus_axil_group writes them to memory (low half first)."""
    return raw & ((1 << 64) - 1), (raw >> 64) & ((1 << 64) - 1)


def test_parse_stream_filters_zero_padding():
    """The bridge's m_mon_axil writes 128-bit packets in two 64-bit
    beats. Beats that haven't been written remain 0. The stream parser
    must skip all-zero records rather than emit bogus PktTypeError/
    PROTOCOL_AXI/event_code=0 packets."""
    raw_err = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x10, 0xCAFE,
    )
    raw_perf = create_monitor_packet(
        PktType.PktTypePerf, ProtocolType.PROTOCOL_AXI,
        AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY, 0, 1, 0x00, 0x42,
    )
    # Each record is 2 beats (lo, hi); intersperse a zero record.
    err_lo, err_hi = _split128(raw_err)
    perf_lo, perf_hi = _split128(raw_perf)
    stream = [0, 0,             # zero record  (skipped)
              err_lo, err_hi,    # error record
              0, 0,             # zero record  (skipped)
              perf_lo, perf_hi]  # perf record
    parsed = list(parse_stream(stream, stride_bytes=16, ts_mode=0))
    assert len(parsed) == 2
    assert parsed[0].get_event_code_name() == "AXI_ERR_DATA_ORPHAN"
    assert parsed[1].get_event_code_name() == "AXI_PERF_TOTAL_LATENCY"


def test_parse_stream_with_source_timestamp():
    """ts_mode=1: each record is packet + source_ts (3 beats, 24 B)."""
    raw_err = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x10, 0xCAFE,
    )
    lo, hi = _split128(raw_err)
    stream = [lo, hi, 0xDEADBEEF12345678]
    parsed = list(parse_stream(stream, stride_bytes=24, ts_mode=1))
    assert len(parsed) == 1
    rec = parsed[0]
    assert rec.packet.get_event_code_name() == "AXI_ERR_DATA_ORPHAN"
    assert rec.source_ts == 0xDEADBEEF12345678
    assert rec.arrival_ts is None


def test_parse_stream_with_both_timestamps():
    """ts_mode=3: packet + source_ts + arrival_ts (4 beats, 32 B)."""
    raw_err = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 0, 2, 0x10, 0xCAFE,
    )
    lo, hi = _split128(raw_err)
    stream = [lo, hi, 0x1111_2222_3333_4444, 0x5555_6666_7777_8888]
    parsed = list(parse_stream(stream, stride_bytes=32, ts_mode=3))
    assert len(parsed) == 1
    rec = parsed[0]
    assert rec.source_ts == 0x1111_2222_3333_4444
    assert rec.arrival_ts == 0x5555_6666_7777_8888


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
