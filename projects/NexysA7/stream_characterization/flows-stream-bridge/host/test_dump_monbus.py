# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Unit tests for dump_monbus.py. Pure pytest, no UART hardware.
#
# Exercises words32_to_beats64, beats_to_packet, read_one_record (via a
# canned reader callable), and the drain_loop end-to-end against a
# scripted bridge mock.

import io
import os
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

# dump_monbus.py imports from bin/TBClasses; mirror that here so the
# imports resolve when pytest runs from anywhere.
_repo_root = HERE.parents[4]  # repo/projects/NexysA7/stream_characterization/flows-stream-bridge/host
sys.path.insert(0, str(_repo_root / "bin"))
sys.path.insert(0, str(_repo_root / "projects/components/converters/bin"))
os.environ.setdefault("REPO_ROOT", str(_repo_root))

from dump_monbus import (  # noqa: E402
    BEATS_PER_RECORD,
    WORDS_PER_RECORD,
    words32_to_beats64,
    beats_to_packet,
    read_one_record,
    format_record,
    drain_loop,
)
from TBClasses.monbus import (  # noqa: E402
    create_monitor_packet,
    parse,
    PktType,
    ProtocolType,
    AXIErrorCode,
    AXIPerformanceCode,
)


# ---------------------------------------------------------------------------
# words32_to_beats64
# ---------------------------------------------------------------------------

def test_words32_to_beats64_pairs_little_endian():
    """Pack pairs of 32-bit words into 64-bit beats. Low 32 bits first."""
    words = [0xDEAD_BEEF, 0xCAFE_F00D, 0x1111_2222, 0x3333_4444]
    beats = words32_to_beats64(words)
    assert len(beats) == 2
    assert beats[0] == 0xCAFE_F00D_DEAD_BEEF
    assert beats[1] == 0x3333_4444_1111_2222


def test_words32_to_beats64_truncates_high_bits():
    """32-bit overflow on input doesn't bleed across beats."""
    beats = words32_to_beats64([0x1_DEAD_BEEF, 0x1_CAFE_F00D])
    assert beats == [0xCAFE_F00D_DEAD_BEEF]


def test_words32_to_beats64_rejects_odd_count():
    with pytest.raises(ValueError):
        words32_to_beats64([1, 2, 3])


# ---------------------------------------------------------------------------
# beats_to_packet
# ---------------------------------------------------------------------------

def _make_axi_error_record(event_code=AXIErrorCode.AXI_ERR_RESP_SLVERR,
                           unit_id=2, agent_id=0x01, channel_id=3,
                           event_data=0xDEAD_BEEF_CAFE_F00D,
                           source_ts=0x0234_5678_9ABC_DEF0):
    # source_ts is 60-bit (drain beat 0 is {tag[3:0], source_ts[59:0]}).
    raw = create_monitor_packet(
        packet_type=PktType.PktTypeError,
        protocol=ProtocolType.PROTOCOL_AXI,
        event_code=event_code,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        event_data=event_data,
    )
    beat_lo = raw & ((1 << 64) - 1)
    beat_hi = (raw >> 64) & ((1 << 64) - 1)
    # TS, HI, LO -- matches the monbus_axil_axil_group slicer / spec.
    return raw, [source_ts, beat_hi, beat_lo]


def test_beats_to_packet_axi_error_round_trip():
    raw, beats = _make_axi_error_record()
    pkt, source_ts = beats_to_packet(beats)
    assert pkt.raw_packet == raw
    assert pkt.get_event_code_name() == "AXI_ERR_RESP_SLVERR"
    assert pkt.unit_id == 2
    assert pkt.agent_id == 0x01
    assert source_ts == 0x0234_5678_9ABC_DEF0


def test_beats_to_packet_rejects_wrong_count():
    with pytest.raises(ValueError):
        beats_to_packet([0, 0])
    with pytest.raises(ValueError):
        beats_to_packet([0, 0, 0, 0])


# ---------------------------------------------------------------------------
# read_one_record -- via a canned reader callable
# ---------------------------------------------------------------------------

class CannedReader:
    """Mock for uart_axi_bridge.read(addr). Returns the next 32-bit
    word from `script`, regardless of address (so the test doesn't have
    to model the SoC's address decode). Records every address it saw
    in `addrs` for assertions."""

    def __init__(self, script):
        self.script = list(script)
        self.addrs = []

    def __call__(self, addr):
        self.addrs.append(addr)
        if not self.script:
            return None
        return self.script.pop(0)


def _record_to_words32(raw_pkt, source_ts):
    """Inverse of words32_to_beats64 + beats_to_packet: produce the
    six 32-bit words a fake UART would return for one record, in the
    slicer's TS, HI, LO beat order (low 32 bits of each beat first)."""
    beat0 = source_ts & ((1 << 64) - 1)            # TS
    beat1 = (raw_pkt >> 64) & ((1 << 64) - 1)      # HI = packet[127:64]
    beat2 = raw_pkt & ((1 << 64) - 1)              # LO = packet[63:0]
    return [
        beat0 & 0xFFFF_FFFF, (beat0 >> 32) & 0xFFFF_FFFF,
        beat1 & 0xFFFF_FFFF, (beat1 >> 32) & 0xFFFF_FFFF,
        beat2 & 0xFFFF_FFFF, (beat2 >> 32) & 0xFFFF_FFFF,
    ]


def test_read_one_record_default_stride_increments_addresses():
    raw, _ = _make_axi_error_record()
    words = _record_to_words32(raw, 0x0234_5678_9ABC_DEF0)
    reader = CannedReader(words)
    pkt, ts = read_one_record(reader, base_addr=0xC000_0000, word_stride=4)
    assert pkt.raw_packet == raw
    assert ts == 0x0234_5678_9ABC_DEF0
    # 6 reads at incrementing 32-bit offsets
    assert reader.addrs == [0xC000_0000 + 4 * i for i in range(6)]


def test_read_one_record_zero_stride_targets_same_address():
    raw, _ = _make_axi_error_record(
        event_code=AXIErrorCode.AXI_ERR_ADDR_RANGE,
        event_data=0xDEAD_BEEF_DEAD_BEEF,
        source_ts=0x42,
    )
    words = _record_to_words32(raw, 0x42)
    reader = CannedReader(words)
    pkt, ts = read_one_record(reader, base_addr=0xC000_0000, word_stride=0)
    assert pkt.get_event_code_name() == "AXI_ERR_ADDR_RANGE"
    assert ts == 0x42
    # All 6 reads at the same base address
    assert reader.addrs == [0xC000_0000] * 6


def test_read_one_record_rejects_invalid_stride():
    with pytest.raises(ValueError):
        read_one_record(CannedReader([]), base_addr=0, word_stride=8)


def test_read_one_record_raises_on_none():
    reader = CannedReader([0, 0, 0, 0, 0, None])
    with pytest.raises(IOError):
        read_one_record(reader, base_addr=0, word_stride=4)


# ---------------------------------------------------------------------------
# format_record
# ---------------------------------------------------------------------------

def test_format_record_includes_timestamp_and_decoded_fields():
    raw, _ = _make_axi_error_record()
    pkt, ts = beats_to_packet(_make_axi_error_record()[1])
    line = format_record(pkt, ts)
    assert "AXI_ERR_RESP_SLVERR" in line
    assert "PROTOCOL_AXI" in line
    assert "PktTypeError" in line
    assert f"0x{ts:016x}" in line
    assert "Agent:01" in line
    assert "Unit:2" in line


# ---------------------------------------------------------------------------
# drain_loop -- end-to-end via mock bridge
# ---------------------------------------------------------------------------

class MockBridge:
    """Anything with a .read(addr) method satisfies drain_loop. Pull
    32-bit words sequentially from the scripted stream."""
    def __init__(self, script):
        self.reader = CannedReader(script)
    def read(self, addr):
        return self.reader(addr)


def test_drain_loop_two_records_finite_count():
    raw_err, _ = _make_axi_error_record(source_ts=0x100)
    raw_perf = create_monitor_packet(
        packet_type=PktType.PktTypePerf,
        protocol=ProtocolType.PROTOCOL_AXI,
        event_code=AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY,
        channel_id=0,
        unit_id=1,
        agent_id=0x10,
        event_data=0x42,
    )
    words = (
        _record_to_words32(raw_err, 0x100)
        + _record_to_words32(raw_perf, 0x200)
    )
    bridge = MockBridge(words)
    out = io.StringIO()
    drained = drain_loop(
        bridge,
        base_addr=0xC000_0000,
        word_stride=4,
        count=2,
        follow=False,
        poll_interval=0,
        out=out,
    )
    assert drained == 2
    lines = out.getvalue().strip().splitlines()
    assert len(lines) == 2
    assert "AXI_ERR_RESP_SLVERR" in lines[0]
    assert "@0x0000000000000100" in lines[0]
    assert "AXI_PERF_TOTAL_LATENCY" in lines[1]
    assert "@0x0000000000000200" in lines[1]


def test_drain_loop_stops_on_empty_fifo_when_not_following():
    """When the bridge returns an all-zero record (slicer driving zeros
    because the FIFO is empty) and we're not in --follow mode, the
    drain loop must stop cleanly without printing a bogus
    'PROTOCOL_AXI PktTypeError event_code=0' line."""
    bridge = MockBridge([0] * WORDS_PER_RECORD)
    out = io.StringIO()
    drained = drain_loop(
        bridge,
        base_addr=0xC000_0000,
        word_stride=4,
        count=None,
        follow=False,
        poll_interval=0,
        out=out,
    )
    assert drained == 0
    assert out.getvalue() == ""


def test_drain_loop_follows_past_empty_to_real_record():
    """With --follow, an empty FIFO snapshot doesn't terminate the
    drain -- the loop polls again and picks up the next real packet
    when it arrives."""
    raw_err, _ = _make_axi_error_record(source_ts=0x77)
    words = (
        [0] * WORDS_PER_RECORD                  # one empty snapshot
        + _record_to_words32(raw_err, 0x77)     # then a real packet
    )
    bridge = MockBridge(words)
    out = io.StringIO()
    drained = drain_loop(
        bridge,
        base_addr=0xC000_0000,
        word_stride=4,
        count=1,
        follow=True,
        poll_interval=0,
        out=out,
    )
    assert drained == 1
    lines = out.getvalue().strip().splitlines()
    assert len(lines) == 1
    assert "@0x0000000000000077" in lines[0]
    assert "AXI_ERR_RESP_SLVERR" in lines[0]
