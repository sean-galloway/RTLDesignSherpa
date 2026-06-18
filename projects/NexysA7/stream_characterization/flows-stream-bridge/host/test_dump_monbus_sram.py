# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Unit tests for dump_monbus_sram.py.

import io
import os
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

_repo_root = HERE.parents[4]
sys.path.insert(0, str(_repo_root / "bin"))
sys.path.insert(0, str(_repo_root / "projects/components/converters/bin"))
os.environ.setdefault("REPO_ROOT", str(_repo_root))

from dump_monbus_sram import (  # noqa: E402
    RECORD_BYTES,
    words32_to_words64,
    read_sram_region,
    parse_records,
    format_timestamped,
    dump,
)
from TBClasses.monbus import (  # noqa: E402
    create_monitor_packet,
    PktType,
    ProtocolType,
    AXIErrorCode,
    AXIPerformanceCode,
    TimestampedPacket,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _record_words(raw_pkt, source_ts=0):
    """Serialize one record into 32-bit words exactly as
    monbus_axil_axil_group's m_axil master writes them to memory.
    Layout is fixed at 3 × 64-bit beats in TS, HI, LO order:
    {tag,source_ts[59:0]}, packet[127:64], packet[63:0] -- matching
    parse_stream(ts_mode=1) and the monitor package spec."""
    beats = [
        source_ts & ((1 << 64) - 1),          # beat0: {tag, source_ts[59:0]}
        (raw_pkt >> 64) & ((1 << 64) - 1),     # beat1: packet[127:64]
        raw_pkt & ((1 << 64) - 1),             # beat2: packet[63:0]
    ]
    out = []
    for b in beats:
        out.extend([b & 0xFFFF_FFFF, (b >> 32) & 0xFFFF_FFFF])
    return out


def _axi_err_packet(event_code=AXIErrorCode.AXI_ERR_RESP_SLVERR,
                    unit_id=2, agent_id=1, event_data=0xDEAD_BEEF):
    return create_monitor_packet(
        packet_type=PktType.PktTypeError,
        protocol=ProtocolType.PROTOCOL_AXI,
        event_code=event_code,
        channel_id=0,
        unit_id=unit_id,
        agent_id=agent_id,
        event_data=event_data,
    )


class CannedReader:
    def __init__(self, words):
        self.words = list(words)
        self.addrs = []
        self.idx = 0
    def __call__(self, addr):
        self.addrs.append(addr)
        if self.idx >= len(self.words):
            return None
        v = self.words[self.idx]
        self.idx += 1
        return v


class MockBridge:
    def __init__(self, words):
        self._reader = CannedReader(words)
    def read(self, addr):
        return self._reader(addr)


# ---------------------------------------------------------------------------
# words32_to_words64
# ---------------------------------------------------------------------------

def test_words32_to_words64_little_endian():
    assert words32_to_words64(
        [0xDEAD_BEEF, 0xCAFE_F00D, 0x1111_2222, 0x3333_4444]
    ) == [0xCAFE_F00D_DEAD_BEEF, 0x3333_4444_1111_2222]


def test_words32_to_words64_rejects_odd_count():
    with pytest.raises(ValueError):
        words32_to_words64([1, 2, 3])


# ---------------------------------------------------------------------------
# read_sram_region
# ---------------------------------------------------------------------------

def test_read_sram_region_returns_words_in_address_order():
    reader = CannedReader([0xAAAA_AAAA, 0xBBBB_BBBB, 0xCCCC_CCCC])
    words = read_sram_region(reader, base_addr=0x0004_0000, n_bytes=12)
    assert words == [0xAAAA_AAAA, 0xBBBB_BBBB, 0xCCCC_CCCC]
    assert reader.addrs == [0x0004_0000, 0x0004_0004, 0x0004_0008]


def test_read_sram_region_rejects_non_multiple_of_4():
    with pytest.raises(ValueError):
        read_sram_region(CannedReader([]), base_addr=0, n_bytes=15)


def test_read_sram_region_raises_on_short_read():
    # Reader runs out before n_bytes worth of words requested.
    reader = CannedReader([0xAAAA, 0xBBBB])
    with pytest.raises(IOError):
        read_sram_region(reader, base_addr=0, n_bytes=12)  # asks for 3 words


# ---------------------------------------------------------------------------
# parse_records -- always 3-beat / 24-byte records
# ---------------------------------------------------------------------------

def test_parse_records_extracts_packet_and_ts():
    raw = _axi_err_packet()
    words = _record_words(raw, source_ts=0x5678)
    recs = parse_records(words)
    assert len(recs) == 1
    rec = recs[0]
    assert isinstance(rec, TimestampedPacket)
    assert rec.packet.raw_packet == raw
    assert rec.source_ts == 0x5678


def test_parse_records_skips_zero_padding():
    raw = _axi_err_packet()
    # Memory layout: one all-zero 24-byte slot, then a real record.
    words = [0] * 6 + _record_words(raw, source_ts=0xAA)
    recs = parse_records(words)
    assert len(recs) == 1
    assert recs[0].packet.raw_packet == raw
    assert recs[0].source_ts == 0xAA


# ---------------------------------------------------------------------------
# format_timestamped
# ---------------------------------------------------------------------------

def test_format_timestamped_renders_event_and_ts():
    raw = _axi_err_packet()
    rec = parse_records(_record_words(raw, source_ts=0x100))[0]
    line = format_timestamped(rec)
    assert "AXI_ERR_RESP_SLVERR" in line


# ---------------------------------------------------------------------------
# dump() end-to-end through a mock bridge
# ---------------------------------------------------------------------------

def test_dump_emits_one_line_per_record():
    raw0 = _axi_err_packet(event_data=0xDEADBEEF)
    raw1 = create_monitor_packet(
        packet_type=PktType.PktTypePerf,
        protocol=ProtocolType.PROTOCOL_AXI,
        event_code=AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY,
        channel_id=0,
        unit_id=1,
        agent_id=0x10,
        event_data=0x42,
    )
    words = (
        _record_words(raw0, source_ts=0x100)
        + _record_words(raw1, source_ts=0x200)
    )
    bridge = MockBridge(words)
    out = io.StringIO()
    n = dump(bridge,
             base_addr=0x0004_0000,
             n_bytes=len(words) * 4,
             out=out)
    assert n == 2
    lines = out.getvalue().strip().splitlines()
    assert len(lines) == 2
    assert "AXI_ERR_RESP_SLVERR" in lines[0]
    assert "AXI_PERF_TOTAL_LATENCY" in lines[1]


def test_record_geometry_is_24_bytes():
    assert RECORD_BYTES == 24
