"""Tests for the monbus sniffer's file I/O (dump + reload).

The live cocotb-driven sampling loop is exercised by the stream
integration tests (any test that imports MonbusSniffer); this file
just confirms the on-disk format round-trips bit-exactly so that an
FPGA-side capture and a sim-side capture can be analysed by the same
tooling.
"""

from __future__ import annotations

import json
import os
import sys
import tempfile

# Make the package importable when running pytest from this dir.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))))))

from TBClasses.monbus.sniffer import MonbusSniffer, load_capture


def _make_sniffer_with_records(records):
    """Build a sniffer with a pre-populated record list — no cocotb needed."""
    s = MonbusSniffer.__new__(MonbusSniffer)
    s.records = list(records)
    s.label = "test"
    return s


def test_dump_and_load_json_round_trip():
    records = [
        (0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210, 0x1111_2222_3333_4444),
        (0xAAAA_BBBB_CCCC_DDDD_EEEE_FFFF_0000_1111, 0x5555_6666_7777_8888),
        (0x0000_0000_0000_0001_0000_0000_0000_0002, 0x0000_0000_0000_0009),
    ]
    s = _make_sniffer_with_records(records)
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
        path = f.name
    try:
        s.dump_json(path, extra_meta={"test_name": "dump_round_trip"})
        loaded = load_capture(path)
        assert loaded == records

        with open(path) as f:
            doc = json.load(f)
        assert doc["meta"]["record_count"] == len(records)
        assert doc["meta"]["test_name"] == "dump_round_trip"
        assert doc["meta"]["label"] == "test"
    finally:
        os.unlink(path)


def test_dump_and_load_csv_round_trip():
    records = [
        (0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210, 0x1111_2222_3333_4444),
        (0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF),
    ]
    s = _make_sniffer_with_records(records)
    with tempfile.NamedTemporaryFile(suffix=".csv", delete=False) as f:
        path = f.name
    try:
        s.dump_csv(path)
        loaded = load_capture(path)
        assert loaded == records
    finally:
        os.unlink(path)


def test_empty_capture_round_trips():
    s = _make_sniffer_with_records([])
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
        path = f.name
    try:
        s.dump_json(path)
        assert load_capture(path) == []
    finally:
        os.unlink(path)


def test_loader_rejects_unknown_extension():
    import pytest
    with tempfile.NamedTemporaryFile(suffix=".bin", delete=False) as f:
        path = f.name
    try:
        with pytest.raises(ValueError, match="unknown capture extension"):
            load_capture(path)
    finally:
        os.unlink(path)


def test_sniffer_count_reflects_records():
    s = _make_sniffer_with_records([(1, 2), (3, 4), (5, 6)])
    assert s.count == 3


def test_round_trip_feeds_compressor():
    """End-to-end: dump → load → encode → decode → records match.

    Uses create_monitor_packet to build well-formed packets (reserved
    bits zero, per spec). The compressor only preserves spec-conformant
    packets exactly — reserved bits in arbitrary 128-bit values are
    dropped by the template-based reconstruction.
    """
    from TBClasses.monbus import (
        create_monitor_packet, PktType, ProtocolType, AXIErrorCode,
    )
    from TBClasses.monbus.monbus_compressor import Encoder, Decoder

    pkt = create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, 2, 2, 0x21, 0xCAFE,
    )
    # Same packet emitted twice with monotonic timestamps — encoder
    # should compress the second one.
    records = [(pkt, 100), (pkt, 110)]
    s = _make_sniffer_with_records(records)
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
        path = f.name
    try:
        s.dump_json(path)
        loaded = load_capture(path)

        enc = Encoder()
        dec = Decoder()
        slots = list(enc.encode(loaded))
        out = list(dec.decode(slots))
        assert out == loaded
        # Second packet should be a Tier-1 hit.
        assert enc.stats.tier1_hits == 1
    finally:
        os.unlink(path)
