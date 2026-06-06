"""Tests for the monbus compressor / decompressor / reporter model.

Validates that the Encoder + Decoder are bit-exact mirrors, that the
format selector picks the smallest fitting Tier-1 sub-format, that
the CAM behaves as LRU under both insertion and hit, and that the
statistics reporter counts correctly on hand-crafted streams.
"""

from __future__ import annotations

import sys
import os

# Make the package importable when running pytest from the tests dir.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))))))

from TBClasses.monbus import (
    create_monitor_packet, PktType, ProtocolType, AXIErrorCode,
    AXIPerformanceCode, AXICompletionCode,
)
from TBClasses.monbus.monbus_compressor import (
    Cam, Encoder, Decoder, CompressorStats, EscapeReason,
    TemplateKey, format_report,
    TAG_RAW, TAG_FORMAT_A, TAG_FORMAT_B, TAG_FORMAT_C,
    DELTA_TS_A, DELTA_TS_B, EVENT_DATA_A, EVENT_DATA_B,
    EVENT_DATA_C_DELTA,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _err_packet(agent=0x21, event_data=0xCAFE, channel=2):
    """Build a canonical PktTypeError AXI packet."""
    return create_monitor_packet(
        PktType.PktTypeError, ProtocolType.PROTOCOL_AXI,
        AXIErrorCode.AXI_ERR_DATA_ORPHAN, channel, 2, agent, event_data,
    )


def _perf_packet(agent=0x11, event_data=0x42, channel=0):
    return create_monitor_packet(
        PktType.PktTypePerf, ProtocolType.PROTOCOL_AXI,
        AXIPerformanceCode.AXI_PERF_TOTAL_LATENCY, channel, 1, agent, event_data,
    )


def _compl_packet(agent=0x31, event_data=0x10, channel=1):
    return create_monitor_packet(
        PktType.PktTypeCompletion, ProtocolType.PROTOCOL_AXI,
        AXICompletionCode.AXI_COMPL_WRITE_COMPLETE, channel, 2, agent, event_data,
    )


def _round_trip(records):
    """Encode then decode, return the decoded list."""
    enc = Encoder()
    dec = Decoder()
    slots = list(enc.encode(records))
    return list(dec.decode(slots)), enc, slots


# ---------------------------------------------------------------------------
# Cam class basics
# ---------------------------------------------------------------------------

def test_cam_install_and_lookup():
    cam = Cam(size=4)
    k = TemplateKey(0, 0, 0x0D, 2, 0x21, 1)
    assert cam.lookup(k) is None
    cam.install(k, event_data=0xDEAD)
    idx = cam.lookup(k)
    assert idx == 0
    assert cam.entries[0].last_event_data == 0xDEAD


def test_cam_lru_move_to_front_on_hit():
    cam = Cam(size=4)
    k1 = TemplateKey(0, 0, 0x01, 0, 0x10, 1)
    k2 = TemplateKey(0, 0, 0x02, 0, 0x20, 1)
    cam.install(k1, 0x100)
    cam.install(k2, 0x200)
    # k2 was most recently installed, so it's at the head.
    assert cam.entries[0].key == k2
    # Hitting k1 moves it to the head.
    cam.lookup(k1)
    assert cam.entries[0].key == k1
    assert cam.entries[1].key == k2


def test_cam_evicts_lru_on_overflow():
    cam = Cam(size=2)
    k1 = TemplateKey(0, 0, 0x01, 0, 0x10, 1)
    k2 = TemplateKey(0, 0, 0x02, 0, 0x20, 1)
    k3 = TemplateKey(0, 0, 0x03, 0, 0x30, 1)
    cam.install(k1, 0x100)
    cam.install(k2, 0x200)
    cam.install(k3, 0x300)   # k1 evicted (LRU)
    assert cam.lookup(k1) is None
    assert cam.lookup(k2) is not None
    assert cam.lookup(k3) is not None


# ---------------------------------------------------------------------------
# Encoder format dispatch
# ---------------------------------------------------------------------------

def test_first_packet_is_always_raw_escape():
    """Cold CAM → CAM miss → Tier-0 escape (3 beats)."""
    enc = Encoder()
    slots = enc.encode_one(_err_packet(), timestamp=100)
    assert len(slots) == 3
    assert (slots[0] >> 60) == TAG_RAW
    assert enc.stats.tier0_escapes == 1
    assert enc.stats.tier1_hits == 0
    assert enc.stats.escape_reasons[EscapeReason.CAM_MISS] == 1


def test_second_identical_packet_hits_format_a():
    """Second packet hits CAM, small delta_ts, small event_data → format A."""
    enc = Encoder()
    enc.encode_one(_err_packet(), timestamp=100)
    slots = enc.encode_one(_err_packet(), timestamp=110)
    assert len(slots) == 1
    assert (slots[0] >> 60) == TAG_FORMAT_A
    assert enc.stats.tier1_a_hits == 1


def test_large_delta_ts_dispatches_to_format_b():
    """delta_ts > 64K but event_data fits 32 bits → format B."""
    enc = Encoder()
    enc.encode_one(_err_packet(), timestamp=0)
    slots = enc.encode_one(_err_packet(), timestamp=200_000)  # > 2^16
    assert len(slots) == 1
    assert (slots[0] >> 60) == TAG_FORMAT_B
    assert enc.stats.tier1_b_hits == 1


def test_event_data_overflow_escapes_to_raw():
    """event_data > 40 bits, delta_ts < 16M, no compact format works for
    novel addresses without a delta — encoder falls back to raw."""
    enc = Encoder()
    # Use a 64-bit event_data that doesn't fit 32 bits either.
    # First packet seeds the CAM (cold-CAM escape: tier0 #1).
    pkt_seed = _err_packet(event_data=0x1234)
    pkt_big  = _err_packet(event_data=(1 << 50))   # too big for A or B
    enc.encode_one(pkt_seed, timestamp=0)
    slots = enc.encode_one(pkt_big, timestamp=10)
    # Format C might salvage this with a 40-bit signed delta, but
    # (1<<50) - 0x1234 ≈ 1<<50 which exceeds 2^39 too, so escape.
    assert len(slots) == 3
    assert (slots[0] >> 60) == TAG_RAW
    # Two escapes total: the cold-CAM seed, then the overflow on the
    # second packet. The second escape's reason is event_data_overflow.
    assert enc.stats.tier0_escapes == 2
    assert enc.stats.escape_reasons[EscapeReason.CAM_MISS] == 1
    assert enc.stats.escape_reasons[EscapeReason.EVENT_DATA_OVF] == 1


def test_event_data_delta_picks_format_c_for_sequential_counter():
    """event_data goes 0x1000 → 0x1004 → 0x1008 (4-byte stride).
    Absolute fits format A every time, so the encoder picks A first; format
    C is only chosen when A and B both fail to fit. Confirm format A is
    used (the encoder's priority order)."""
    enc = Encoder()
    enc.encode_one(_perf_packet(event_data=0x1000), timestamp=0)
    enc.encode_one(_perf_packet(event_data=0x1004), timestamp=10)
    enc.encode_one(_perf_packet(event_data=0x1008), timestamp=20)
    # All three: first is raw (cold CAM), next two are format A (small ed).
    assert enc.stats.tier1_a_hits == 2
    assert enc.stats.tier1_c_hits == 0


def test_format_c_engaged_when_a_and_b_fail():
    """Build a case where event_data is too big for A and B but delta is small."""
    enc = Encoder()
    # Seed CAM with event_data 0xBEEF_CAFE_DEAD_F00D (64-bit).
    seed_ed = 0xBEEF_CAFE_DEAD_F00D
    enc.encode_one(_perf_packet(event_data=seed_ed), timestamp=0)
    # Next packet: same template, event_data differs by +0x10.
    # Absolute event_data is 64 bits (doesn't fit A's 40 bits or B's 32 bits).
    # But delta is +0x10 which fits in format C's signed 40-bit field.
    slots = enc.encode_one(_perf_packet(event_data=seed_ed + 0x10), timestamp=5)
    assert len(slots) == 1
    assert (slots[0] >> 60) == TAG_FORMAT_C
    assert enc.stats.tier1_c_hits == 1


# ---------------------------------------------------------------------------
# Round-trip correctness (encoder + decoder = identity)
# ---------------------------------------------------------------------------

def test_round_trip_single_packet():
    pkt = _err_packet()
    records = [(pkt, 100)]
    out, _enc, _slots = _round_trip(records)
    assert out == [(pkt, 100)]


def test_round_trip_three_identical_packets():
    pkt = _err_packet()
    records = [(pkt, 100), (pkt, 110), (pkt, 125)]
    out, enc, _ = _round_trip(records)
    assert out == records
    # 1 raw + 2 Tier-1 = 3 + 2 = 5 slots
    assert enc.stats.slots_emitted == 5


def test_round_trip_mixed_packet_types():
    p1 = _err_packet()
    p2 = _perf_packet()
    p3 = _compl_packet()
    records = [
        (p1, 100),  # cold → raw
        (p2, 110),  # cold → raw
        (p1, 120),  # hit  → tier-1
        (p3, 130),  # cold → raw
        (p2, 140),  # hit  → tier-1
        (p1, 150),  # hit  → tier-1
    ]
    out, enc, _ = _round_trip(records)
    assert out == records
    assert enc.stats.tier0_escapes == 3
    assert enc.stats.tier1_hits == 3


def test_round_trip_with_format_b():
    pkt = _err_packet()
    records = [
        (pkt, 0),
        (pkt, 100_000),     # delta > 2^16 → format B
        (pkt, 100_005),     # delta = 5 → format A
    ]
    out, enc, _ = _round_trip(records)
    assert out == records
    assert enc.stats.tier1_b_hits == 1
    assert enc.stats.tier1_a_hits == 1


def test_round_trip_with_format_c():
    """Build a stream where some records take format C."""
    seed_ed = 0xBEEF_CAFE_DEAD_F00D
    pkt0 = _perf_packet(event_data=seed_ed)
    pkt1 = _perf_packet(event_data=seed_ed + 0x10)
    pkt2 = _perf_packet(event_data=seed_ed + 0x20)
    records = [(pkt0, 0), (pkt1, 5), (pkt2, 10)]
    out, enc, _ = _round_trip(records)
    assert out == records
    assert enc.stats.tier1_c_hits == 2


def test_round_trip_with_eviction():
    """Force CAM eviction by using more unique templates than CAM size."""
    enc = Encoder(cam_size=4)
    dec = Decoder(cam_size=4)

    records = []
    # 6 unique templates → 4 fit, last 2 evict 2 entries.
    for i in range(6):
        records.append((_err_packet(agent=0x10 + i), 100 + i))
    # Hit on the most-recent ones — should be format A.
    for i in range(2):
        records.append((_err_packet(agent=0x14 + i), 200 + i))

    slots = list(enc.encode(records))
    decoded = list(dec.decode(slots))
    assert decoded == records


def test_round_trip_long_random_stream():
    """100-record stream of mixed packet types."""
    import random
    random.seed(42)

    records = []
    agents = [0x10, 0x11, 0x12, 0x13, 0x20, 0x21]
    pkt_makers = [_err_packet, _perf_packet, _compl_packet]
    ts = 0
    for _ in range(100):
        agent = random.choice(agents)
        ed = random.randrange(0, 1 << 30)
        maker = random.choice(pkt_makers)
        records.append((maker(agent=agent, event_data=ed), ts))
        ts += random.randrange(1, 1000)

    out, enc, slots = _round_trip(records)
    assert out == records
    # Tier 1 should win the majority over a 100-record stream with 18
    # template tuples (3 makers × 6 agents) and a 16-entry CAM.
    assert enc.stats.tier1_hits > enc.stats.tier0_escapes


# ---------------------------------------------------------------------------
# Stats reporter
# ---------------------------------------------------------------------------

def test_stats_counts_match_manual_count():
    enc = Encoder()
    enc.encode_one(_err_packet(), 0)   # raw
    enc.encode_one(_err_packet(), 5)   # A
    enc.encode_one(_err_packet(), 200_000)  # B
    enc.encode_one(_perf_packet(), 200_005)  # raw (new template)

    s = enc.stats
    assert s.records_total == 4
    assert s.tier0_escapes == 2
    assert s.tier1_a_hits == 1
    assert s.tier1_b_hits == 1
    assert s.slots_emitted == 3 + 1 + 1 + 3
    assert s.bits_in == 4 * 192
    assert s.bits_out == 8 * 64


def test_compression_ratio_on_hot_stream():
    """1 cold + 99 hot identical packets → very high compression ratio."""
    enc = Encoder()
    pkt = _err_packet()
    enc.encode_one(pkt, 0)
    for i in range(1, 100):
        enc.encode_one(pkt, i * 10)
    # Total slots: 3 (cold) + 99 (hot) = 102. Records: 100.
    s = enc.stats
    assert s.slots_emitted == 102
    assert s.compression_ratio > 2.8  # 100*192 / (102*64) ≈ 2.94


def test_report_renders_clean_summary():
    enc = Encoder()
    enc.encode_one(_err_packet(), 0)
    enc.encode_one(_err_packet(), 5)
    enc.encode_one(_perf_packet(), 10)
    report = format_report(enc)
    assert "Records:" in report
    assert "Tier 1 hits:" in report
    assert "CAM final state" in report
    assert "Compression ratio:" in report


def test_report_handles_empty_stream():
    enc = Encoder()
    out = format_report(enc)
    assert "Records:" in out
    assert "(empty stream)" in out


# ---------------------------------------------------------------------------
# Boundary / edge cases
# ---------------------------------------------------------------------------

def test_delta_ts_exactly_at_format_a_boundary():
    """delta_ts = 2^16 - 1 fits format A; = 2^16 falls to B."""
    pkt = _err_packet()
    enc = Encoder()
    enc.encode_one(pkt, 0)
    slots = enc.encode_one(pkt, (1 << DELTA_TS_A) - 1)
    assert (slots[0] >> 60) == TAG_FORMAT_A
    enc.reset()
    enc.encode_one(pkt, 0)
    slots = enc.encode_one(pkt, 1 << DELTA_TS_A)
    assert (slots[0] >> 60) == TAG_FORMAT_B


def test_event_data_exactly_at_format_a_boundary():
    """event_data fits in 40 bits → A; doesn't → B (if it fits 32)
    or escape via C/raw."""
    enc = Encoder()
    # Seed.
    enc.encode_one(_err_packet(event_data=0), 0)
    # Just-fits-A:
    slots = enc.encode_one(_err_packet(event_data=(1 << EVENT_DATA_A) - 1), 5)
    assert (slots[0] >> 60) == TAG_FORMAT_A
    # Doesn't fit A (40 bits) but fits B (32 bits)? No — 1<<40 > 1<<32.
    # So jumps to format C (signed 40-bit delta).
    # event_data = (1 << EVENT_DATA_A) is exactly out of A's range,
    # and out of B (32 bits) too. Test that the encoder picks C if the
    # delta fits, else raw.
    enc.reset()
    enc.encode_one(_err_packet(event_data=0), 0)
    slots = enc.encode_one(_err_packet(event_data=1 << EVENT_DATA_A), 5)
    # delta = 1<<40 = 2^40, falls outside signed 40-bit range (-2^39..2^39-1)
    # → escape.
    assert (slots[0] >> 60) == TAG_RAW


def test_decoder_rejects_unknown_tag():
    """Tag 0x4..0xF are reserved; decoder raises."""
    import pytest
    dec = Decoder()
    bad_slot = (0x4 << 60) | 0x123
    with pytest.raises(ValueError, match="unknown tag"):
        list(dec.decode([bad_slot]))


def test_encoder_and_decoder_reset_cleanly():
    pkt = _err_packet()
    enc = Encoder()
    dec = Decoder()
    enc.encode_one(pkt, 0)
    enc.encode_one(pkt, 10)
    enc.reset()
    dec.reset()
    # After reset, the next packet must be a Tier-0 escape again.
    slots = enc.encode_one(pkt, 100)
    assert len(slots) == 3
    out = list(dec.decode(slots))
    assert out == [(pkt, 100)]
