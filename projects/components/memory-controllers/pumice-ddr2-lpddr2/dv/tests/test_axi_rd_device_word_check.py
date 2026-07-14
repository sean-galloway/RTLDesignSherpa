# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Unit test for the AXI read-data device-word ORDER assertion.

Pure-python (no simulator): feeds the assertion the EXACT on-silicon ILA values
(reports/ila_read_fixed.csv) to prove the contract checker localizes the real
x16 read de-interleave failure signatures. This is the assertion that the
existing beat-level golden compare (and the DFISlavePHY-ideal sims) did NOT
catch — the coverage gap that let the regression through.
"""
import os
import sys

_TB = os.path.join(os.path.dirname(__file__), "..", "tbclasses")
sys.path.insert(0, os.path.abspath(_TB))

from axi_rd_device_word_check import (           # noqa: E402
    check_beat_device_words, check_read_device_word_order, format_violations,
)

BEAT_BYTES = 8      # AXI_DATA_WIDTH=64 -> 8 bytes/beat
DEV_BYTES  = 2      # x16 device word = 16 bits

# golden = the write pattern captured clean on w_dfi_wrdata (ila_wr_fixed.csv).
# 64b beat = 4 x16 device-words, little-endian: slot k = bits [k*16 +: 16].
G_A = 0xa5a03f18a5a03f1c    # slots: [3f1c, a5a0, 3f18, a5a0]
G_B = 0xa5a03f00a5a03f04    # slots: [3f04, a5a0, 3f00, a5a0]


def test_clean_beat_passes():
    assert check_beat_device_words(0, G_A, G_A, BEAT_BYTES, DEV_BYTES) is None


def test_phase_duplication_localized():
    # on-board read returned 0xa5a03f1ca5a03f1c for golden G_A: slot2 got slot0's
    # value (phase1 <- phase0). The checker must pin slot 2 as a shift@0.
    actual = 0xa5a03f1ca5a03f1c
    v = check_beat_device_words(0x40, G_A, actual, BEAT_BYTES, DEV_BYTES)
    assert v is not None
    bad = {b["slot"]: b for b in v["bad_slots"]}
    assert set(bad) == {2}, v
    assert bad[2]["expected"] == "0x3f18" and bad[2]["actual"] == "0x3f1c"
    assert bad[2]["class"].startswith("shift@0"), bad[2]


def test_dropped_device_words_localized():
    # on-board read returned 0x000000000000a5a0 for golden G_B: slot0 got slot1's
    # value (shift), slots 1..3 dropped to zero.
    actual = 0x000000000000a5a0
    v = check_beat_device_words(0x0, G_B, actual, BEAT_BYTES, DEV_BYTES)
    assert v is not None
    bad = {b["slot"]: b for b in v["bad_slots"]}
    assert set(bad) == {0, 1, 2, 3}, v
    assert bad[0]["class"].startswith("shift@1"), bad[0]     # a5a0 == golden slot1
    for k in (1, 2, 3):
        assert bad[k]["class"].startswith("zero"), bad[k]


def test_batch_over_snoop_and_format():
    # mixed stream: one clean beat, two corrupted (the ILA signatures).
    snoop = [
        (0x00, G_B, 0),                       # clean
        (0x40, 0xa5a03f1ca5a03f1c, 0),        # phase dup
        (0x80, 0x000000000000a5a0, 1),        # dropped
    ]
    golden = {0x00: G_B, 0x40: G_A, 0x80: G_B}
    viol = check_read_device_word_order(
        snoop, lambda a, n: golden[a], BEAT_BYTES, DEV_BYTES)
    assert len(viol) == 2                      # the clean beat is not flagged
    text = format_violations(viol)
    assert "CONTRACT VIOLATED" in text and "shift@" in text and "zero" in text


def test_all_clean_returns_empty():
    snoop = [(0x00, G_A, 0), (0x08, G_B, 0)]
    golden = {0x00: G_A, 0x08: G_B}
    assert check_read_device_word_order(
        snoop, lambda a, n: golden[a], BEAT_BYTES, DEV_BYTES) == []
