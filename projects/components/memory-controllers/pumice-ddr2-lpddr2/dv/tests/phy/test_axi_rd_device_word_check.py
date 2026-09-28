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

import pytest

from TBClasses.shared.test_levels import level_env, reg_level_grid

_TB = os.path.join(os.path.dirname(__file__), "..", "..", "tbclasses")
sys.path.insert(0, os.path.abspath(_TB))

from axi_rd_device_word_check import (           # noqa: E402
    check_beat_device_words, check_read_device_word_order, format_violations,
)

# dv/ on sys.path so the area's depth profile resolves as `tbclasses.*`.
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_levels import depth as _profile_depth  # noqa: E402

BEAT_BYTES = 8      # AXI_DATA_WIDTH=64 -> 8 bytes/beat
DEV_BYTES  = 2      # x16 device word = 16 bits

# golden = the write pattern captured clean on w_dfi_wrdata (ila_wr_fixed.csv).
# 64b beat = 4 x16 device-words, little-endian: slot k = bits [k*16 +: 16].
G_A = 0xa5a03f18a5a03f1c    # slots: [3f1c, a5a0, 3f18, a5a0]
G_B = 0xa5a03f00a5a03f04    # slots: [3f04, a5a0, 3f00, a5a0]

# Every test carries the gate/func/full cell like a simulator wrapper does
# (tooling BUG-004). No simulator here, so the same level_env() entries go
# into THIS process's environment, where pumice_levels.depth() reads them.
pytestmark = pytest.mark.parametrize("test_level", reg_level_grid())


def _enter_level(monkeypatch, test_level):
    for k, v in level_env(test_level).items():
        monkeypatch.setenv(k, v)
    assert os.environ.get("TEST_LEVEL") == test_level, "level did not reach the depth reader"


def test_clean_beat_passes(test_level):
    assert check_beat_device_words(0, G_A, G_A, BEAT_BYTES, DEV_BYTES) is None


def test_phase_duplication_localized(test_level):
    # on-board read returned 0xa5a03f1ca5a03f1c for golden G_A: slot2 got slot0's
    # value (phase1 <- phase0). The checker must pin slot 2 as a shift@0.
    actual = 0xa5a03f1ca5a03f1c
    v = check_beat_device_words(0x40, G_A, actual, BEAT_BYTES, DEV_BYTES)
    assert v is not None
    bad = {b["slot"]: b for b in v["bad_slots"]}
    assert set(bad) == {2}, v
    assert bad[2]["expected"] == "0x3f18" and bad[2]["actual"] == "0x3f1c"
    assert bad[2]["class"].startswith("shift@0"), bad[2]


def test_dropped_device_words_localized(test_level):
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


def test_batch_over_snoop_and_format(test_level):
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


def test_all_clean_returns_empty(monkeypatch, test_level):
    # The all-clean stream's length is the file's one pure-repetition count:
    # alternating G_A/G_B beats at consecutive beat addresses, none flagged.
    _enter_level(monkeypatch, test_level)
    n_beats = _profile_depth('phy_wordcheck_clean_beats')
    golden = {k * BEAT_BYTES: (G_A if k % 2 == 0 else G_B) for k in range(n_beats)}
    snoop = [(addr, g, 0) for addr, g in golden.items()]
    assert check_read_device_word_order(
        snoop, lambda a, n: golden[a], BEAT_BYTES, DEV_BYTES) == []
