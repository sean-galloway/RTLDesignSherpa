# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Reproduce the on-board pumice read corruption (task #143) from first
principles: the a7ddrphy 4-phase deserialize window + a slot (read-latency)
offset -> the exact device-word-shift garbage the ILA showed, caught by the
committed device-word assertion.

- slot_offset == 0  => bit-exact {p1,p0} readout (the working alignment).
- slot_offset != 0  => the controller grabs the wrong deserializer slots ->
                       shifted device-words + zeros -> assertion flags
                       shift@k / zero, matching the board.

This is the mechanism to drop into DFISlavePHY so the cocotb sim reproduces the
board and the assertion turns red on the current RTL.
"""
import os
import sys

import pytest

from TBClasses.shared.test_levels import level_env, reg_level_grid

_TB = os.path.join(os.path.dirname(__file__), "..", "..", "tbclasses")
sys.path.insert(0, os.path.abspath(_TB))

from a7ddrphy_read_window import beat_from_golden, place_read_window, read_p1p0  # noqa: E402
from axi_rd_device_word_check import check_beat_device_words                     # noqa: E402

# dv/ on sys.path so the area's depth profile resolves as `tbclasses.*`.
_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_levels import depth as _profile_depth  # noqa: E402

BEAT_BYTES, DEV_BYTES = 8, 2
G_A = 0xa5a03f18a5a03f1c    # device-words (beats): [3f1c, a5a0, 3f18, a5a0]
G_B = 0xa5a03f00a5a03f04    # device-words (beats): [3f04, a5a0, 3f00, a5a0]

# Every test carries the gate/func/full cell like a simulator wrapper does
# (tooling BUG-004). No simulator here, so the same level_env() entries go
# into THIS process's environment, where pumice_levels.depth() reads them.
pytestmark = pytest.mark.parametrize("test_level", reg_level_grid())


def _enter_level(monkeypatch, test_level):
    for k, v in level_env(test_level).items():
        monkeypatch.setenv(k, v)
    assert os.environ.get("TEST_LEVEL") == test_level, "level did not reach the depth reader"


def test_aligned_window_is_bit_exact(test_level):
    # correct read-latency alignment: {p1,p0} == the golden beat, every time.
    for g in (G_A, G_B):
        assert beat_from_golden(g, slot_offset=0) == g
        assert check_beat_device_words(0, g, beat_from_golden(g, 0),
                                       BEAT_BYTES, DEV_BYTES) is None


def test_slot_offset_reproduces_board_garbage_and_assertion_fires(test_level):
    # a +2-slot (one-phase) misalignment: controller captures beats [2,3,x,x]
    # of an isolated read (x=empty) -> shifted device-words + zeros.
    # +2-slot misalignment: window = [0,0, d0,d1, d2,d3, 0,0]; controller reads
    # slots [0:4] = [0, 0, d0, d1] -> 0xa5a03f1c00000000 for G_A.
    actual = beat_from_golden(G_A, slot_offset=2)
    assert actual == 0xa5a03f1c00000000 and actual != G_A   # board-class garbage
    v = check_beat_device_words(0x40, G_A, actual, BEAT_BYTES, DEV_BYTES)
    assert v is not None
    bad = {b["slot"]: b for b in v["bad_slots"]}
    # slots 0,1 dropped to zero; slot2 got golden slot0's device-word (a shift).
    assert bad[0]["class"].startswith("zero"), bad[0]
    assert bad[1]["class"].startswith("zero"), bad[1]
    assert bad[2]["class"].startswith("shift@0"), bad[2]


def test_offset_is_the_only_variable(monkeypatch, test_level):
    # sweep offsets: exactly one (0) is clean; every other offset corrupts.
    # The sweep width is the file's one pure-repetition count: an offset past
    # the 8-slot window drives every slot empty, which is still not clean, so
    # widening it only adds offsets the model must reject.
    _enter_level(monkeypatch, test_level)
    span = _profile_depth('phy_rdwin_offset_span')
    clean = [off for off in range(-span, span + 2)
             if check_beat_device_words(0, G_B, beat_from_golden(G_B, off),
                                        BEAT_BYTES, DEV_BYTES) is None]
    assert clean == [0], f"only slot_offset 0 should be clean, got {clean}"


def test_window_placement_primitive(test_level):
    # p0 = slots[0,1], p1 = slots[2,3]; {p1,p0} = slot3<<48|slot2<<32|slot1<<16|slot0
    win = place_read_window([0x1111, 0x2222, 0x3333, 0x4444], slot_offset=0)
    assert read_p1p0(win) == 0x4444333322221111
