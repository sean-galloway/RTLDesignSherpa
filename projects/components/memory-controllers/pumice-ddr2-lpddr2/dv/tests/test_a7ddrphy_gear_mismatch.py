# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# *** SUPERSEDED (2026-07-15) — THE GEAR-RATIO THEORY BELOW IS WRONG. ***
# The board bitstream was rebuilt at DFI_RATE=4 (== PHY nphases=4, gear MATCHED —
# see flows-ours-uart synth logs "Parameter DFI_RATE bound to ...0100") and STILL
# read exactly 2 of every 4 device-words wrong. So the failure is NOT a gear-ratio
# mismatch. The real mechanism is that a BL4 read is SHORTER than a full BL8 DFI
# cycle: it fills only its rd_phase-anchored phase-pair and the other phases hold
# the OTHER packed read's beats (stale), which pumice's grab-all aligner captures
# as the read's data -> 2/4 wrong INDEPENDENT of gear. The correct, current proof
# is test_a7ddrphy_bl4_anchored.py (BL-anchored contract, gear=4, phase-distinct
# pattern). This file is retained ONLY as a historical record of the disproven
# theory; its tests are skipped so they cannot be mistaken for ground truth.
#
# Original (disproven) docstring follows.
"""DETERMINISTIC PROOF that the on-board pumice read failure is a GEAR-RATIO
mismatch, and that matching the gear (DFI_RATE == PHY nphases) fixes it.

Grounded in the on-silicon ILA ground truth (task #143, 2026-07-15):
  * a7ddrphy is FIXED nphases=4 -> each read burst deserializes into an 8-slot
    window = 4 DFI phases x 2 x16 device-words:
        slots:  0 1 | 2 3 | 4 5 | 6 7   =   p0 | p1 | p2 | p3
  * pumice runs DFI_RATE=2 and its adapter (dfi_v21_flat_to_a7ddrphy, g_rd2)
    gathers ONLY {p1,p0} = slots [0:4], NOPing p2,p3.
  * The board returns 16 beats for 32 read commands (2:1): each tCCD pair of
    reads resolves to the SAME beat. Mechanism proven here: the PHY packs read A
    into slots 0-3 and read B into slots 4-7 of one window; the DFI_RATE=2 gather
    reads slots 0-3 for BOTH -> both get A, B is dropped -> beats_mismatched == N/2.

This uses the committed a7ddrphy_read_window model (the PHY's real de-interleave),
so it is not a hand-wave: it is the same slot layout the silicon exhibits. It
proves, with zero board access:
  - gear=2 (gather 4 of 8 slots)  -> HALF the reads lost  (the board's 2*txn)
  - gear=4 (gather all 8 slots)   -> every read exact     (the fix)
"""
import random

import pytest

# SUPERSEDED: the gear-ratio theory was disproven on silicon (see the header).
# Skip so these disproven assertions cannot be read as ground truth; the current
# proof is test_a7ddrphy_bl4_anchored.py.
pytestmark = pytest.mark.skip(
    reason="Gear-ratio theory disproven on silicon (board DFI_RATE=4 still read "
           "2/4 wrong). Superseded by test_a7ddrphy_bl4_anchored.py.")

# The model lives in the project tbclasses; import via file path to avoid a
# package-name dependency (dv trees aren't always importable packages).
import importlib.util as _ilu
import os as _os
_MODEL = _os.path.join(
    _os.path.dirname(__file__), "..", "tbclasses", "a7ddrphy_read_window.py")
_spec = _ilu.spec_from_file_location("a7ddrphy_read_window", _MODEL)
_m = _ilu.module_from_spec(_spec)
_spec.loader.exec_module(_m)


DW_BITS = 16          # x16 device word
N_SLOTS = 8           # nphases=4 * 2 device-words


def _dws(seed, n=4):
    rng = random.Random(seed)
    return [rng.randrange(1, 1 << DW_BITS) for _ in range(n)]


def _pack_two_reads(readA, readB):
    """The a7ddrphy packs two BL4 reads into one 8-slot window:
    read A -> slots 0-3 (p0,p1), read B -> slots 4-7 (p2,p3)."""
    return list(readA) + list(readB)


def _gather_gear2(window):
    """DFI_RATE=2 controller: reads {p1,p0} = slots [0:4] only (drops p2,p3)."""
    return _m.read_p1p0(window, DW_BITS)


def _gather_gear4(window):
    """DFI_RATE=4 controller (gear == nphases): reads all 8 slots = 128b word."""
    return sum(window[s] << (s * DW_BITS) for s in range(N_SLOTS))


def _golden64(read_dws):
    return sum(dw << (k * DW_BITS) for k, dw in enumerate(read_dws))


def _golden128(readA, readB):
    return _golden64(readA) | (_golden64(readB) << (4 * DW_BITS))


NPAIRS = 8   # 16 reads = 8 tCCD pairs = 32 device-word beats, like the board run


def test_gear2_drops_half_the_reads():
    """GEAR MISMATCH (pumice DFI_RATE=2 vs fixed PHY nphases=4): the 2nd read of
    every packed pair is lost -> exactly the board's beats_mismatched == 2*txn."""
    mismatched = 0
    total = 0
    for p in range(NPAIRS):
        A, B = _dws(2 * p), _dws(2 * p + 1)
        window = _pack_two_reads(A, B)
        # Command A and command B BOTH gather {p1,p0} = slots [0:4] (the adapter
        # always reads the low 4 slots). So both see read A's data.
        got_A = _gather_gear2(window)
        got_B = _gather_gear2(window)     # same gather -> same (A's) data
        if got_A != _golden64(A):
            mismatched += 1
        if got_B != _golden64(B):         # B expected, A delivered -> mismatch
            mismatched += 1
        total += 2
    assert total == 2 * NPAIRS
    # Every 2nd read (B) is wrong: exactly half. This is the board's 2*txn.
    assert mismatched == NPAIRS, (
        f"expected half ({NPAIRS}) reads lost at gear=2, got {mismatched}")
    # And confirm the board's precise signature: B returns A's beat (the pair
    # returns the SAME beat), not garbage.
    A, B = _dws(0), _dws(1)
    w = _pack_two_reads(A, B)
    assert _gather_gear2(w) == _golden64(A)          # command A -> A (ok)
    # command B gathers the same slots -> also A: the "pair returns same beat".


def test_gear4_matches_phy_reads_every_command_exact():
    """GEAR MATCH (DFI_RATE=4 == nphases=4): the controller gathers all 8 slots,
    so both packed reads are recovered -> ZERO mismatches. THE FIX."""
    mismatched = 0
    total = 0
    for p in range(NPAIRS):
        A, B = _dws(2 * p), _dws(2 * p + 1)
        window = _pack_two_reads(A, B)
        # One gear-4 read gathers the full 128b window = {B, A}; the split layer
        # hands A to command A and B to command B (both device-word-exact).
        full = _gather_gear4(window)
        assert full == _golden128(A, B)
        got_A = full & ((1 << (4 * DW_BITS)) - 1)
        got_B = full >> (4 * DW_BITS)
        if got_A != _golden64(A):
            mismatched += 1
        if got_B != _golden64(B):
            mismatched += 1
        total += 2
    assert total == 2 * NPAIRS
    assert mismatched == 0, (
        f"gear=4 must read every command exact; got {mismatched} mismatches")
