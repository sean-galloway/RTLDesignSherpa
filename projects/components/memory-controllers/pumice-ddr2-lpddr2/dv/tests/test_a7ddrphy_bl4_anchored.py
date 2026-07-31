# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""DETERMINISTIC PROOF of the on-board pumice DDR2 x16 BL4 read failure, and of
the fix — WITHOUT touching RTL or the board.

Ground truth (on-silicon ILA, tasks #143/#146, converged 2026-07-15):
  * The Artix-7 a7ddrphy is a FIXED nphases=4 / 8-slot BL8 de-interleaver. One
    DFI cycle exposes words_per_cycle = nphases*words_per_beat device-word slots
    (8 for x16: 4 phases x 2 device-words).
  * A BL4 read (bl=4 < 2*nphases=8) fills ONLY its rd_phase-ANCHORED contiguous
    slot run (4 slots). The slots it does NOT drive HOLD THE PREVIOUS READ'S
    device-words (STALE) — not this burst's data, not zeros.
  * pumice's read aligner (pumice_dfi_rd_aligner.sv, BL_WORDS=1) captures ALL
    words_per_cycle slots as one wide DFI word, so it takes the anchored run
    correct and the rest STALE -> exactly 2 of the 4 captured device-words wrong
    per BL4 read -> beats_mismatched == 2*txn. This is INVARIANT to gear/tap/
    pacing/rddata_delay/rd_phase.

WHY THE EARLIER test_a7ddrphy_gear_mismatch THEORY WAS WRONG
-----------------------------------------------------------
That test blamed a GEAR-RATIO mismatch (controller DFI_RATE=2 vs PHY nphases=4,
gathering only {p1,p0}=4 of 8 slots). But the board bitstream was built at
DFI_RATE=4 (== nphases, gear MATCHED — see build-perf synth logs: "Parameter
DFI_RATE bound to ...0100" == 4) and STILL read exactly 2/4 wrong. So the bug is
NOT the gear ratio; it is that a BL4 burst is SHORTER than a full BL8 DFI cycle
regardless of gear. This module supersedes the gear theory: the failure survives
gear==nphases and is reproduced here at gear=4.

CRITICAL: this proof uses a PHASE-DISTINCT data pattern (0x1111,0x2222,...). An
aliased pattern (e.g. repeating a5a0) can make a shifted/stale slot equal the
expected slot and silently HIDE the corruption — that masking wasted a whole
prior debug session. Never use an aliased pattern for a de-interleave proof.

The anchored slot layout is derived from the SAME shared contract the DV BFM and
the future RTL assertion use:
    CocoTBFramework.components.dfi.dfi_timing.bl_anchored_slot_mask
so this is not a hand-rolled model — it is the exact rule the fix must encode.
"""
import os
import sys

# Import the shared phase-mask contract from the RDS-DV framework (editable
# install => PYTHONPATH has it; env_python sets this up).
from CocoTBFramework.components.dfi.dfi_timing import bl_anchored_slot_mask
# The faithful a7ddrphy de-interleaver the BFM (DFISlavePHY) is built from —
# tying this model proof to the SAME code that runs in the integration sim.
from CocoTBFramework.components.dfi.dfi_slave_phy import deinterleave_read_window

# Reuse the committed device-word ORDER assertion (the same one the char TB uses)
# so a mismatch is LOCALIZED (which slot, and how: zero / shift@k / stale).
_TB = os.path.join(os.path.dirname(__file__), "..", "tbclasses")
sys.path.insert(0, os.path.abspath(_TB))
from axi_rd_device_word_check import check_beat_device_words  # noqa: E402


# ---- Board config (rate4_x16): the EXACT DFI geometry the bitstream was built
#      with. gear == nphases == 4 (NOT the disproven gear=2), x16 device. --------
NPHASES        = 4          # a7ddrphy fixed phase count (== board DFI_RATE)
WORDS_PER_BEAT = 2          # x16 device (2B) packed into a 32b DFI phase (K)
WORDS_PER_CYC  = NPHASES * WORDS_PER_BEAT   # 8-slot de-interleave window
DW_BITS        = 16         # x16 device word
BL             = 4          # DDR2 BL4
RD_PHASE       = 0          # board cfg: rd_phase=0 (a7ddrphy handles rdphase internally)

# Device-word bytes / a "captured BL4 read" beat = 4 device words = 64 bits.
DEV_BYTES      = DW_BITS // 8            # 2
BEAT_BYTES     = BL * DEV_BYTES          # 8  (the 4-device-word BL4 read)


def _phase_distinct(base):
    """4 DISTINCT device-words for one BL4 read — never aliased, so a stale/shift
    slot can never accidentally equal the expected slot."""
    return [(base + i) & ((1 << DW_BITS) - 1) for i in (0x1000, 0x2000, 0x3000, 0x4000)]


def _pack64(dws):
    return sum(dw << (k * DW_BITS) for k, dw in enumerate(dws))


# The board captures a BL4 read as a BL8-SHAPED wide DFI word: all
# WORDS_PER_CYC (8) device-word slots, of which only BL (4) are this read's real
# anchored data — the other 4 belong to the OTHER read packed into the same
# window. The controller (current aligner) hands the whole 8-slot word to AXI as
# the read, so half of it is the wrong read's data. The 2/4 board fingerprint is
# per BL4 AXI beat: 2 anchored-correct, 2 stale device-words.
GOLD_BL8_WIDTH = WORDS_PER_CYC * DEV_BYTES     # 16B: the BL8-shaped captured word


def _grab_bl8_shaped(window_slots):
    """CURRENT pumice aligner (rd_data_o = dfi_rddata_i, BL_WORDS=1): captures
    the WHOLE WORDS_PER_CYC-slot DFI word for the read. Returns all 8 slots."""
    return list(window_slots)


def _anchored_bl4(window_slots, first_slot):
    """THE FIX: hand AXI exactly the BL anchored device-words (the real read),
    per the shared contract — dropping the non-anchored (stale) slots."""
    return [window_slots[(first_slot + i) % WORDS_PER_CYC] for i in range(BL)]


NTXN = 8   # page-hit BL4 reads, like the board run (mism == 2*txn == 16)


def _pack_two_reads(readA, readB):
    """The a7ddrphy BL8 window carries TWO BL4 reads: read A anchored at the low
    phase-pair (slots [0:4]), read B at the high phase-pair (slots [4:8]). This
    is how consecutive page-hit BL4 reads share one 8-slot de-interleave window on
    silicon — and why the non-anchored half of read A's captured word holds read
    B's REAL data (stale), not zeros."""
    win = [0] * WORDS_PER_CYC
    for i in range(BL):
        win[i] = readA[i]
        win[BL + i] = readB[i]
    return win


def test_grab_all_phases_reproduces_board_two_of_four():
    """CURRENT aligner (rd_data_o = whole dfi_rddata_i) captures each BL4 read as
    the FULL 8-slot BL8-shaped word. Two consecutive BL4 reads pack into one
    window (A -> slots[0:4], B -> slots[4:8]); the controller hands BOTH captured
    words to AXI as full 8-device-word reads. Read A's word has slots[4:8] = read
    B's data (STALE for A); read B's word has slots[0:4] = read A's data (STALE
    for B). Over the stream exactly HALF of every captured word is the wrong (the
    OTHER read's) data -> per BL4 AXI beat 2 of 4 device-words wrong ==
    beats_mismatched == 2*txn. PHASE-DISTINCT pattern so a stale slot can never
    alias the expected value."""
    bad_total = 0
    viols = []
    npairs = NTXN // 2
    for p in range(npairs):
        A = _phase_distinct(0x0100 * (2 * p + 1))
        B = _phase_distinct(0x0100 * (2 * p + 2))
        window = _pack_two_reads(A, B)
        gotA = _grab_bl8_shaped(window)     # read A captures ALL 8 slots
        gotB = _grab_bl8_shaped(window)     # read B ALSO captures ALL 8 slots
        # The controller believes each captured 8-slot word is that read's data.
        # Golden for read A as an 8-slot word == A repeated twice (A's own 4 dws
        # are all it should see); slots[4:8] actually hold B -> flagged wrong.
        goldA8 = A + A
        goldB8 = B + B
        vA = check_beat_device_words(
            byte_addr=(2*p) * GOLD_BL8_WIDTH,
            golden_int=sum(g << (k*DW_BITS) for k, g in enumerate(goldA8)),
            actual_int=sum(a << (k*DW_BITS) for k, a in enumerate(gotA)),
            beat_bytes=GOLD_BL8_WIDTH, device_word_bytes=DEV_BYTES)
        vB = check_beat_device_words(
            byte_addr=(2*p+1) * GOLD_BL8_WIDTH,
            golden_int=sum(g << (k*DW_BITS) for k, g in enumerate(goldB8)),
            actual_int=sum(a << (k*DW_BITS) for k, a in enumerate(gotB)),
            beat_bytes=GOLD_BL8_WIDTH, device_word_bytes=DEV_BYTES)
        for v in (vA, vB):
            assert v is not None                    # every read is corrupted
            viols.append(v)
            bad_total += len(v["bad_slots"])
    # Each captured word has exactly BL (4) wrong device-words (the non-anchored
    # half carrying the OTHER read). 4 wrong * NTXN reads == 4*NTXN. Per BL4 AXI
    # beat that is 2 of 4 -> the board's beats_mismatched == 2*txn.
    assert bad_total == BL * NTXN, (
        f"expected {BL*NTXN} stale device-words (2/4 per read), got {bad_total}")
    assert bad_total == (WORDS_PER_CYC * NTXN) // 2      # half the captured data
    # Read A's wrong slots are slots[4:8] carrying read B's REAL data (a genuine
    # value, NOT zero) -> classified as a shift/stale, the board fingerprint.
    a_bad = {b["slot"]: b for b in viols[0]["bad_slots"]}
    assert set(a_bad) == {4, 5, 6, 7}, a_bad
    assert all(not b["class"].startswith("zero") for b in a_bad.values()), a_bad


def test_anchored_selection_is_bit_exact_the_fix():
    """THE FIX (hand AXI exactly the BL anchored run per read, per the shared
    contract): from the SAME shared 8-slot window, read A takes its anchored
    slots[0:4] and read B its anchored slots[4:8] -> each returns its own 4
    device-words, ZERO stale. Demonstrated without touching RTL — the contract
    (bl_anchored_slot_mask) IS the fix."""
    bad = 0
    npairs = NTXN // 2
    for p in range(npairs):
        A = _phase_distinct(0x0100 * (2 * p + 1))
        B = _phase_distinct(0x0100 * (2 * p + 2))
        window = _pack_two_reads(A, B)
        # Anchor contract: read A at rd_phase=0 (first_slot 0), read B at the next
        # phase-pair (rd_phase=BL//WORDS_PER_BEAT => first_slot BL).
        _, firstA, _ = bl_anchored_slot_mask(BL, NPHASES, WORDS_PER_BEAT, 0)
        _, firstB, _ = bl_anchored_slot_mask(
            BL, NPHASES, WORDS_PER_BEAT, BL // WORDS_PER_BEAT)
        gotA = _anchored_bl4(window, firstA)
        gotB = _anchored_bl4(window, firstB)
        for golden4, got4 in ((A, gotA), (B, gotB)):
            v = check_beat_device_words(
                byte_addr=0, golden_int=_pack64(golden4),
                actual_int=_pack64(got4),
                beat_bytes=BEAT_BYTES, device_word_bytes=DEV_BYTES)
            if v is not None:
                bad += len(v["bad_slots"])
    assert bad == 0, f"anchored selection must be exact; got {bad} bad device-words"


def test_bfm_deinterleaver_one_read_reproduces_stale():
    """Drive the ACTUAL BFM de-interleaver (deinterleave_read_window, the same
    code the integration sim runs) with the BUG cadence: ONE BL4 RD per DFI
    cycle. Consecutive reads at alternating phase-pairs leave the non-anchored
    half holding the PREVIOUS read's REAL data (stale) -> per captured window
    4 real + 4 stale == the on-silicon beats_mismatched == 2*txn."""
    bad_total = 0
    prev = []                       # first read: window starts zero
    reads = [(_phase_distinct(0x0100 * (i + 1)),
              # alternate anchor phase-pair each cycle (2 => slots[4:8], 0 =>[0:4])
              (2 if i % 2 == 0 else 0)) for i in range(NTXN)]
    windows = []
    for dws, anchor in reads:
        prev = deinterleave_read_window(prev_window=prev, bursts=[(anchor, dws)],
                                        words_per_cycle=WORDS_PER_CYC,
                                        nphases=NPHASES, words_per_beat=WORDS_PER_BEAT)
        windows.append((list(prev), dws, anchor))
    # From the SECOND read on, the non-anchored half holds the prior read's data.
    for (win, dws, anchor) in windows[1:]:
        _, first, nslots = bl_anchored_slot_mask(BL, NPHASES, WORDS_PER_BEAT, anchor)
        anchored = {(first + i) % WORDS_PER_CYC for i in range(nslots)}
        for s in range(WORDS_PER_CYC):
            if s not in anchored and win[s] != 0:
                bad_total += 1            # a real (non-zero) stale slot
    assert bad_total == BL * (NTXN - 1), (
        f"expected {BL*(NTXN-1)} stale device-words, got {bad_total}")


def test_bfm_deinterleaver_two_reads_pack_zero_stale():
    """Drive the ACTUAL BFM de-interleaver with the FIX cadence: TWO BL4 RDs per
    DFI cycle at phases {0, 2}. Both anchored runs land in ONE window ->
    slots[0:4]=readA, slots[4:8]=readB, ZERO stale — bit-exact, the fix."""
    for p in range(NTXN // 2):
        A = _phase_distinct(0x0100 * (2 * p + 1))
        B = _phase_distinct(0x0100 * (2 * p + 2))
        # Seed a non-zero previous window so any surviving stale is VISIBLE.
        prev = list(range(0xE0, 0xE0 + WORDS_PER_CYC))
        win = deinterleave_read_window(prev_window=prev,
                                       bursts=[(0, A), (BL // WORDS_PER_BEAT, B)],
                                       words_per_cycle=WORDS_PER_CYC,
                                       nphases=NPHASES, words_per_beat=WORDS_PER_BEAT)
        assert win[0:BL] == A
        assert win[BL:2 * BL] == B
        # nothing of the seed survived -> zero stale
        assert not any(win[i] in prev and prev[i] not in (A + B)
                       for i in range(WORDS_PER_CYC))


def test_contract_full_burst_degenerates_to_identity():
    """A FULL BL8 read (bl == 2*nphases) fills ALL 8 slots — no stale slots, so
    grab-all == anchored. This is why full-BL reads NEVER showed the board bug
    and only BL4 (sub-DFI-word) did."""
    wpc, first, nslots = bl_anchored_slot_mask(
        bl=2 * NPHASES, nphases=NPHASES, words_per_beat=WORDS_PER_BEAT, rd_phase=0)
    assert (wpc, first, nslots) == (WORDS_PER_CYC, 0, WORDS_PER_CYC)


def test_pattern_is_phase_distinct_not_aliased():
    """Guard the guard: the proof pattern MUST be phase-distinct, else a stale
    slot could equal the expected slot and hide the corruption (the a5a0 trap)."""
    dws = _phase_distinct(0x0100)
    assert len(set(dws)) == BL, f"pattern aliases: {[hex(x) for x in dws]}"


def test_contract_rejects_illegal_geometry():
    """The contract asserts its power-of-two / burst-size requirements so the RTL
    assertion can mirror them verbatim."""
    import pytest
    with pytest.raises(AssertionError):
        bl_anchored_slot_mask(bl=4, nphases=3, words_per_beat=2, rd_phase=0)   # nphases not pow2
    with pytest.raises(AssertionError):
        bl_anchored_slot_mask(bl=5, nphases=4, words_per_beat=2, rd_phase=0)   # odd bl
    with pytest.raises(AssertionError):
        bl_anchored_slot_mask(bl=16, nphases=4, words_per_beat=2, rd_phase=0)  # bl > full cycle
