# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_char_golden
# Purpose: Deterministic, bit-exact software reference model of the on-chip
#          RAPIDS characterization pattern (per-channel LFSR -> CRC-32).
#          Mirrors rtl/common/shifter_lfsr_fibonacci.sv and rtl/common/dataint_crc.sv
#          exactly as wired by axi4_slave_rd_pattern_gen.sv /
#          axi4_slave_wr_crc_check.sv / axis4_master_pattern_gen.sv.
#
# Documentation: projects/NexysA7/rapids_characterization/flows-rapids-beats/
# Subsystem: rapids_char_harness
#
# Author: sean galloway
# Created: 2026-07-03
#
# ============================================================================
# EXACT RTL SEMANTICS REPRODUCED HERE (verified bit-for-bit against hardware):
# ============================================================================
#
# LFSR (shifter_lfsr_fibonacci.sv, WIDTH=32, TAP_INDEX_WIDTH=12, TAP_COUNT=4,
#       taps = {12'd32, 12'd22, 12'd2, 12'd1}, seed = LFSR_SEED ^ channel):
#   - Right-shift Fibonacci LFSR. Feedback XORs the *tapped* bits and shifts
#     the result INTO the MSB:  r_lfsr <= {feedback, r_lfsr[WIDTH-1:1]}.
#   - Taps are 1-indexed (tap value T taps bit T-1). Taps {32,22,2,1} therefore
#     tap bits {31, 21, 1, 0}:  feedback = lfsr[31]^lfsr[21]^lfsr[1]^lfsr[0].
#   - On the reset pulse the seed is LOADED into the register. lfsr_out is the
#     *current* register value (combinational), so the SEED VALUE ITSELF is the
#     first value consumed (beat 0); each subsequent beat is one shift later.
#   - Shift only happens while the register is non-zero (matches RTL `|r_lfsr`),
#     which for a maximal-length seed never matters over these run lengths.
#
# CRC (dataint_crc.sv, DATA_WIDTH=32, CRC_WIDTH=32, POLY=0x04C11DB7,
#      POLY_INIT=0xFFFFFFFF, XOROUT=0xFFFFFFFF, REFIN=1, REFOUT=1):
#   - Standard *reflected* CRC-32 (the zlib / Ethernet variant), but built from
#     the bit-serial dataint_crc_xor_shift primitive:
#       feedback = new_bit ^ reg[31]
#       reg      = (reg << 1) & 0xFFFFFFFF ; if feedback: reg ^= POLY
#     i.e. MSB-first shift with polynomial 0x04C11DB7.
#   - Per 32-bit beat, 4 bytes are processed byte 0 first (cascade stage 0..3).
#     REFIN=1 reflects the bits within each byte before feeding MSB-first, which
#     is identical to feeding each original byte LSB-first.
#   - The internal register (r_crc_value) persists across beats (load_from_cascade),
#     so the CRC accumulates over the whole per-channel LFSR stream.
#   - The output is REFOUT (reflect all 32 bits) then XOROUT (^0xFFFFFFFF):
#       crc_out = reflect32(r_crc_value) ^ 0xFFFFFFFF.
#
# The AXIS gen/checker (axis4_*) and the AXI4 rd-gen / wr-check all instantiate
# these SAME primitives with these SAME parameters, so one golden model covers
# every on-chip block (sink gen, sink write-CRC, source read-CRC, source check).
# ============================================================================

from typing import List

# --- LFSR parameters (fixed, from the RTL instantiation) -------------------
LFSR_SEED_DEFAULT = 0xDEADBEEF
_MASK32 = 0xFFFFFFFF
# Tapped bit positions (taps {32,22,2,1} -> bits {31,21,1,0}).
_TAP_BITS = (31, 21, 1, 0)

# --- CRC parameters (fixed, from the RTL instantiation) --------------------
_CRC_POLY = 0x04C11DB7
_CRC_INIT = 0xFFFFFFFF
_CRC_XOROUT = 0xFFFFFFFF


def _reflect(value: int, width: int) -> int:
    """Reverse the low `width` bits of `value` (bit reflection)."""
    result = 0
    for i in range(width):
        if (value >> i) & 1:
            result |= 1 << (width - 1 - i)
    return result


def lfsr_seq(seed32: int, n: int) -> List[int]:
    """Return the `n` consecutive 32-bit LFSR output values.

    Mirrors shifter_lfsr_fibonacci.sv exactly: the seed value itself is the
    first output (beat 0), then each element is one right-shift-with-feedback
    later.
    """
    state = seed32 & _MASK32
    out: List[int] = []
    for _ in range(n):
        out.append(state)
        if state != 0:  # RTL only shifts while |r_lfsr
            fb = 0
            for b in _TAP_BITS:
                fb ^= (state >> b) & 1
            state = ((fb << 31) | (state >> 1)) & _MASK32
    return out


def crc32_over(values: List[int]) -> int:
    """Compute the dataint_crc-equivalent CRC-32 over a list of 32-bit values.

    REFIN=1, REFOUT=1, POLY=0x04C11DB7, INIT=0xFFFFFFFF, XOROUT=0xFFFFFFFF.
    Each 32-bit value is processed as 4 bytes, byte 0 first.
    """
    reg = _CRC_INIT
    for val in values:
        val &= _MASK32
        for byte_idx in range(4):  # cascade stage 0..3, byte 0 first
            byte = (val >> (byte_idx * 8)) & 0xFF
            refb = _reflect(byte, 8)  # REFIN: reflect bits within the byte
            for bit in range(7, -1, -1):  # feed reflected byte MSB-first
                new_bit = (refb >> bit) & 1
                fb = new_bit ^ ((reg >> 31) & 1)
                reg = (reg << 1) & _MASK32
                if fb:
                    reg ^= _CRC_POLY
    # REFOUT then XOROUT
    return _reflect(reg, 32) ^ _CRC_XOROUT


def golden_crc(channel: int, num_beats: int, base_seed: int = LFSR_SEED_DEFAULT) -> int:
    """Golden per-channel CRC: seed = base_seed ^ channel, over `num_beats`."""
    seed = (base_seed ^ channel) & _MASK32
    return crc32_over(lfsr_seq(seed, num_beats))


# Known-good hardware AND simulation values: num_beats=8, cfg_lfsr_seed=0
# (=> LFSR_SEED = 0xDEADBEEF), channels 0..3.
_KNOWN_GOOD = {
    0: 0x8C023372,
    1: 0x3FB81189,
    2: 0xD64B4EEC,
    3: 0x65F16C17,
}


if __name__ == '__main__':
    import sys

    print("RAPIDS characterization golden CRC self-test")
    print(f"  base_seed = 0x{LFSR_SEED_DEFAULT:08X}, num_beats = 8")
    print("  ch  golden      expected    match")
    all_ok = True
    for ch in range(4):
        got = golden_crc(ch, 8)
        exp = _KNOWN_GOOD[ch]
        ok = (got == exp)
        all_ok &= ok
        print(f"  {ch}   0x{got:08X}  0x{exp:08X}  {'OK' if ok else 'FAIL'}")
        assert ok, f"ch{ch}: golden 0x{got:08X} != known-good 0x{exp:08X}"

    print("SELF-TEST PASSED: golden model reproduces all known-good values."
          if all_ok else "SELF-TEST FAILED")
    sys.exit(0 if all_ok else 1)
