# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_ieee754_2008_fp16_fma
# Purpose: Test for the FP16 floating-point fma module
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-01-02

"""
Test for the FP16 floating-point fma module.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.common.fp_testing import (
    FPFMATB, FPUtils, FORMATS,
    special_value_grid, fp_special_value_product,
)

# =============================================================================
# Exact integer oracle for the FMA with optional gradual underflow
# =============================================================================
#
# Everything is computed on Python integers in units of u = 2^(1-bias-mant_bits)
# (the subnormal LSB). Every finite operand is an integer multiple of u, so the
# exact product A*B (in units of u^2) and the exact sum A*B + C (brought onto
# the u^2 grid by shifting C up by bias+mant_bits-1) are exact integers and all
# rounding is integer RNE at a known bit position -- no float anywhere.
#
# SUBNORMAL_SUPPORT=1: full IEEE 754-2008 gradual underflow on inputs and
#   outputs with single-rounded fused semantics (one rounding of the exact
#   a*b+c, validated against an independent fractions.Fraction model). The
#   exact sum is rounded once: normal RNE when the true exponent is >= 1,
#   subnormal-grid RNE otherwise, with a rounding carry out of pre-round
#   exponent 0 producing min-normal, not a flush (math BUG-004 ruling).
#   ow_underflow asserts exactly when the after-rounding result is tiny
#   (exp field 0) AND the result was inexact; exact tiny results leave it
#   deasserted. Product magnitudes down to subnormal*subnormal and alignment
#   spreads beyond the 72-bit accumulator are handled exactly (the RTL folds
#   every shifted-out bit into a TRUE sticky, with the effective-subtract
#   tie corner rounding down -- the dropped bits make the exact sum smaller
#   than the in-frame value).
# SUBNORMAL_SUPPORT=0: regression -- subnormal inputs treated as zero, tiny
#   results flushed to zero with ow_underflow, byte-identical legacy corners
#   (c=0 product-only path TRUNCATES the product, the alignment shift drops
#   bits with NO sticky, subnormal*inf -> NaN + ow_invalid, 0*b+c passes c
#   through raw). The model transcribes the legacy datapath bit-for-bit.

def _decode_fields(x, fmt):
    """Extract (sign, exp, mant) integer fields."""
    sign = (x >> (fmt.bits - 1)) & 1
    exp = (x >> fmt.mant_bits) & ((1 << fmt.exp_bits) - 1)
    mant = x & ((1 << fmt.mant_bits) - 1)
    return sign, exp, mant


def _rne(kept, rem, sh):
    """Integer round-to-nearest-even: round kept up per rem at shift sh."""
    if sh <= 0:
        return kept, False
    half = 1 << (sh - 1)
    if rem > half or (rem == half and (kept & 1)):
        return kept + 1, True
    return kept, rem != 0


def _exact_fma_oracle(a, b, c, fmt, subnormal_support):
    """Exact integer model: returns (result_bits, overflow, underflow, invalid)."""
    m_bits = fmt.mant_bits
    bias = fmt.bias
    exp_max = fmt.exp_max
    mant_mask = (1 << m_bits) - 1

    sa, ea, ma = _decode_fields(a, fmt)
    sb, eb, mb = _decode_fields(b, fmt)
    sc, ec, mc = _decode_fields(c, fmt)

    a_is_nan = (ea == exp_max) and (ma != 0)
    b_is_nan = (eb == exp_max) and (mb != 0)
    c_is_nan = (ec == exp_max) and (mc != 0)
    a_is_inf = (ea == exp_max) and (ma == 0)
    b_is_inf = (eb == exp_max) and (mb == 0)
    c_is_inf = (ec == exp_max) and (mc == 0)

    prod_sign = sa ^ sb

    # Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1
    # only true zeros are effective zero
    a_zero = (ea == 0) and (ma == 0)
    b_zero = (eb == 0) and (mb == 0)
    c_zero = (ec == 0) and (mc == 0)
    a_sub = (ea == 0) and (ma != 0)
    b_sub = (eb == 0) and (mb != 0)
    c_sub = (ec == 0) and (mc != 0)
    a_eff = a_zero or (a_sub and not subnormal_support)
    b_eff = b_zero or (b_sub and not subnormal_support)
    c_eff = c_zero or (c_sub and not subnormal_support)

    nan = FPUtils.make_value(0, exp_max, 1 << (m_bits - 1), fmt)
    invalid = ((a_eff and b_is_inf) or (b_eff and a_is_inf) or
               ((a_is_inf or b_is_inf) and c_is_inf and (prod_sign != sc)))
    if a_is_nan or b_is_nan or c_is_nan or invalid:
        return nan, False, False, invalid
    if a_is_inf or b_is_inf:
        return FPUtils.make_value(prod_sign, exp_max, 0, fmt), False, False, False
    if c_is_inf:
        return FPUtils.make_value(sc, exp_max, 0, fmt), False, False, False

    if a_eff or b_eff:
        # 0*b + c = c (raw pass-through), 0*b + 0 = signed AND of the signs
        if c_eff:
            return (prod_sign & sc) << (fmt.bits - 1), False, False, False
        return c, False, False, False

    if subnormal_support:
        return _fma_exact_gradual(ea, ma, eb, mb, ec, mc, prod_sign, sc, fmt)
    return _fma_legacy_frame(ea, ma, eb, mb, ec, mc, prod_sign, sc, fmt)


def _fma_exact_gradual(ea, ma, eb, mb, ec, mc, prod_sign, sc, fmt):
    """SUBNORMAL_SUPPORT=1: exact a*b+c on the u^2 grid, rounded once."""
    m_bits = fmt.mant_bits
    bias = fmt.bias
    exp_max = fmt.exp_max

    # Magnitudes in units of u = 2^(1-bias-mant_bits): value = mag * u
    #   normal:    mag = sig << (e-1),   sig = 2^mant_bits + m
    #   subnormal: mag = m               (hidden bit 0, effective exponent 1)
    def mag(e, m):
        return m if e == 0 else (((1 << m_bits) | m) << (e - 1))

    p = mag(ea, ma) * mag(eb, mb)                    # exact product, u^2 units
    c_u2 = mag(ec, mc) << (bias + m_bits - 1)        # addend brought to u^2
    s = (-p if prod_sign else p) + (-c_u2 if sc else c_u2)
    if s == 0:
        return 0, False, False, False
    sign = 1 if s < 0 else 0
    s = abs(s)

    # value = s * 2^(2-2*bias-2*mant_bits) = 1.f * 2^(E-bias)
    e_true = s.bit_length() + 1 - 2 * m_bits - bias

    if e_true >= 1:
        # Normal range: RNE at the (mant_bits+1)-bit boundary
        sh = s.bit_length() - 1 - m_bits
        kept = s >> sh
        rem = s & ((1 << sh) - 1)
        kept, _ = _rne(kept, rem, sh)
        e = e_true
        if kept >= (1 << (m_bits + 1)):  # rounding carried out of the mantissa
            kept >>= 1
            e += 1
        if e >= exp_max:
            return FPUtils.make_value(sign, exp_max, 0, fmt), True, False, False
        return FPUtils.make_value(sign, e, kept & ((1 << m_bits) - 1), fmt), False, False, False

    # Gradual underflow: sub_int = value / u = s / 2^(bias+mant_bits-1)
    sh = bias + m_bits - 1
    kept = s >> sh
    rem = s & ((1 << sh) - 1)
    kept, _ = _rne(kept, rem, sh)
    if kept >= (1 << m_bits):
        # Rounding carried out of pre-round exponent 0 -> min-normal, not a
        # flush (math BUG-004 ruling); the result is no longer tiny, no flag
        return FPUtils.make_value(sign, 1, 0, fmt), False, False, False
    # Tiny after rounding (exp field 0). Underflow asserts only when the
    # result was also inexact; exact subnormal results leave it deasserted.
    underflow = rem != 0
    return FPUtils.make_value(sign, 0, kept, fmt), False, underflow, False


def _fma_legacy_frame(ea, ma, eb, mb, ec, mc, prod_sign, sc, fmt):
    """SUBNORMAL_SUPPORT=0: bit-faithful transcription of the legacy datapath.

    Reproduces the FTZ input handling, the c=0 product-only TRUNCATION path,
    the alignment shift that drops bits with NO sticky, and the flush/flag
    corners exactly as the generated SV computes them.
    """
    m_bits = fmt.mant_bits
    bias = fmt.bias
    exp_max = fmt.exp_max

    if fmt.bits == 32:
        w, addw, prod_sh, c_sh = 72, 72, 24, 48
    else:
        w, addw, prod_sh, c_sh = 44, 45, 22, 33
    mask_w = (1 << w) - 1
    mask_addw = (1 << addw) - 1
    mant_lsb = w - 1 - m_bits          # mantissa field LSB in the frame
    gpos = w - 2 - m_bits              # guard bit position
    rpos = w - 3 - m_bits              # round bit position

    sig_a = (1 << m_bits) | ma
    sig_b = (1 << m_bits) | mb
    sig_p = sig_a * sig_b
    nn = (sig_p >> (2 * m_bits + 1)) & 1
    prod_exp = ea + eb - bias + nn
    mant_norm = sig_p if nn else (sig_p << 1)

    # c_eff_zero shortcut paths (c is zero or subnormal here)
    if (ec == 0):
        if prod_exp > exp_max - 1:
            return FPUtils.make_value(prod_sign, exp_max, 0, fmt), True, False, False
        if prod_exp < 1:
            return prod_sign << (fmt.bits - 1), False, True, False
        # Product-only path: TRUNCATED product mantissa, no rounding
        trunc = (mant_norm >> (m_bits + 1)) & ((1 << m_bits) - 1)
        return FPUtils.make_value(prod_sign, prod_exp, trunc, fmt), False, False, False

    prod72 = (mant_norm << prod_sh) & mask_w
    sig_c = (1 << m_bits) | mc
    c72 = (sig_c << c_sh) & mask_w

    diff = prod_exp - ec
    if diff >= 0:
        larger, pre = prod72, prod_exp
        sign_larger = prod_sign
        smaller = c72
        shift = diff
    else:
        larger, pre = c72, ec
        sign_larger = sc
        smaller = prod72
        shift = -diff
    shift = min(shift, w)
    smaller_shifted = (smaller >> shift) & mask_w

    # 44-bit accumulator / 45-bit two's-complement add. The legacy overflow
    # detect is the carry out of the adder for fp32 and bit W of the sum for
    # fp16 -- both equal bit W of the unwrapped full sum here.
    eff_sub = prod_sign != sc
    if eff_sub:
        full = larger + (mask_addw ^ smaller_shifted) + 1
        if full >= (1 << addw):
            sum_abs = full & mask_addw
            rsign = sign_larger
        else:
            sum_abs = (-(full & mask_addw)) & mask_addw
            rsign = sign_larger ^ 1
    else:
        full = larger + smaller_shifted
        sum_abs = full & mask_addw
        rsign = sign_larger
    add_ovf = 0 if eff_sub else (full >> w) & 1
    if add_ovf:
        # {carry, sum[W-1:1]} (fp32 keeps the carry; fp16 prepends 0 == drop)
        sum_abs = (full >> 1) & mask_w
    else:
        sum_abs &= mask_w

    lz_raw = w - sum_abs.bit_length() if sum_abs else w
    lz = min(lz_raw, w - 1)
    norm = (sum_abs << lz) & mask_w
    exp_adj = pre - lz_raw + add_ovf

    mant = (norm >> mant_lsb) & ((1 << m_bits) - 1)
    guard = (norm >> gpos) & 1
    round_b = (norm >> rpos) & 1
    sticky = norm & ((1 << rpos) - 1) != 0
    round_up = guard & (round_b | sticky | (mant & 1))
    mant_r = mant + round_up
    round_ovf = (mant_r >> m_bits) & 1
    mant_f = 0 if round_ovf else (mant_r & ((1 << m_bits) - 1))
    exp_f = exp_adj + round_ovf

    if exp_f >= 0 and exp_f > exp_max - 1:
        return FPUtils.make_value(rsign, exp_max, 0, fmt), True, False, False
    if exp_f < 1 or sum_abs == 0:
        underflow = (exp_f < 1) and sum_abs != 0
        return rsign << (fmt.bits - 1), False, underflow, False
    return FPUtils.make_value(rsign, exp_f, mant_f, fmt), False, False, False


# =============================================================================
# Independent fractions.Fraction cross-check of the integer oracle
# =============================================================================

def _fraction_oracle(a, b, c, fmt, subnormal_support):
    """Fully independent exact model on rational arithmetic.

    Returns (result_bits, overflow, underflow) for finite operands; specials
    are handled only by the integer oracle. Any disagreement with
    _exact_fma_oracle is a model bug -- this is the cross-check.
    """
    from fractions import Fraction

    m_bits = fmt.mant_bits
    bias = fmt.bias
    exp_max = fmt.exp_max

    def to_frac(x):
        sign, e, m = _decode_fields(x, fmt)
        if e == 0:
            # FTZ on inputs when subnormal support is off
            if m == 0 or not subnormal_support:
                f = Fraction(0)
            else:
                f = Fraction(m, 1 << m_bits) * Fraction(2) ** (1 - bias)
        else:
            f = Fraction((1 << m_bits) | m, 1 << m_bits) * Fraction(2) ** (e - bias)
        return -f if sign else f

    av, bv, cv = to_frac(a), to_frac(b), to_frac(c)
    exact = av * bv + cv
    if exact == 0:
        return 0, False, False

    sign = 1 if exact < 0 else 0
    x = abs(exact)

    # k = floor(log2(x))
    k = x.numerator.bit_length() - x.denominator.bit_length()
    if Fraction(2) ** k > x:
        k -= 1

    def round_at(unit):
        kept = x // unit
        rem = x - kept * unit
        half = unit / 2
        if rem > half or (rem == half and kept % 2):
            kept += 1
        return kept, rem != 0

    if k + bias >= 1:
        # Normal range: unit = 2^(k-mant_bits), E = k + bias
        e = k + bias
        unit = Fraction(2) ** (k - m_bits)
        kept, inexact = round_at(unit)
        if kept >= (1 << (m_bits + 1)):
            kept >>= 1
            e += 1
        if e >= exp_max:
            return FPUtils.make_value(sign, exp_max, 0, fmt), True, False
        return FPUtils.make_value(sign, e, kept & ((1 << m_bits) - 1), fmt), False, False

    # Subnormal grid: unit = u = 2^(1-bias-mant_bits)
    unit = Fraction(2) ** (1 - bias - m_bits)
    kept, inexact = round_at(unit)
    if kept >= (1 << m_bits):
        # BUG-004 carry into min-normal: not tiny, no flag
        return FPUtils.make_value(sign, 1, 0, fmt), False, False
    return FPUtils.make_value(sign, 0, kept, fmt), False, inexact


def _cross_check_oracle(fmt, subnormal_support, seed, n):
    """Compare the integer oracle against the Fraction model on n vectors.

    =1 mode uses subnormal-heavy operands: the integer oracle is exact there,
    so every vector must agree. =0 mode uses a dedicated loss-free generator
    (all operands normal, |exp diff| <= 20 so the 72/44-bit frame never drops
    a bit and the c=0 truncation path never fires): the legacy transcription
    is provably exact on those vectors, so they must agree too. Vectors
    where the legacy datapath is intentionally lossy (alignment drops, the
    truncated product-only path) are covered by the RTL sweeps instead.
    """
    from fractions import Fraction  # noqa: F401 -- model lives in _fraction_oracle
    rng = random.Random(seed ^ (0x5F0 if subnormal_support else 0xA50))
    mant_max = (1 << fmt.mant_bits) - 1

    def rand_subnormal_heavy():
        while True:
            s = rng.randint(0, 1)
            e = rng.randint(0, fmt.exp_max - 1)
            m = rng.randint(0, mant_max)
            if e == 0 and m == 0:
                continue
            # bias hard toward the subnormal / tiny range
            if rng.random() < 0.55:
                e = rng.choice([0, 0, 1, 1, 2])
                if e == 0 and m == 0:
                    m = rng.randint(1, mant_max)
            return FPUtils.make_value(s, e, m, fmt)

    def rand_loss_free():
        # All-normal operands with the product exponent within `margin` of
        # c's, so the legacy frame alignment never shifts a significand bit
        # out and the c=0 shortcut paths never fire.
        margin = min(20, (fmt.exp_max - 2) // 2 - 1)
        p_exp = rng.randint(margin + 1, fmt.exp_max - 1 - margin)
        nn = rng.randint(0, 1)
        total = p_exp + fmt.bias - nn          # ea + eb
        lo = max(1, total - (fmt.exp_max - 1))
        hi = min(fmt.exp_max - 1, total - 1)
        ea = rng.randint(lo, hi)
        eb = total - ea
        ec = p_exp + rng.randint(-margin, margin)
        return (FPUtils.make_value(rng.randint(0, 1), ea, rng.randint(0, mant_max), fmt),
                FPUtils.make_value(rng.randint(0, 1), eb, rng.randint(0, mant_max), fmt),
                FPUtils.make_value(rng.randint(0, 1), ec, rng.randint(0, mant_max), fmt))

    gen = rand_subnormal_heavy if subnormal_support else rand_loss_free
    sign_mask = (1 << (fmt.bits - 1)) - 1

    checked = 0
    for _ in range(n):
        if subnormal_support:
            a, b, c = gen(), gen(), gen()
        else:
            a, b, c = gen()
        got = _exact_fma_oracle(a, b, c, fmt, subnormal_support)
        want = _fraction_oracle(a, b, c, fmt, subnormal_support)
        # Zero results: the integer model reproduces the RTL's zero-sign
        # convention, the Fraction model always returns +0; check_result
        # treats +/-0 as equivalent, so canonicalize for the comparison.
        gz = got[0] & sign_mask
        wz = want[0] & sign_mask
        if (gz, got[1], got[2]) != (wz, want[1], want[2]):
            raise AssertionError(
                f"oracle cross-check mismatch (SUBNORMAL_SUPPORT={int(subnormal_support)}): "
                f"a=0x{a:0{fmt.bits // 4}X} b=0x{b:0{fmt.bits // 4}X} c=0x{c:0{fmt.bits // 4}X} "
                f"integer={got} fraction={want}")
        checked += 1
    return checked


class FPFMASubnormalTB(FPFMATB):
    """FPFMATB with an exact integer oracle and SUBNORMAL_SUPPORT awareness.

    Runs the directed gradual-underflow corner suite plus seeded randomized
    sweeps for both parameter values, checking result bits AND all three
    exception flags per vector:
      SUBNORMAL_SUPPORT=1: full IEEE 754-2008 gradual underflow on inputs and
        outputs; single-rounded fused semantics (one rounding of the exact
        a*b+c); ow_underflow asserts for an inexact tiny result and stays
        deasserted for exact tiny results; a rounding carry into min-normal
        is not a flush and not underflow (math BUG-004 ruling).
      SUBNORMAL_SUPPORT=0: regression -- subnormal inputs treated as zero,
        tiny results flushed to zero with the flag, byte-identical legacy
        corners (truncated c=0 product path, no-sticky alignment drops,
        subnormal*inf -> NaN + ow_invalid).
    """

    def __init__(self, dut, fmt, subnormal_support):
        super().__init__(dut, fmt)
        self.subnormal_support = subnormal_support
        self.log.info(f"SUBNORMAL_SUPPORT={int(subnormal_support)}")

    def compute_expected(self, a, b, c):
        return _exact_fma_oracle(a, b, c, self.fmt, self.subnormal_support)

    async def test_single_checked(self, a, b, c, desc=""):
        """Drive one vector and check result bits AND exception flags."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        self.dut.i_c.value = c
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        exp_result, exp_ovf, exp_unf, exp_inv = self.compute_expected(a, b, c)
        ok = self.check_result(result, exp_result, desc)

        for sig, got, want in (("ow_overflow", int(self.dut.ow_overflow.value), int(exp_ovf)),
                               ("ow_underflow", int(self.dut.ow_underflow.value), int(exp_unf)),
                               ("ow_invalid", int(self.dut.ow_invalid.value), int(exp_inv))):
            self.test_count += 1
            if got != want:
                self.fail_count += 1
                self.log.error(f"FAIL {desc}: {sig} got {got}, expected {want} "
                               f"(a=0x{a:04X}, b=0x{b:04X}, c=0x{c:04X})")
            else:
                self.pass_count += 1
        return ok

    def _directed_vectors(self):
        fmt = self.fmt
        m_bits = fmt.mant_bits
        bias = fmt.bias
        exp_max = fmt.exp_max
        mant_mask = (1 << m_bits) - 1
        min_sub = 1
        max_sub = mant_mask

        def sv(s, e, m):
            return FPUtils.make_value(s, e, m, fmt)

        def neg(x):
            return x ^ (1 << (fmt.bits - 1))

        one = sv(0, bias, 0)
        two = sv(0, bias + 1, 0)
        half = sv(0, bias - 1, 0)
        one_p_ulp = sv(0, bias, 1)                 # 1.0 + 1 ulp
        one_p_half = sv(0, bias, 1 << (m_bits - 1))  # 1.5
        min_norm = sv(0, 1, 0)
        max_sub_v = sv(0, 0, max_sub)
        min_sub_v = sv(0, 0, min_sub)
        two_min_sub = sv(0, 0, 2)
        inf = sv(0, exp_max, 0)
        nan = sv(0, exp_max, 1)
        zero = sv(0, 0, 0)

        # Exact in-frame tie at the 24-bit boundary: (1+2^-k)(1+2^-(mb+1-k))
        # = 1 + 2^-k + 2^-(mb+1-k) + 2^-(mb+1) -- kept mantissa, guard = 1,
        # round = sticky = 0 after normalization. k keeps both partner
        # exponents inside the kept field for any mantissa width.
        k = m_bits // 2 + 1
        tie_a = sv(0, bias, 1 << (m_bits - k))
        tie_b = sv(0, bias, 1 << (k - 1))
        # Same product plus an LSB-1 significand bit and a bit below the
        # guard: (1+2^-k+2^-mb)(1+2^-(mb+1-k)) adds f bits mb (LSB) and
        # 2mb+1-k (sticky) -- RNE rounds UP, truncation (legacy c=0 path)
        # keeps the dropped bits off.
        tiel_a = sv(0, bias, (1 << (m_bits - k)) | 1)
        tiel_b = tie_b

        if self.subnormal_support:
            return [
                # subnormal x subnormal: product deep below the grid
                ("sn_sn_deep_plus_zero", min_sub_v, min_sub_v, zero),      # +0, underflow
                ("sn_sn_deep_plus_minsub", min_sub_v, min_sub_v, min_sub_v),  # min_sub, underflow
                ("sn_sn_plus_c_dominates", min_sub_v, min_sub_v, one),     # 1, exact, no flag
                # subnormal x normal + subnormal
                ("sn_x_one_plus_zero", min_sub_v, one, zero),              # exact min_sub, no flag
                ("sn_x_one_plus_minsub", min_sub_v, one, min_sub_v),       # exact 2*min_sub, no flag
                ("sn_x_onep5_plus_minsub", min_sub_v, one_p_half, min_sub_v),  # 2.5u tie -> 2u, flag
                ("sn_x_onepulp_plus_minsub", min_sub_v, one_p_ulp, min_sub_v),  # fused-only flag
                ("onepulp_x_sn_plus_zero", one_p_ulp, min_sub_v, zero),    # inexact tiny, flag
                ("sn_x_half_tie_to_zero", min_sub_v, half, zero),          # 0.5u tie -> +0, flag
                ("sn_x_oneminusulp", min_sub_v, sv(0, bias, mant_mask), zero),  # (1-u)u -> u, flag
                # exact tiny (no flag) vs inexact tiny (flag)
                ("exact_tiny", min_sub_v, one, zero),
                ("inexact_tiny", min_sub_v, one_p_ulp, zero),
                # min-normal carry-out of pre-round exponent 0 (BUG-004)
                ("minnorm_carry", max_sub_v, one_p_ulp, zero),             # -> min normal, no flag
                ("minnorm_carry_with_c", max_sub_v, one_p_ulp, min_sub_v),  # -> min normal + u, no flag
                # cancellation into the subnormal range (exact) and out of it
                ("cancel_into_subnormal", one, min_norm, neg(max_sub_v)),  # u, exact, no flag
                ("cancel_out_add_sticky", tie_a, tie_b, min_sub_v),        # tie + eps -> up
                ("cancel_out_sub_tiekill", tie_a, tie_b, neg(min_sub_v)),  # tie - eps -> DOWN
                ("cancel_out_sub_tiekill_lsb1", tiel_a, tiel_b,
                 neg(min_sub_v)),                                          # tie, odd LSB, sub -> DOWN
                # product subnormal-scale with cancellation from c
                ("prod_subnorm_cancel", half, max_sub_v, neg(two_min_sub)),  # (2^22-2)u, flag
                ("prod_subnorm_c_dominates", min_sub_v, min_sub_v, half),  # half + eps, no flag
                # exact cancellation at a LARGE exponent: the in-frame sum is
                # zero with lz=44 and exp_adjusted >= 1 -- must still flush to
                # a signed zero with no flag (exact-zero corner of the
                # underflow branch, reachable only via the w_sum_44 == 0
                # disjunct)
                ("exact_zero_large_exp", one_p_half, two, neg(sv(0, bias + 1, 1 << (m_bits - 1)))),  # 1.5*2 - 3 = 0
                ("exact_zero_large_exp2", one_p_half, sv(0, bias + 3, 0),
                 neg(sv(0, bias + 3, 1 << (m_bits - 1)))),  # 1.5*8 - 12 = 0
                # all three operand positions subnormal
                ("a_pos_subnormal", min_sub_v, two, one),
                ("b_pos_subnormal", two, min_sub_v, one),
                ("c_pos_subnormal", one, two, min_sub_v),
                # specials: unchanged by the parameter except subnormal x inf
                ("sn_x_inf", min_sub_v, inf, one),                         # =1: inf, no invalid
                ("inf_x_sn", inf, min_sub_v, one),
                ("neg_sn_x_inf", neg(min_sub_v), inf, one),
                ("zero_x_inf", zero, inf, one),                            # invalid both modes
                ("inf_minus_inf", inf, one, neg(inf)),                     # invalid
                ("nan_prop", nan, one, one),
                ("sn_x_nan", min_sub_v, nan, one),
                ("zero_plus_c", zero, one, min_sub_v),                     # c passthrough
                ("zero_plus_zero", zero, one, zero),
                ("sn_x_zero", min_sub_v, one, zero),
            ]
        return [
            # FTZ corners: subnormal operands contribute signed zero
            ("ftz_sn_x_one", min_sub_v, one, one),                     # 0*b + c = c
            ("ftz_sub_c_flushed", min_sub_v, one, min_sub_v),          # c is FTZ-zero too -> +0
            ("ftz_sn_x_sn", min_sub_v, min_sub_v, one),
            ("ftz_neg_sn", neg(min_sub_v), one, one),
            # subnormal x inf is an invalid op in FTZ mode (eff-zero x inf)
            ("ftz_sn_x_inf", min_sub_v, inf, one),
            ("ftz_inf_x_sn", inf, min_sub_v, one),
            # tiny normal products flush to zero and flag (c=0 shortcut path)
            ("ftz_minnorm_sq", min_norm, min_norm, zero),
            ("ftz_minnorm_sq_neg", min_norm, min_norm, neg(zero)),
            # tiny product + dominating c: main path drops the product silently
            ("ftz_minnorm_sq_plus1", min_norm, min_norm, one),
            # c=0 product-only path TRUNCATES (round-toward-zero, no RNE):
            # kept mantissa 0x1801, guard+sticky dropped by the legacy path,
            # correctly rounded (up) at SUBNORMAL_SUPPORT=1
            ("ftz_truncation", tiel_a, tiel_b, zero),
            # sanity: an ordinary normal FMA is untouched by the parameter
            ("ftz_normal_pair", one_p_ulp, one, one),                  # exact 2+2^-23
            ("ftz_zero_plus_c", zero, one, one),
            ("ftz_zero_x_inf", zero, inf, one),
            ("ftz_inf_minus_inf", inf, one, neg(inf)),
            ("ftz_nan", nan, one, one),
        ]

    def _random_triple(self):
        fmt = self.fmt
        mant_max = (1 << fmt.mant_bits) - 1

        def subn():
            return FPUtils.make_value(random.randint(0, 1), 0,
                                      random.randint(1, mant_max), fmt)

        def small_norm():
            return FPUtils.make_value(random.randint(0, 1),
                                      random.randint(1, 3),
                                      random.randint(0, mant_max), fmt)

        def near_one():
            return FPUtils.make_value(random.randint(0, 1),
                                      random.randint(fmt.bias - 2, fmt.bias + 2),
                                      random.randint(0, mant_max), fmt)

        def any_norm():
            return FPUtils.make_value(random.randint(0, 1),
                                      random.randint(1, fmt.exp_max - 1),
                                      random.randint(0, mant_max), fmt)

        r = random.random()
        if r < 0.25:
            return subn(), subn(), subn() if random.random() < 0.5 else small_norm()
        if r < 0.45:
            return subn(), small_norm(), subn()
        if r < 0.60:
            return small_norm(), small_norm(), subn()
        if r < 0.75:
            return near_one(), near_one(), subn()
        if r < 0.90:
            return any_norm(), any_norm(), subn()
        return any_norm(), any_norm(), any_norm()

    async def run_comprehensive_tests(self):
        """Directed corners + seeded randomized sweep for this param value."""
        mode = "gradual-underflow" if self.subnormal_support else "ftz-regression"
        self.log.info(f"Starting {mode} FMA tests "
                      f"(SUBNORMAL_SUPPORT={int(self.subnormal_support)})")

        # math TASK-007: systematic special-value Cartesian product (9x9x9 = 729 cells)
        await fp_special_value_product(self.test_single_checked,
                                       special_value_grid(self.fmt),
                                       special_value_grid(self.fmt),
                                       special_value_grid(self.fmt),
                                       log=self.log)

        # Independent cross-validation of the integer oracle against a
        # fractions.Fraction model before any DUT comparison
        seed = int(os.environ.get('SEED', '0'))
        cross_n = {'basic': 200, 'medium': 600, 'full': 1500}[self.test_level]
        checked = _cross_check_oracle(self.fmt, self.subnormal_support,
                                      seed, cross_n)
        self.log.info(f"oracle cross-check: {checked} vectors vs Fraction model, 0 mismatches")
        self.test_count += checked
        self.pass_count += checked

        for name, a, b, c in self._directed_vectors():
            await self.test_single_checked(a, b, c, f"directed_{name}")

        sweep_n = {'basic': 64, 'medium': 256, 'full': 1024}[self.test_level]
        for i in range(sweep_n):
            a, b, c = self._random_triple()
            await self.test_single_checked(a, b, c, f"sweep_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


def get_fp16_fma_params():
    """Generate test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        levels = ['gate']
    elif reg_level == 'FUNC':
        levels = ['func']
    else:
        levels = ['gate', 'func', 'full']
    return [{'test_level': lvl, 'subnormal_support': ss}
            for lvl in levels for ss in (False, True)]

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def fp16_fma_test(dut):
    """Test the FP16 fma"""
    if os.environ.get('SUBNORMAL_SUPPORT', '0') == '1':
        # The legacy float-oracle TB models FTZ behavior only; the
        # SUBNORMAL_SUPPORT=1 build runs fp16_fma_subnormal_test instead.
        dut._log.info("fp16_fma_test skipped on SUBNORMAL_SUPPORT=1 build")
        return
    tb = FPFMATB(dut, FORMATS['fp16'])
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def fp16_fma_subnormal_test(dut):
    """Directed + seeded-sweep tests for both SUBNORMAL_SUPPORT values.

    Uses an exact integer oracle (see _exact_fma_oracle) and checks the
    exception flags in addition to the result bits.
    """
    subnormal_support = os.environ.get('SUBNORMAL_SUPPORT', '0') == '1'
    tb = FPFMASubnormalTB(dut, FORMATS['fp16'], subnormal_support)
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()

@pytest.mark.parametrize("params", get_fp16_fma_params())
def test_math_ieee754_2008_fp16_fma(request, params):
    """PyTest wrapper for FP16 fma."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common',
        'rtl_math': 'rtl/math'})
    dut_name = "math_ieee754_2008_fp16_fma"
    t_name = params['test_level']
    subnormal_support = params['subnormal_support']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}_sn{int(subnormal_support)}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(

        repo_root=repo_root,

        module='math_ieee754_2008_fp16_fma'

    )

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst", 'VERILATOR_TRACE': '1',
        'DUT': dut_name, 'LOG_PATH': log_path, 'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path, 'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
        'SUBNORMAL_SUPPORT': str(int(subnormal_support)),
    }
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    sim_args = ['--trace'] if enable_waves else []

    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        parameters={'SUBNORMAL_SUPPORT': 1 if subnormal_support else 0},
        sim_build=sim_build,
        extra_env=extra_env, extra_args=extra_args,
        plus_args=sim_args,
        waves=enable_waves,
    )
