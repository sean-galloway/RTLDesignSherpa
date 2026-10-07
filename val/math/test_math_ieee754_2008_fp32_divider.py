# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_ieee754_2008_fp32_divider
# Purpose: Test for the FP32 floating-point divider module
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-07

"""
Test for the FP32 floating-point divider module (math_ieee754_2008_fp32_divider).

The DUT is a multi-cycle Goldschmidt/Newton divider:
  i_valid -> ow_valid, 9 cycles from the accept edge to ow_valid on
  the normal path (10 counting the presentation cycle), 1 cycle for
  special cases (2 with accept).

Algorithm under test (see the module header for the full account):
  1. 7-bit-index / 12-bit reciprocal seed LUT (|r0*b - 1| <= 2^-7.96)
  2. two Newton refinements of the reciprocal (24x24 family mantissa
     multiplies), exhaustively bounded to |B*r2 - 2^47| <= 24992532
     (rel <= 2^-22.5) over ALL 2^24 divisors
  3. q0 = a*r2, biased so the EXACT integer residual rem = a - b*q0 lands
     in [0, 16B): 4-bit exact reduction + textbook RNE
     (round up iff guard & (round|sticky|LSB)) with TRUE sticky from the
     exact remainder -- an unfaithful last bit is a bug here
  4. SUBNORMAL_SUPPORT=1: exact subnormal-grid shift with dropped-bit
     sticky + RNE; carry out of pre-round exponent 0 yields min-normal
     (math BUG-004); ow_underflow = tiny-after-rounding AND inexact.

Oracle: exact integer long division of the 24+ bit significands -- NO float
division, NO float-threshold comparisons anywhere (float64 cannot represent
fp32 quotient boundaries exactly).
"""
import os
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.common.fp_testing import (
    FPBaseTB, FPUtils, FORMATS
)

# =============================================================================
# Exact integer oracle
# =============================================================================
#
# Everything is computed on Python integers. Operands decode to (sign, exp,
# mant); significand integers A,B in [2^23, 2^24) with signed effective
# exponents (SUBNORMAL_SUPPORT=1 normalizes subnormal operands at exponent
# k-22, hidden bit 0). The quotient is computed as qn = (A/B)*2^(1-half)
# in [1,2) with half = (A < B), at 2^53 exact precision via integer long
# division; round/sticky are TRUE (exact remainder). No float anywhere.

_EXP_MAX = 0xFF


def _decode_fields(x):
    """Extract (sign, exp, mant) integer fields for fp32."""
    return (x >> 31) & 1, (x >> 23) & _EXP_MAX, x & 0x7FFFFF


def _exact_div_oracle(a, b, subnormal_support):
    """Exact integer model: returns (result_bits, overflow, underflow, invalid)."""
    sa, ea, ma = _decode_fields(a)
    sb, eb, mb = _decode_fields(b)

    sign = sa ^ sb

    a_nan = (ea == _EXP_MAX) and (ma != 0)
    b_nan = (eb == _EXP_MAX) and (mb != 0)
    a_inf = (ea == _EXP_MAX) and (ma == 0)
    b_inf = (eb == _EXP_MAX) and (mb == 0)
    a_zero = (ea == 0) and (ma == 0)
    b_zero = (eb == 0) and (mb == 0)
    a_sub = (ea == 0) and (ma != 0)
    b_sub = (eb == 0) and (mb != 0)

    # FTZ folds subnormals into zero; =1 only true zeros are effective zero
    a_effz = a_zero or (a_sub and not subnormal_support)
    b_effz = b_zero or (b_sub and not subnormal_support)

    nanres = (sign << 31) | 0x7FC00000
    if a_nan or b_nan:
        return nanres, 0, 0, 1
    if (a_effz and b_effz) or (a_inf and b_inf):
        return nanres, 0, 0, 1
    if b_effz:
        return (sign << 31) | 0x7F800000, 0, 0, 0
    if a_effz:
        return sign << 31, 0, 0, 0
    if a_inf:
        return (sign << 31) | 0x7F800000, 0, 0, 0
    if b_inf:
        return sign << 31, 0, 0, 0

    if subnormal_support:
        def sig_exp(e, m):
            if e == 0:
                k = m.bit_length() - 1      # leading bit position 0..22
                return m << (23 - k), k - 22
            return (1 << 23) | m, e
    else:
        def sig_exp(e, m):
            return (1 << 23) | m, e

    A, ea_s = sig_exp(ea, ma)
    B, eb_s = sig_exp(eb, mb)

    half = 1 if A < B else 0
    e_f = ea_s - eb_s + 127 - half

    # exact quotient: q53 = qn * 2^53, rmd = TRUE sticky
    num = A << (53 + half)
    q53 = num // B
    rmd = num - q53 * B
    kept = q53 >> 30                     # 24-bit significand
    guard = (q53 >> 29) & 1
    rnd = (q53 >> 28) & 1
    sticky = ((q53 & ((1 << 28) - 1)) != 0) or (rmd != 0)
    lsb = kept & 1
    ru = 1 if (guard and (rnd or sticky or lsb)) else 0
    kept += ru
    if kept == (1 << 24):                # rounding carry
        kept >>= 1
        e_f += 1

    if e_f >= 255:
        return (sign << 31) | 0x7F800000, 1, 0, 0

    if e_f >= 1:
        return (sign << 31) | (e_f << 23) | (kept & 0x7FFFFF), 0, 0, 0

    # subnormal/zero grid: N_true = qn_S * 2^(e_f-1) = q53 * 2^(e_f-31)
    sh = 31 - e_f                        # >= 31
    n_val = q53 >> sh
    rembits = q53 & ((1 << sh) - 1)
    g = (q53 >> (sh - 1)) & 1
    r = (q53 >> (sh - 2)) & 1
    # TRUE sticky: bits strictly below the round bit, plus the exact remainder
    s = ((q53 & ((1 << (sh - 2)) - 1)) != 0) or (rmd != 0)
    lsb = n_val & 1
    ru = 1 if (g and (r or s or lsb)) else 0
    n_val += ru
    inexact = 1 if (rembits != 0) or (rmd != 0) else 0
    if n_val >= (1 << 23):               # BUG-004: carry -> min-normal, no flush
        return (sign << 31) | (1 << 23), 0, 0, 0
    if not subnormal_support:
        # FTZ: nonzero quotient flushes to zero with the flag
        return sign << 31, 0, 1, 0
    unf = 1 if inexact else 0
    return (sign << 31) | n_val, 0, unf, 0


class FPDividerTB(FPBaseTB):
    """Multi-cycle divider TB with an exact integer oracle and latency pins.

    Protocol: drive i_a/i_b with i_valid for one accept clock, then wait for
    the single ow_valid pulse. Result bits and all three exception flags are
    checked per vector. Latency (falling-edge count from accept to ow_valid)
    is pinned exactly: 1 cycle for special cases, 8 for the normal path --
    any FSM change shows up here.
    """

    NORM_LAT = 9
    SUBN_LAT = 10
    SPEC_LAT = 1

    def __init__(self, dut, fmt, subnormal_support):
        super().__init__(dut, fmt)
        self.subnormal_support = subnormal_support
        self.lat_min = None
        self.lat_max = None
        self.lat_by_class = {}
        self.log.info(f"SUBNORMAL_SUPPORT={int(subnormal_support)}")

    # ------------------------------------------------------------------
    # clock/reset
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('i_clk', 10, 'ns')
        self.dut.i_rst_n.value = 0
        self.dut.i_valid.value = 0
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        await self.wait_clocks('i_clk', 10)
        self.dut.i_rst_n.value = 1
        await self.wait_clocks('i_clk', 5)

    # ------------------------------------------------------------------
    # single-vector check
    # ------------------------------------------------------------------
    async def test_single_checked(self, a, b, desc=""):
        """Drive one vector, wait ow_valid, check result bits AND flags AND latency."""
        dut = self.dut
        dut.i_a.value = a
        dut.i_b.value = b
        dut.i_valid.value = 1
        await RisingEdge(dut.i_clk)          # accept edge
        dut.i_valid.value = 0

        cycles = 0
        while True:
            await FallingEdge(dut.i_clk)     # sample mid-cycle: NBAs settled
            cycles += 1
            if int(dut.ow_valid.value):
                break
            if cycles > 40:
                raise TimeoutError(f"ow_valid never asserted for {desc}")
        # Let S_OUT retire to S_IDLE so the next vector is not presented
        # while the FSM is busy (a drive in S_OUT would be dropped).
        await RisingEdge(dut.i_clk)

        result = int(dut.ow_result.value)
        exp = _exact_div_oracle(a, b, self.subnormal_support)
        exp_result, exp_ovf, exp_unf, exp_inv = exp

        # Special-case FSM path fires when any operand is NaN/Inf/zero, or a
        # subnormal in FTZ mode (folded into effective zero).
        def _is_special(x):
            xe = (x >> 23) & 0xFF
            xm = x & 0x7FFFFF
            if xe == 0xFF:
                return True                    # inf or NaN
            if xe == 0:
                # zero always; subnormal only in FTZ mode (folded to zero)
                return (xm == 0) or not self.subnormal_support
            return False
        is_special = _is_special(a) or _is_special(b)
        # Subnormal-grid results (=1, e_f <= 0, shift 1..24) take the extra
        # m*B compare cycle in S_SUBN; deep shifts flush in S_RNE (normal
        # latency); FTZ flushes likewise.
        if not is_special and self.subnormal_support:
            sa_, ea_, ma_ = _decode_fields(a)
            sb_, eb_, mb_ = _decode_fields(b)
            def _sig_exp(e, m):
                if e == 0:
                    k = m.bit_length() - 1
                    return m << (23 - k), k - 22
                return (1 << 23) | m, e
            A_, ea_s = _sig_exp(ea_, ma_)
            B_, eb_s = _sig_exp(eb_, mb_)
            half_ = 1 if A_ < B_ else 0
            e_f_ = ea_s - eb_s + 127 - half_
            if -23 <= e_f_ <= 0:
                want_lat = self.SUBN_LAT
                cls = 'subnormal'
            else:
                want_lat = self.NORM_LAT
                cls = 'normal'
        else:
            want_lat = self.SPEC_LAT if is_special else self.NORM_LAT
            cls = 'special' if is_special else 'normal'
        self.lat_by_class[cls] = self.lat_by_class.get(cls, (None, None))
        lo, hi = self.lat_by_class[cls]
        self.lat_by_class[cls] = (
            cycles if lo is None else min(lo, cycles),
            cycles if hi is None else max(hi, cycles))
        self.lat_min = cycles if self.lat_min is None else min(self.lat_min, cycles)
        self.lat_max = cycles if self.lat_max is None else max(self.lat_max, cycles)

        self.test_count += 1
        ok = True
        if cycles != want_lat:
            self.fail_count += 1
            ok = False
            self.log.error(f"FAIL {desc}: latency {cycles}, expected {want_lat} "
                           f"(a=0x{a:08X}, b=0x{b:08X})")

        if result != exp_result:
            # NaN results: any NaN encoding accepted if the oracle said NaN
            if not (exp_result == 0x7FC00000 and (result & 0x7FC00000) == 0x7FC00000):
                self.fail_count += 1
                ok = False
                self.log.error(f"FAIL {desc}: result 0x{result:08X}, expected "
                               f"0x{exp_result:08X} (a=0x{a:08X}, b=0x{b:08X})")

        for sig, got, want in (("ow_overflow", int(dut.ow_overflow.value), exp_ovf),
                               ("ow_underflow", int(dut.ow_underflow.value), exp_unf),
                               ("ow_invalid", int(dut.ow_invalid.value), exp_inv)):
            self.test_count += 1
            if got != want:
                self.fail_count += 1
                ok = False
                self.log.error(f"FAIL {desc}: {sig} got {got}, expected {want} "
                               f"(a=0x{a:08X}, b=0x{b:08X})")
            else:
                self.pass_count += 1
        return ok

    # ------------------------------------------------------------------
    # directed vectors
    # ------------------------------------------------------------------
    def _directed_vectors(self):
        fmt = self.fmt
        bias = fmt.bias
        mant_mask = (1 << fmt.mant_bits) - 1

        def sv(s, e, m):
            return FPUtils.make_value(s, e, m, fmt)

        one = sv(0, bias, 0)
        one_ulp_up = sv(0, bias, 1)            # 1 + 2^-23
        one_ulp_dn = sv(0, bias - 1, mant_mask)  # 1 - 2^-24 (largest < 1)
        two = sv(0, bias + 1, 0)
        four = sv(0, bias + 2, 0)
        b_2p23 = sv(0, bias + 23, 0)           # 2^23
        b_2p24 = sv(0, bias + 24, 0)           # 2^24
        b_2p25 = sv(0, bias + 25, 0)           # 2^25
        b_1p2p22 = sv(0, bias, 1 << 22)        # 1 + 2^-22
        b_1p2p23 = sv(0, bias, 1)              # 1 + 2^-23
        b_1m2p23 = sv(0, bias - 1, mant_mask)  # 1 - 2^-23
        min_norm = sv(0, 1, 0)
        min_sub = 1                            # subnormal, mantissa 1
        max_sub = mant_mask                    # subnormal, mantissa all ones
        three_min_sub = 3                      # 3 * min_sub
        max_norm = sv(0, fmt.exp_max - 1, mant_mask)
        inf = sv(0, fmt.exp_max, 0)
        nan = sv(0, fmt.exp_max, 1)
        zero = sv(0, 0, 0)

        v = [
            # ---- IEEE 754-2008 special cases, full sign matrix ----
            ("pos_over_pos0", one, zero), ("pos_over_neg0", one, sv(1, 0, 0)),
            ("neg_over_pos0", sv(1, bias, 0), zero),
            ("neg_over_neg0", sv(1, bias, 0), sv(1, 0, 0)),
            ("pos0_over_pos", zero, one), ("pos0_over_neg", zero, sv(1, bias, 0)),
            ("neg0_over_pos", sv(1, 0, 0), one),
            ("neg0_over_neg", sv(1, 0, 0), sv(1, bias, 0)),
            ("pos0_over_pos0", zero, zero), ("neg0_over_neg0", sv(1, 0, 0), sv(1, 0, 0)),
            ("neg0_over_pos0", sv(1, 0, 0), zero),
            ("posinf_over_posinf", inf, inf), ("neginf_over_neginf", sv(1, fmt.exp_max, 0), sv(1, fmt.exp_max, 0)),
            ("posinf_over_neginf", inf, sv(1, fmt.exp_max, 0)),
            ("neginf_over_posinf", sv(1, fmt.exp_max, 0), inf),
            ("posinf_over_pos", inf, one), ("neginf_over_pos", sv(1, fmt.exp_max, 0), one),
            ("posinf_over_neg", inf, sv(1, bias, 0)),
            ("pos_over_posinf", one, inf), ("neg_over_neginf", sv(1, bias, 0), sv(1, fmt.exp_max, 0)),
            ("neg_over_posinf", sv(1, bias, 0), inf),
            ("nan_over_pos", nan, one), ("pos_over_nan", one, nan),
            ("nan_over_inf", nan, inf), ("inf_over_nan", inf, nan),
            ("nan_over_zero", nan, zero), ("zero_over_nan", zero, nan),
            ("nan_over_nan", nan, sv(0, fmt.exp_max, 0x7FFFFF)),
            # ---- basic exactness / signs ----
            ("one_over_one", one, one),
            ("neg_one_over_one", sv(1, bias, 0), one),
            ("one_over_neg_one", one, sv(1, bias, 0)),
            ("neg_over_neg", sv(1, bias, 0), sv(1, bias, 0)),
            ("three_half", sv(0, bias, 1 << 22), two),      # 1.5/2 = 0.75
            ("one_over_two", one, two),
            ("two_over_one", two, one),
            ("four_over_two", four, two),
            ("x_over_x", sv(0, bias - 7, 0x123456), sv(0, bias - 7, 0x123456)),
            # ---- overflow / near-overflow ----
            ("maxnorm_over_half", max_norm, sv(0, bias - 1, 0)),   # -> inf + ovf
            ("maxnorm_over_1pulp", max_norm, one_ulp_up),
            ("maxnorm_over_1m2p23", max_norm, b_1m2p23),
            ("maxnorm_over_maxnorm", max_norm, max_norm),
            ("maxnorm_over_minnorm", max_norm, min_norm),          # deep tiny
            ("huge_over_tiny", sv(0, 250, mant_mask), sv(0, 2, 0)),
            # ---- boundary +-1ulp around the result=1.0 point ----
            ("1mulp_over_1m2p23", one_ulp_dn, b_1m2p23),
            ("1pulp_over_1pulp", one_ulp_up, one_ulp_up),
            ("1pulp_over_1", one_ulp_up, one),
            # ---- exact quotient / inexact pins ----
            ("minnorm_over_2p23", min_norm, b_2p23),               # = min_sub, exact
            ("minnorm_over_2p24", min_norm, b_2p24),               # exact tie -> +0
            ("minnorm_over_2p25", min_norm, b_2p25),               # below tie -> +0
            ("minnorm_over_1p2p22", min_norm, b_1p2p22),           # BUG-004 carry -> min_norm, NO uf
            ("minnorm_over_1p2p23", min_norm, b_1p2p23),
            ("minnorm_over_3", min_norm, sv(0, bias + 1, 1 << 22)),  # inexact tiny
            ("minnorm_over_half", min_norm, sv(0, bias - 1, 0)),     # exact 2^-127... normal
            ("maxnorm_times2_over_3", sv(0, fmt.exp_max - 1, mant_mask - 2), sv(0, bias + 1, 1 << 22)),
        ]
        if self.subnormal_support:
            v += [
                # ---- subnormal operand grid (=1 gradual underflow) ----
                ("minsub_over_one", min_sub, one),                 # exact min_sub
                ("minsub_over_two", min_sub, two),                 # tie -> +0 (even), uf
                ("3minsub_over_two", three_min_sub, two),          # tie -> 2*min_sub (even), uf
                ("minsub_over_four", min_sub, four),               # deep -> +0, uf
                ("maxsub_over_one", max_sub, one),                 # exact max_sub
                ("maxsub_over_two", max_sub, two),                 # tie k odd -> 0x400000, uf
                ("maxsub_over_1m2p23", max_sub, b_1m2p23),         # ~min_normal boundary
                ("one_over_minsub", one, min_sub),                 # -> inf + OVF
                ("negone_over_minsub", sv(1, bias, 0), min_sub),
                ("one_over_maxsub", one, max_sub),
                ("maxsub_over_minsub", max_sub, min_sub),
                ("subn_over_1pulp", 0x00012345, one_ulp_up),       # inexact subnormal quotient
                ("subn_over_self", 0x00012345, 0x00012345),        # 1.0 exact
                ("subn_neg_over_one", sv(1, 0, 0x54321), one),
                ("minnorm_over_minsub", min_norm, min_sub),        # inf + ovf
                ("subn_times_2p23", 1, b_2p23),                    # min_sub * 2^-23... deep
                ("subn_mid_over_2", 0x00400000, two),              # tie at 2^21 -> even, uf
                # subnormal x subnormal
                ("subn_subn", 0x00010001, 0x00010001),
                ("subn_subn2", 0x0007FFFF, 0x0000F0F0),
            ]
        else:
            v += [
                # ---- FTZ grid (=0): subnormal operands act as zero ----
                ("ftz_subn_over_one", min_sub, one),               # eff-zero -> +0
                ("ftz_one_over_subn", one, min_sub),               # x/0 rule -> +inf, no invalid
                ("ftz_negone_over_subn", sv(1, bias, 0), min_sub),
                ("ftz_subn_over_subn", min_sub, min_sub),          # 0/0 -> qNaN + invalid
                ("ftz_subn_over_zero", min_sub, zero),             # 0/0 -> qNaN + invalid
                ("ftz_zero_over_subn", zero, min_sub),             # 0/0 -> qNaN + invalid
                ("ftz_maxsub_over_one", max_sub, one),
                ("ftz_subn_over_inf", min_sub, inf),
                ("ftz_inf_over_subn", inf, min_sub),
                ("ftz_subn_over_nan", min_sub, nan),
                # tiny NORMAL quotients still flush with the flag
                ("ftz_minnorm_over_2p23", min_norm, b_2p23),
                ("ftz_minnorm_over_2p24", min_norm, b_2p24),
                ("ftz_minnorm_over_1p2p22", min_norm, b_1p2p22),
                ("ftz_minnorm_over_maxnorm", min_norm, max_norm),
            ]
        return v

    # ------------------------------------------------------------------
    # randomized sweep
    # ------------------------------------------------------------------
    def _random_pair(self):
        rng = random
        fmt = self.fmt

        def subn():
            return FPUtils.make_value(rng.randint(0, 1), 0,
                                      rng.randint(1, fmt.mant_max), fmt)

        def tiny_norm():
            return FPUtils.make_value(rng.randint(0, 1),
                                      rng.randint(1, 3),
                                      rng.randint(0, fmt.mant_max), fmt)

        def near_one():
            return FPUtils.make_value(rng.randint(0, 1),
                                      rng.randint(fmt.bias - 2, fmt.bias + 2),
                                      rng.randint(0, fmt.mant_max), fmt)

        def any_norm():
            return FPUtils.make_value(rng.randint(0, 1),
                                      rng.randint(1, fmt.exp_max - 1),
                                      rng.randint(0, fmt.mant_max), fmt)

        def mant_extreme():
            return FPUtils.make_value(rng.randint(0, 1),
                                      rng.randint(1, fmt.exp_max - 1),
                                      rng.choice([0, 1, fmt.mant_max - 1, fmt.mant_max,
                                                  1 << 22, (1 << 22) - 1]), fmt)

        r = rng.random()
        if not self.subnormal_support:
            if r < 0.70:
                return any_norm(), any_norm()
            if r < 0.85:
                return mant_extreme(), mant_extreme()
            # tiny-quotient + overflow stress
            if r < 0.93:
                return tiny_norm(), FPUtils.make_value(rng.randint(0, 1),
                    rng.randint(fmt.bias + 20, fmt.exp_max - 1),
                    rng.randint(0, fmt.mant_max), fmt)
            return FPUtils.make_value(rng.randint(0, 1),
                rng.randint(fmt.bias + 20, fmt.exp_max - 1),
                rng.randint(0, fmt.mant_max), fmt), tiny_norm()
        # =1 mode: subnormal-heavy mix
        if r < 0.25:
            return subn(), subn()
        if r < 0.45:
            return subn(), any_norm()
        if r < 0.60:
            return any_norm(), subn()
        if r < 0.75:
            return tiny_norm(), tiny_norm()
        if r < 0.85:
            return near_one(), near_one()
        if r < 0.95:
            return mant_extreme(), mant_extreme()
        return any_norm(), any_norm()

    async def run_comprehensive_tests(self):
        """Directed corners + seeded randomized sweep for this param value."""
        mode = "gradual-underflow" if self.subnormal_support else "ftz-regression"
        self.log.info(f"Starting {mode} divider tests "
                      f"(SUBNORMAL_SUPPORT={int(self.subnormal_support)})")

        for name, a, b in self._directed_vectors():
            await self.test_single_checked(a, b, f"directed_{name}")

        sweep_n = {'basic': 64, 'medium': 256, 'full': 1024}[self.test_level]
        for i in range(sweep_n):
            a, b = self._random_pair()
            await self.test_single_checked(a, b, f"sweep_{i}")

        self.log.info(f"Latency: min={self.lat_min} max={self.lat_max} "
                      f"by class {self.lat_by_class}")
        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


def get_fp32_divider_params():
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
async def fp32_divider_test(dut):
    """Directed + seeded-sweep exact-oracle tests for both SUBNORMAL_SUPPORT values."""
    subnormal_support = os.environ.get('SUBNORMAL_SUPPORT', '0') == '1'
    tb = FPDividerTB(dut, FORMATS['fp32'], subnormal_support)
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.setup_clocks_and_reset()
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_fp32_divider_params())
def test_math_ieee754_2008_fp32_divider(request, params):
    """PyTest wrapper for FP32 divider."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common',
        'rtl_math': 'rtl/math'})
    dut_name = "math_ieee754_2008_fp32_divider"
    t_name = params['test_level']
    subnormal_support = params['subnormal_support']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}_sn{int(subnormal_support)}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(

        repo_root=repo_root,

        module='math_ieee754_2008_fp32_divider'

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
