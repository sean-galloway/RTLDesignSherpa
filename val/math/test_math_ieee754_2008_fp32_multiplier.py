# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_ieee754_2008_fp32_multiplier
# Purpose: Test for the FP32 floating-point multiplier module
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-01-02

"""
Test for the FP32 floating-point multiplier module.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.common.fp_testing import (
    FPMultiplierTB, FPUtils, FORMATS
)

# =============================================================================
# Exact integer oracle for the multiplier with optional gradual underflow
# =============================================================================
#
# Everything is computed on Python integers in units of u = 2^(1-bias-mant_bits)
# (the subnormal LSB). Every finite operand is an integer multiple of u, so the
# exact product A*B (in units of u^2) is an exact integer and all rounding is
# integer RNE at a known bit position -- no float anywhere.
#
# SUBNORMAL_SUPPORT=1: full IEEE 754-2008 gradual underflow on inputs and
#   outputs. Subnormal operands decode at effective biased exponent 1
#   (hidden bit 0); a product whose true exponent is < 1 is right-shifted onto
#   the subnormal grid and rounded RNE, so unlike addition a multiplier CAN
#   produce an inexact tiny result: ow_underflow asserts exactly when the
#   post-rounding result is tiny (exp field 0) AND the product was inexact.
#   Exact tiny products exist here (powers of two, x*1.0) and must NOT flag.
#   A rounding carry out of pre-round exponent 0 yields min-normal, not a
#   flush (math BUG-004 ruling in rtl/math/CLAUDE.md).
# SUBNORMAL_SUPPORT=0: regression -- subnormal inputs treated as zero, tiny
#   products flushed to zero with ow_underflow, byte-identical legacy corners
#   (including subnormal*inf -> NaN + ow_invalid).

def _decode_fields(x, fmt):
    """Extract (sign, exp, mant) integer fields."""
    sign = (x >> (fmt.bits - 1)) & 1
    exp = (x >> fmt.mant_bits) & ((1 << fmt.exp_bits) - 1)
    mant = x & ((1 << fmt.mant_bits) - 1)
    return sign, exp, mant


def _exact_mult_oracle(a, b, fmt, subnormal_support):
    """Exact integer model: returns (result_bits, overflow, underflow, invalid)."""
    m_bits = fmt.mant_bits
    bias = fmt.bias
    exp_max = fmt.exp_max
    mant_mask = (1 << m_bits) - 1

    sa, ea, ma = _decode_fields(a, fmt)
    sb, eb, mb = _decode_fields(b, fmt)

    a_is_nan = (ea == exp_max) and (ma != 0)
    b_is_nan = (eb == exp_max) and (mb != 0)
    a_is_inf = (ea == exp_max) and (ma == 0)
    b_is_inf = (eb == exp_max) and (mb == 0)

    sign = sa ^ sb

    a_is_zero = (ea == 0) and (ma == 0)
    b_is_zero = (eb == 0) and (mb == 0)
    a_is_sub = (ea == 0) and (ma != 0)
    b_is_sub = (eb == 0) and (mb != 0)

    # Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1
    # only true zeros are effective zero
    a_eff_zero = a_is_zero or (a_is_sub and not subnormal_support)
    b_eff_zero = b_is_zero or (b_is_sub and not subnormal_support)

    invalid = (a_eff_zero and b_is_inf) or (b_eff_zero and a_is_inf)
    if a_is_nan or b_is_nan or invalid:
        # Quiet NaN with the XOR sign, matching the RTL's canonical encoding
        nan = FPUtils.make_value(sign, exp_max, 1 << (m_bits - 1), fmt)
        return nan, False, False, invalid
    if a_is_inf or b_is_inf:
        return FPUtils.make_value(sign, exp_max, 0, fmt), False, False, False
    if a_eff_zero or b_eff_zero:
        return sign << (fmt.bits - 1), False, False, False

    if not subnormal_support:
        # Legacy FTZ: subnormal operands contribute signed zero
        if a_is_sub:
            a_is_zero, ma, a_is_sub = True, 0, False
        if b_is_sub:
            b_is_zero, mb, b_is_sub = True, 0, False

    # Operand magnitudes in units of u: value = sig * 2^(E-bias-mant_bits)
    #   normal:    sig = 2^mant_bits + m, E = e
    #   subnormal: sig = m,               E = 1  (hidden bit 0, exp 1-bias)
    def mag(e, m):
        sig = m if e == 0 else ((1 << m_bits) | m)
        return sig << ((1 if e == 0 else e) - 1)

    p = mag(ea, ma) * mag(eb, mb)  # exact product, units of u^2
    if p == 0:
        return sign << (fmt.bits - 1), False, False, False

    bl = p.bit_length()
    # value = p * 2^(2-2*bias-2*mant_bits) = m * 2^(E_true-bias), m in [1,2)
    e_true = bl + 1 - 2 * m_bits - bias

    if e_true >= 1:
        # Normal range: RNE at the (mant_bits+1)-bit boundary
        sh = bl - 1 - m_bits
        kept = p >> sh
        rem = p & ((1 << sh) - 1)
        half = 1 << (sh - 1)
        if rem > half or (rem == half and (kept & 1)):
            kept += 1
        e = e_true
        if kept >= (2 << m_bits):  # rounding carried out of the mantissa
            kept >>= 1
            e += 1
        if e >= exp_max:
            return FPUtils.make_value(sign, exp_max, 0, fmt), True, False, False
        return FPUtils.make_value(sign, e, kept & mant_mask, fmt), False, False, False

    if not subnormal_support:
        # Legacy FTZ: post-rounding tiny products flush to zero + flag
        return sign << (fmt.bits - 1), False, True, False

    # Gradual underflow: sub_int_exact = value / u = p / 2^(bias+mant_bits-1)
    sh = bias + m_bits - 1
    kept = p >> sh
    rem = p & ((1 << sh) - 1)
    half = 1 << (sh - 1)
    if rem > half or (rem == half and (kept & 1)):
        kept += 1
    if kept >= (1 << m_bits):
        # Rounding carried out of pre-round exponent 0 -> min-normal, not a
        # flush (math BUG-004 ruling); the result is no longer tiny, so no flag
        return FPUtils.make_value(sign, 1, 0, fmt), False, False, False
    # Tiny after rounding (exp field 0). Underflow asserts only when the
    # product was also inexact; exact subnormal products leave it deasserted.
    underflow = rem != 0
    return FPUtils.make_value(sign, 0, kept, fmt), False, underflow, False


class FPMultiplierSubnormalTB(FPMultiplierTB):
    """FPMultiplierTB with an exact integer oracle and SUBNORMAL_SUPPORT awareness.

    Runs the directed gradual-underflow corner suite plus seeded randomized
    sweeps for both parameter values:
      SUBNORMAL_SUPPORT=1: full IEEE 754-2008 gradual underflow on inputs and
        outputs; ow_underflow asserts for an inexact tiny product (multiplier
        rounding IS inexact at the subnormal boundary, unlike addition) and
        stays deasserted for exact tiny products (powers of two, x*1.0).
      SUBNORMAL_SUPPORT=0: regression -- subnormal inputs treated as zero,
        tiny products flushed to zero with the flag, byte-identical legacy.
    """

    def __init__(self, dut, fmt, subnormal_support):
        super().__init__(dut, fmt)
        self.subnormal_support = subnormal_support
        self.log.info(f"SUBNORMAL_SUPPORT={int(subnormal_support)}")

    def compute_expected(self, a, b):
        return _exact_mult_oracle(a, b, self.fmt, self.subnormal_support)

    async def test_single_checked(self, a, b, desc=""):
        """Drive one vector and check result bits AND exception flags."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        await self.wait_time(1, 'ns')

        result = int(self.dut.ow_result.value)
        exp_result, exp_ovf, exp_unf, exp_inv = self.compute_expected(a, b)
        ok = self.check_result(result, exp_result, desc)

        for sig, got, want in (("ow_overflow", int(self.dut.ow_overflow.value), int(exp_ovf)),
                               ("ow_underflow", int(self.dut.ow_underflow.value), int(exp_unf)),
                               ("ow_invalid", int(self.dut.ow_invalid.value), int(exp_inv))):
            self.test_count += 1
            if got != want:
                self.fail_count += 1
                self.log.error(f"FAIL {desc}: {sig} got {got}, expected {want} "
                               f"(a=0x{a:08X}, b=0x{b:08X})")
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

        one = sv(0, bias, 0)
        two = sv(0, bias + 1, 0)
        four = sv(0, bias + 2, 0)
        half = sv(0, bias - 1, 0)
        half_ulp = sv(0, bias - 1, 1)              # 0.5 + 1 ulp
        below_one = sv(0, bias - 1, mant_mask)     # largest fp strictly < 1.0
        one_p_ulp = sv(0, bias, 1)                 # 1.0 + 1 ulp
        min_norm = sv(0, 1, 0)
        min_sub_pow_m = sv(0, bias + m_bits, 0)    # 2^mant_bits: min_sub * it = min normal
        tiny_normal = sv(0, 1, 1)
        inf = sv(0, exp_max, 0)
        nan = sv(0, exp_max, 1)
        zero = sv(0, 0, 0)

        if self.subnormal_support:
            return [
                # min_normal x < 1 -> subnormal results
                ("minnorm_x_half", min_norm, half),
                ("minnorm_x_half_rev", half, min_norm),
                ("minnorm_x_half_neg", min_norm, sv(1, bias - 1, 0)),
                ("minnorm_x_three_quarter", min_norm, sv(0, bias - 2, 1 << (m_bits - 1))),
                # inexact subnormal -> rounds, flags underflow
                ("minnorm_x_half_plus_ulp", min_norm, half_ulp),
                # tie at top of subnormal range: carries out of pre-round
                # exponent 0 -> min-normal, NOT a flush, NO underflow (BUG-004)
                ("minnorm_x_below_one", min_norm, below_one),
                # subnormal x normal
                ("minsub_x_one", min_sub, one),            # exact, no flag
                ("one_x_minsub", one, min_sub),
                ("maxsub_x_one", max_sub, one),            # exact x*1.0, no flag
                ("minsub_x_1p5_tie", min_sub, sv(0, bias, 1 << (m_bits - 1))),
                # tie exactly at half of min_sub: rounds to +0, inexact -> flag
                ("minsub_x_half_tie", min_sub, half),
                # just above that tie: rounds up to min_sub, inexact -> flag
                ("minsub_x_half_up", min_sub, half_ulp),
                # max_sub x (1+ulp) carries out of pre-round exponent 0 ->
                # min-normal, NO underflow (BUG-004)
                ("maxsub_x_one_p_ulp", max_sub, one_p_ulp),
                ("maxsub_x_two", max_sub, two),            # exact normal
                # exact tiny products with a subnormal operand: powers of two,
                # underflow must stay deasserted
                ("minsub_x_four", min_sub, four),
                ("minsub_x_2pow_mbits_to_min_norm", min_sub, min_sub_pow_m),
                ("subn_x_tiny_normal", min_sub, tiny_normal),  # deep -> +0, flag
                # subnormal x subnormal: product is always far below the grid
                ("subn_x_subn_mins", min_sub, min_sub),
                ("subn_x_subn_maxs", max_sub, max_sub),
                ("subn_x_subn_mixed", min_sub, max_sub),
                # sign / zero / inf / NaN special cases (unchanged by the param)
                ("zero_x_subn", zero, min_sub),
                ("subn_x_zero", min_sub, zero),
                ("subn_x_inf", min_sub, inf),
                ("neg_subn_x_inf", sv(1, 0, min_sub), inf),
                ("inf_x_subn", inf, min_sub),
                ("nan_x_subn", nan, min_sub),
                ("subn_x_nan", min_sub, nan),
                ("inf_x_zero", inf, zero),
                ("zero_x_inf", zero, inf),
            ]
        return [
            ("ftz_subn_x_one", min_sub, one),          # eff-zero -> signed zero
            ("ftz_one_x_subn", one, min_sub),
            ("ftz_subn_x_subn", min_sub, min_sub),
            ("ftz_maxsub_x_maxsub", max_sub, max_sub),
            ("ftz_neg_subn_x_one", sv(1, 0, min_sub), one),
            # subnormal x inf is an invalid op in FTZ mode (eff-zero x inf)
            ("ftz_subn_x_inf", min_sub, inf),
            ("ftz_inf_x_subn", inf, min_sub),
            # tiny normal products flush to zero and flag
            ("ftz_minnorm_x_half", min_norm, half),
            ("ftz_minnorm_x_half_ulp", min_norm, half_ulp),
            ("ftz_subn_x_normal", min_sub, sv(0, 1, 0)),
            # sanity: an ordinary normal product is untouched by the param
            ("ftz_normal_pair", one, below_one),
        ]

    def _random_pair(self):
        fmt = self.fmt
        mant_max = fmt.mant_max

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
        if r < 0.30:
            return subn(), subn()
        if r < 0.55:
            return subn(), small_norm()
        if r < 0.70:
            return subn(), any_norm()
        if r < 0.85:
            return small_norm(), small_norm()
        if r < 0.95:
            return near_one(), near_one()
        return any_norm(), any_norm()

    async def run_comprehensive_tests(self):
        """Directed corners + seeded randomized sweep for this param value."""
        mode = "gradual-underflow" if self.subnormal_support else "ftz-regression"
        self.log.info(f"Starting {mode} multiplier tests "
                      f"(SUBNORMAL_SUPPORT={int(self.subnormal_support)})")

        for name, a, b in self._directed_vectors():
            await self.test_single_checked(a, b, f"directed_{name}")

        sweep_n = {'basic': 64, 'medium': 256, 'full': 1024}[self.test_level]
        for i in range(sweep_n):
            a, b = self._random_pair()
            await self.test_single_checked(a, b, f"sweep_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


def get_fp32_multiplier_params():
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
async def fp32_multiplier_test(dut):
    """Test the FP32 multiplier"""
    if os.environ.get('SUBNORMAL_SUPPORT', '0') == '1':
        # The legacy float-oracle TB models FTZ behavior only; the
        # SUBNORMAL_SUPPORT=1 build runs fp32_multiplier_subnormal_test instead.
        dut._log.info("fp32_multiplier_test skipped on SUBNORMAL_SUPPORT=1 build")
        return
    tb = FPMultiplierTB(dut, FORMATS['fp32'])
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def fp32_multiplier_subnormal_test(dut):
    """Directed + seeded-sweep tests for both SUBNORMAL_SUPPORT values.

    Uses an exact integer oracle (see _exact_mult_oracle) and checks the
    exception flags in addition to the result bits.
    """
    subnormal_support = os.environ.get('SUBNORMAL_SUPPORT', '0') == '1'
    tb = FPMultiplierSubnormalTB(dut, FORMATS['fp32'], subnormal_support)
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()

@pytest.mark.parametrize("params", get_fp32_multiplier_params())
def test_math_ieee754_2008_fp32_multiplier(request, params):
    """PyTest wrapper for FP32 multiplier."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common',
        'rtl_math': 'rtl/math'})
    dut_name = "math_ieee754_2008_fp32_multiplier"
    t_name = params['test_level']
    subnormal_support = params['subnormal_support']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}_sn{int(subnormal_support)}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(

        repo_root=repo_root,

        module='math_ieee754_2008_fp32_multiplier'

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
