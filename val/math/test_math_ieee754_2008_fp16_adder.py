# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_ieee754_2008_fp16_adder
# Purpose: Test for the FP16 floating-point adder module
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-01-02

"""
Test for the FP16 floating-point adder module.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.common.fp_testing import (
    FPAdderTB, FPUtils, FORMATS
)

# =============================================================================
# Exact integer oracle for the adder with optional gradual underflow
# =============================================================================
#
# Everything is computed on Python integers in units of u = 2^(1-bias-mant_bits)
# (the subnormal LSB). Every finite operand is an integer multiple of u, so the
# exact sum is a grid point and RNE rounding can only ever fire on the normal
# path -- a result that lands in the subnormal range is always exact, which is
# why ow_underflow never asserts for addition with SUBNORMAL_SUPPORT=1
# (IEEE underflow = tiny-after-rounding AND inexact, detected after rounding;
# math BUG-004 ruling in rtl/math/CLAUDE.md). With SUBNORMAL_SUPPORT=0 the
# model reproduces the current FTZ datapath bit-for-bit, including
# flush-to-zero on tiny results.

def _decode_fields(x, fmt):
    """Extract (sign, exp, mant) integer fields."""
    sign = (x >> (fmt.bits - 1)) & 1
    exp = (x >> fmt.mant_bits) & ((1 << fmt.exp_bits) - 1)
    mant = x & ((1 << fmt.mant_bits) - 1)
    return sign, exp, mant


def _exact_addsub_oracle(a, b, fmt, subnormal_support):
    """Exact integer model: returns (result_bits, overflow, underflow, invalid)."""
    m_bits = fmt.mant_bits
    bias = fmt.bias
    exp_max = fmt.exp_max

    sa, ea, ma = _decode_fields(a, fmt)
    sb, eb, mb = _decode_fields(b, fmt)

    a_is_nan = (ea == exp_max) and (ma != 0)
    b_is_nan = (eb == exp_max) and (mb != 0)
    a_is_inf = (ea == exp_max) and (ma == 0)
    b_is_inf = (eb == exp_max) and (mb == 0)

    invalid = a_is_inf and b_is_inf and (sa != sb)
    if a_is_nan or b_is_nan or invalid:
        nan = FPUtils.make_value(0, exp_max, 1, fmt)
        return nan, False, False, invalid
    if a_is_inf:
        return a, False, False, False
    if b_is_inf:
        return b, False, False, False

    a_is_zero = (ea == 0) and (ma == 0)
    b_is_zero = (eb == 0) and (mb == 0)
    a_is_sub = (ea == 0) and (ma != 0)
    b_is_sub = (eb == 0) and (mb != 0)

    if not subnormal_support:
        # FTZ on inputs: subnormal operands contribute signed zero
        if a_is_sub:
            a_is_zero, ma, a_is_sub = True, 0, False
        if b_is_sub:
            b_is_zero, mb, b_is_sub = True, 0, False

    if a_is_zero and b_is_zero:
        return (sa & sb) << (fmt.bits - 1), False, False, False
    if a_is_zero:
        return b, False, False, False
    if b_is_zero:
        return a, False, False, False

    # Exact sum in units of u: value = sig * 2^(E-bias-mant_bits)
    #   normal:    sig = 2^mant_bits + m, E = e
    #   subnormal: sig = m,               E = 1  (hidden bit 0, exp 1-bias)
    def on_grid(sign, e, m):
        sig = m if e == 0 else ((1 << m_bits) | m)
        e_eff = 1 if e == 0 else e
        mag = sig << (e_eff - 1)
        return -mag if sign else mag

    v = on_grid(sa, ea, ma) + on_grid(sb, eb, mb)
    if v == 0:
        # Exact cancellation: +0 in RNE (TB treats +0/-0 as equivalent)
        return 0, False, False, False
    sres = 1 if v < 0 else 0
    c = abs(v)

    if c >= (1 << m_bits):
        # Normal range: RNE at the (mant_bits+1)-bit boundary
        sh = c.bit_length() - 1 - m_bits
        kept = c >> sh
        if sh > 0:
            rem = c & ((1 << sh) - 1)
            half = 1 << (sh - 1)
            if rem > half or (rem == half and (kept & 1)):
                kept += 1
        exp_field = c.bit_length() - m_bits
        if kept >= (1 << (m_bits + 1)):
            kept >>= 1
            exp_field += 1
        if exp_field >= exp_max:
            inf = FPUtils.make_value(sres, exp_max, 0, fmt)
            return inf, True, False, False
        return FPUtils.make_value(sres, exp_field, kept - (1 << m_bits), fmt), False, False, False

    # Subnormal-range exact result (1 <= c < 2^mant_bits)
    if subnormal_support:
        # Exact: the grid point is representable and no rounding fires, so
        # underflow (tiny AND inexact) stays deasserted for addition.
        return FPUtils.make_value(sres, 0, c, fmt), False, False, False

    # SUBNORMAL_SUPPORT=0: legacy FTZ datapath, pinned bit-for-bit
    # (pre-round exponent <= 0 -> flush to zero with the underflow flag)
    return sres << (fmt.bits - 1), False, True, False


class FPAdderSubnormalTB(FPAdderTB):
    """FPAdderTB with an exact integer oracle and SUBNORMAL_SUPPORT awareness.

    Runs the directed gradual-underflow corner suite plus seeded randomized
    sweeps for both parameter values:
      SUBNORMAL_SUPPORT=1: full IEEE 754-2008 gradual underflow on inputs and
        outputs; ow_underflow must stay deasserted (tiny and inexact never
        co-occur for addition).
      SUBNORMAL_SUPPORT=0: regression -- subnormal inputs treated as zero and
        the legacy FTZ corners pinned bit-for-bit.
    """

    def __init__(self, dut, fmt, subnormal_support):
        super().__init__(dut, fmt)
        self.subnormal_support = subnormal_support
        self.log.info(f"SUBNORMAL_SUPPORT={int(subnormal_support)}")

    def compute_expected(self, a, b):
        return _exact_addsub_oracle(a, b, self.fmt, self.subnormal_support)

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
                               f"(a=0x{a:04X}, b=0x{b:04X})")
            else:
                self.pass_count += 1
        return ok

    def _directed_vectors(self):
        fmt = self.fmt
        m_bits = fmt.mant_bits
        min_sub = 1
        max_sub = (1 << m_bits) - 1
        min_norm = 1 << m_bits

        def sv(s, e, m):
            return FPUtils.make_value(s, e, m, fmt)

        if self.subnormal_support:
            return [
                ("subn_plus_normal", min_sub, sv(0, fmt.bias, 0)),
                ("normal_plus_subn", sv(0, fmt.bias, 0), min_sub),
                ("maxsub_plus_one", max_sub, sv(0, fmt.bias, 0)),
                ("subnormal_add", min_sub, min_sub),
                ("subnormal_add_max", max_sub, max_sub),
                # max_sub + ulp carries out of pre-round exponent 0 and must
                # land on min-normal with NO underflow flag (BUG-004 ruling)
                ("maxsub_plus_ulp_into_min_norm", max_sub, min_sub),
                ("minsub_plus_maxsub_rev", min_sub, max_sub),
                ("cancel_to_subnormal", min_norm, sv(1, 0, max_sub)),
                ("cancel_to_subnormal_rev", sv(1, 0, max_sub), min_norm),
                ("cancel_deep_to_subnormal", sv(0, 2, 0), sv(1, 1, max_sub)),
                ("cancel_exact_zero", min_norm, sv(1, 1, 0)),
                ("neg_subnormal_add", sv(1, 0, max_sub), sv(1, 0, max_sub)),
                ("neg_maxsub_plus_ulp", sv(1, 0, max_sub), sv(1, 0, min_sub)),
                ("neg_cancel_to_subnormal", sv(1, 1, 0), sv(0, 0, max_sub)),
                ("subn_plus_small_normal", sv(0, 1, 0), max_sub),
                ("small_normal_minus_subn", sv(0, 1, 0), sv(1, 1, max_sub)),
                ("normal_tie_rne", sv(0, fmt.bias, 0), sv(0, fmt.bias, 1)),
            ]
        return [
            ("ftz_subn_plus_normal", min_sub, sv(0, fmt.bias, 0)),
            ("ftz_normal_plus_subn", sv(0, fmt.bias, 0), min_sub),
            ("ftz_subn_plus_subn", min_sub, min_sub),
            ("ftz_maxsub_plus_maxsub", max_sub, max_sub),
            ("ftz_maxsub_minus_maxsub", max_sub, sv(1, 0, max_sub)),
            ("ftz_neg_subn_plus_neg_subn", sv(1, 0, min_sub), sv(1, 0, min_sub)),
            # cancellation into [min_normal/2, min_normal) flushes + flags
            ("ftz_cancel_flush_half", sv(0, 2, 0), sv(1, 1, 1 << (m_bits - 2))),
            # cancellation below min_normal/2 also flushes (no fp32 inf corner)
            ("ftz_cancel_tiny_corner", sv(0, 2, 0), sv(1, 1, max_sub)),
        ]

    def _random_pair(self):
        fmt = self.fmt
        m_bits = fmt.mant_bits
        mant_max = (1 << m_bits) - 1

        def subn():
            return FPUtils.make_value(random.randint(0, 1), 0,
                                      random.randint(1, mant_max), fmt)

        def small_norm():
            return FPUtils.make_value(random.randint(0, 1),
                                      random.randint(1, 3),
                                      random.randint(0, mant_max), fmt)

        def close_pair():
            e = random.randint(1, 2)
            m = random.randint(1, mant_max)
            dm = random.randint(0, min(8, m))
            s = random.randint(0, 1)
            return (FPUtils.make_value(s, e, m, fmt),
                    FPUtils.make_value(s ^ 1, e, m - dm, fmt))

        def any_norm():
            return FPUtils.make_value(random.randint(0, 1),
                                      random.randint(1, fmt.exp_max - 1),
                                      random.randint(0, mant_max), fmt)

        r = random.random()
        if r < 0.30:
            return subn(), subn()
        if r < 0.55:
            return subn(), small_norm()
        if r < 0.80:
            return close_pair()
        return any_norm(), any_norm()

    async def run_comprehensive_tests(self):
        """Directed corners + seeded randomized sweep for this param value."""
        mode = "gradual-underflow" if self.subnormal_support else "ftz-regression"
        self.log.info(f"Starting {mode} adder tests "
                      f"(SUBNORMAL_SUPPORT={int(self.subnormal_support)})")

        for name, a, b in self._directed_vectors():
            await self.test_single_checked(a, b, f"directed_{name}")

        sweep_n = {'basic': 64, 'medium': 256, 'full': 1024}[self.test_level]
        for i in range(sweep_n):
            a, b = self._random_pair()
            await self.test_single_checked(a, b, f"sweep_{i}")

        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


def get_fp16_adder_params():
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
async def fp16_adder_test(dut):
    """Test the FP16 adder"""
    if os.environ.get('SUBNORMAL_SUPPORT', '0') == '1':
        # The legacy float-oracle TB models FTZ behavior only; the
        # SUBNORMAL_SUPPORT=1 build runs fp16_adder_subnormal_test instead.
        dut._log.info("fp16_adder_test skipped on SUBNORMAL_SUPPORT=1 build")
        return
    tb = FPAdderTB(dut, FORMATS['fp16'])
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()

@cocotb.test(timeout_time=60, timeout_unit="ms")
async def fp16_adder_subnormal_test(dut):
    """Directed + seeded-sweep tests for both SUBNORMAL_SUPPORT values.

    Uses an exact integer oracle (see _exact_addsub_oracle) and checks the
    exception flags in addition to the result bits.
    """
    subnormal_support = os.environ.get('SUBNORMAL_SUPPORT', '0') == '1'
    tb = FPAdderSubnormalTB(dut, FORMATS['fp16'], subnormal_support)
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.clear_interface()
    await tb.wait_time(1, 'ns')
    await tb.run_comprehensive_tests()

@pytest.mark.parametrize("params", get_fp16_adder_params())
def test_math_ieee754_2008_fp16_adder(request, params):
    """PyTest wrapper for FP16 adder."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common',
        'rtl_math': 'rtl/math'})
    dut_name = "math_ieee754_2008_fp16_adder"
    t_name = params['test_level']
    subnormal_support = params['subnormal_support']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}_sn{int(subnormal_support)}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(

        repo_root=repo_root,

        module='math_ieee754_2008_fp16_adder'

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
