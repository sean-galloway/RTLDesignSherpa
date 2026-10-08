# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_ieee754_2008_fp32_sqrt
# Purpose: Test for the FP32 floating-point square root module
#
# Documentation: IEEE754_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-07

"""
Test for the FP32 floating-point square root module (math_ieee754_2008_fp32_sqrt).

The DUT is a multi-cycle Newton-Raphson reciprocal-sqrt unit:
  i_valid -> ow_valid, 10 cycles from the accept edge to ow_valid on the
  odd-exponent path (11 for even exponents, which need the 1/sqrt(2)
  significand-scale cycle), 1 cycle for special cases.

Algorithm under test (see the module header for the full account):
  1. 7-bit-index / 12-bit-entry reciprocal-sqrt seed LUT over the significand
     top bits (bucket-center, |r0 - r0*| <= 2^-8 class measured at bucket ends)
  2. two textbook Newton refinements r' = r*(3/2 - b*r^2/2) on the shared
     24x24 family significand multiplier (u = r*r, t = b*u, r' = r*e with
     e = 3/2 - t/2), exhaustively bounded over ALL 2^24 significands at
     generate time
  3. y = b*r2 (significand root), biased DOWN by a generate-time-measured
     constant, so the EXACT residual rem = W - y0^2 (W = S<<(23+parity))
     lands in [0, 15*2y0): 4-bit exact square-test reduction + textbook RNE
     (round up iff rem' >= Y_base+1) with TRUE sticky from the exact
     remainder -- an unfaithful last bit is a bug here. Half-ULP ties can
     never occur (W is an integer, (k+1/2)^2 is not), so RNE degenerates to
     exact round-to-nearest.
  4. exponent halving with ODD-exponent 1/sqrt(2) significand scaling;
     rounding carry out of the significand bumps the result exponent.

Special values: sqrt(+/-0) = +/-0 (sign preserved, exact), sqrt(-x) for
x nonzero (incl. -inf) = canonical qNaN + ow_invalid, sqrt(+inf) = +inf,
sqrt(NaN) = canonical qNaN + ow_invalid.
SUBNORMAL_SUPPORT=0 (FTZ): subnormal inputs act as +/-0 -> result +/-0,
no invalid, no underflow. =1: subnormal inputs are normalized into the
normal range and run the normal path. NOTE: a square root can NEVER
underflow or overflow for finite fp32 inputs (sqrt pushes every exponent
toward zero: sqrt(2^-149) ~ 2^-75, sqrt(~2^128) < 2^64), so results are
always normal and ow_underflow is tied low by design.

Oracle: exact integer isqrt of the 48-bit radicand W = S<<(23+parity) --
NO float anywhere in the oracle (float64 cannot represent fp32 sqrt
boundaries exactly).
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
# Operands decode to (sign, exp, mant). Positive finite operands normalize to
# a 24-bit significand S in [2^23, 2^24) with effective exponent E_x (biased
# field minus 127; SUBNORMAL_SUPPORT=1 normalizes subnormal inputs at
# E_x = k-149, k the leading-bit position). With g = E_x mod 2 (non-negative
# mod, == floor semantics) and e_r = floor(E_x/2) + 127, the exact result
# significand is RNE_24bit(sqrt(W)), W = S << (23+g), an exact integer:
# ties can never occur (proved: W integer, (k+1/2)^2 = k^2+k+1/4 not), so
# RNE is exact round-to-nearest with round-up iff rem >= y+1.

_EXP_MAX = 0xFF


def _decode_fields(x):
    """Extract (sign, exp, mant) integer fields for fp32."""
    return (x >> 31) & 1, (x >> 23) & _EXP_MAX, x & 0x7FFFFF


def _exact_sqrt_oracle(a, subnormal_support):
    """Exact integer model: returns (result_bits, underflow, invalid)."""
    sa, ea, ma = _decode_fields(a)

    a_nan = (ea == _EXP_MAX) and (ma != 0)
    a_inf = (ea == _EXP_MAX) and (ma == 0)
    a_zero = (ea == 0) and (ma == 0)
    a_sub = (ea == 0) and (ma != 0)

    nanres = 0x7FC00000
    if a_nan:
        return nanres, 0, 1
    if a_inf:
        if sa:
            return nanres, 0, 1          # sqrt(-inf) = qNaN + invalid
        return 0x7F800000, 0, 0
    if a_zero:
        return sa << 31, 0, 0            # sqrt(+/-0) = +/-0, sign preserved
    if a_sub and not subnormal_support:
        return sa << 31, 0, 0            # FTZ: subnormal acts as +/-0, sign kept
    if sa:
        return nanres, 0, 1              # sqrt(negative) = qNaN + invalid

    if a_sub:
        k = ma.bit_length() - 1          # leading bit position 0..22
        S = ma << (23 - k)
        E_x = k - 149
    else:
        S = (1 << 23) | ma
        E_x = ea - 127

    g = E_x % 2                          # Python % is floor-semantics
    e_r = E_x // 2 + 127

    W = S << (23 + g)
    y = _isqrt(W)
    rem = W - y * y
    if rem >= y + 1:
        y += 1
    inexact = 1 if rem != 0 else 0
    if y >= (1 << 24):                   # rounding carry out of the significand
        y >>= 1
        e_r += 1

    # sqrt of any finite fp32 input is always normal (never underflows)
    if e_r < 1:
        raise RuntimeError(f"oracle: subnormal sqrt result (unreachable): a={a:#x}")

    return (e_r << 23) | (y & 0x7FFFFF), 0, 0


def _isqrt(n):
    """Exact integer square root (Newton, no float)."""
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


class FPSqrtTB(FPBaseTB):
    """Multi-cycle sqrt TB with an exact integer oracle and latency pins.

    Protocol: drive i_a with i_valid for one accept clock, then wait for the
    single ow_valid pulse. Result bits and both exception flags are checked
    per vector. Latency (falling-edge count from accept to ow_valid) is
    pinned exactly per class: 1 cycle for special cases, 10 for odd-exponent
    (g=1) normal results, 11 for even-exponent (g=0) results which need the
    1/sqrt(2) significand-scale cycle -- any FSM change shows up here.
    """

    ODD_LAT = 10
    EVEN_LAT = 11
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
        await self.wait_clocks('i_clk', 10)
        self.dut.i_rst_n.value = 1
        await self.wait_clocks('i_clk', 5)

    # ------------------------------------------------------------------
    # single-vector check
    # ------------------------------------------------------------------
    async def test_single_checked(self, a, desc=""):
        """Drive one vector, wait ow_valid, check result bits AND flags AND latency."""
        dut = self.dut
        dut.i_a.value = a
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
        exp_result, exp_unf, exp_inv = _exact_sqrt_oracle(a, self.subnormal_support)

        # Special-case FSM path fires for NaN/Inf/zero, any negative
        # operand (qNaN + invalid), or a subnormal in FTZ mode.
        def _is_special(x):
            xe = (x >> 23) & 0xFF
            xm = x & 0x7FFFFF
            if xe == 0xFF:
                return True                    # inf or NaN
            if xm == 0 and xe == 0:
                return True                    # zero
            if (x >> 31) & 1:
                return True                    # negative -> qNaN + invalid
            if xe == 0:
                # positive subnormal: special only in FTZ mode
                return not self.subnormal_support
            return False

        if _is_special(a):
            want_lat = self.SPEC_LAT
            cls = 'special'
        else:
            # normal path: latency depends on the exponent parity (g)
            _, ea_, ma_ = _decode_fields(a)
            if ea_ == 0:
                k_ = ma_.bit_length() - 1
                E_x_ = k_ - 149
            else:
                E_x_ = ea_ - 127
            if E_x_ % 2 == 1:
                want_lat = self.ODD_LAT
                cls = 'odd'
            else:
                want_lat = self.EVEN_LAT
                cls = 'even'
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
                           f"(a=0x{a:08X})")

        if result != exp_result:
            # NaN results: any NaN encoding accepted if the oracle said NaN
            if not (exp_result == 0x7FC00000 and (result & 0x7FC00000) == 0x7FC00000):
                self.fail_count += 1
                ok = False
                self.log.error(f"FAIL {desc}: result 0x{result:08X}, expected "
                               f"0x{exp_result:08X} (a=0x{a:08X})")

        for sig, got, want in (("ow_underflow", int(dut.ow_underflow.value), exp_unf),
                               ("ow_invalid", int(dut.ow_invalid.value), exp_inv)):
            self.test_count += 1
            if got != want:
                self.fail_count += 1
                ok = False
                self.log.error(f"FAIL {desc}: {sig} got {got}, expected {want} "
                               f"(a=0x{a:08X})")
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
        two = sv(0, bias + 1, 0)
        four = sv(0, bias + 2, 0)
        one_ulp_up = sv(0, bias, 1)            # 1 + 2^-23
        one_ulp_dn = sv(0, bias - 1, mant_mask)  # 1 - 2^-24 (largest < 1)
        b_1p2p11 = sv(0, bias, 1 << 12)        # 1 + 2^-11 (perfect-square root grid)
        min_norm = sv(0, 1, 0)
        min_sub = 1                            # subnormal, mantissa 1
        max_sub = mant_mask                    # subnormal, mantissa all ones
        max_norm = sv(0, fmt.exp_max - 1, mant_mask)
        inf = sv(0, fmt.exp_max, 0)
        nan = sv(0, fmt.exp_max, 1)
        zero = sv(0, 0, 0)

        # perfect squares: (1 + k*2^-11)^2 has an exact 24-bit significand
        def square(s, e, m):
            """Return the fp32 value of sv(s,e,m)**2 when exactly representable."""
            sig = (1 << 23) | m
            sq = sig * sig                    # 46/47-bit integer
            exp2 = 2 * (e - bias)
            if sq >= (1 << 47):               # significand in [2,4): bump exp
                sq >>= 23
                exp2 += 1
            else:                             # significand in [1,2)
                sq >>= 23
            return FPUtils.make_value(s, exp2 + bias, sq & mant_mask, fmt)

        v = [
            # ---- IEEE 754-2008 special cases, full sign matrix ----
            ("pos_sqrt_pos0", zero), ("pos_sqrt_neg0", sv(1, 0, 0)),
            ("neg_sqrt_pos0_invalid_sign", sv(1, bias, 0)),   # sqrt(-1) = qNaN
            ("pos_sqrt_posinf", inf), ("pos_sqrt_neginf", sv(1, fmt.exp_max, 0)),
            ("pos_sqrt_qnan", nan), ("pos_sqrt_snan", sv(0, fmt.exp_max, 1 << 21)),
            ("neg_sqrt_qnan", sv(1, fmt.exp_max, 1)),
            ("neg_sqrt_minnorm", sv(1, 1, 0)),
            ("neg_sqrt_maxnorm", sv(1, fmt.exp_max - 1, mant_mask)),
            ("neg_sqrt_one", sv(1, bias, 0)),
            ("neg_sqrt_subnorm", sv(1, 0, 1)),
            # ---- basic exactness ----
            ("sqrt_one", one),
            ("sqrt_two_inexact", two),                          # sqrt(2) irrational
            ("sqrt_four", four),                                # exact 2.0, carry-class
            ("sqrt_1ulp_up", one_ulp_up),
            ("sqrt_1ulp_dn", one_ulp_dn),                       # rounds up to 1.0
            ("sqrt_quarter", sv(0, bias - 2, 0)),               # 0.25 -> 0.5 exact
            ("sqrt_half_inexact", sv(0, bias - 1, 0)),          # odd negative exp
            ("sqrt_2p25", sv(0, bias + 1, 1 << 22)),            # 1.5^2 exact
            # ---- perfect squares on the 2^-11 root grid ----
            ("sqrt_sq_1p2p11", square(0, bias, 1 << 12)),
            ("sqrt_sq_1p2p10", square(0, bias, 3 << 11)),
            ("sqrt_sq_1p2p11_oddexp", square(0, bias - 1, 1 << 12)),
            ("sqrt_sq_1m2p11", square(0, bias, (1 << 23) - (1 << 12))),
            # ---- +-1 ulp around perfect squares ----
            ("sqrt_sq_1p_ulp_up", square(0, bias, 1 << 12) + 1),
            ("sqrt_sq_1p_ulp_dn", square(0, bias, 1 << 12) - 1),
            ("sqrt_four_ulp_dn", four - 1),                     # just below 4: ->2.0 carry
            ("sqrt_four_ulp_up", four + 1),
            # ---- odd/even exponent parity pairs ----
            ("sqrt_1p5_odd", sv(0, bias, 1 << 22)),             # 1.5, E=0
            ("sqrt_3_even", sv(0, bias + 1, 1 << 22)),          # 3.0, E=1
            ("sqrt_parity_exp126", sv(0, bias - 1, 0x654321)),
            ("sqrt_parity_exp127", sv(0, bias, 0x654321)),
            # ---- exponent halving range stress ----
            ("sqrt_maxnorm", max_norm),                         # ~1.34e19, no overflow
            ("sqrt_minnorm", min_norm),                         # 2^-63 exact
            ("sqrt_2minnorm", sv(0, 1, 1)),
            ("sqrt_3minnorm", sv(0, 1, 2)),
            ("sqrt_largest_below4", sv(0, bias + 1, mant_mask)),  # ~4 - 2^-22
            ("sqrt_smallest_above4", sv(0, bias + 2, 1)),         # 4 + 2^-21-ish
            ("sqrt_2p120", sv(0, 120, 0)),                        # 2^60 exact
            ("sqrt_2m120", sv(0, bias - 120 + 1, 0)),             # 2^-60 exact
            ("sqrt_2m126", sv(0, 1, 0)),                          # min normal, 2^-63
        ]
        if self.subnormal_support:
            v += [
                # ---- subnormal input grid (=1 gradual handling) ----
                # NOTE: sqrt never underflows - every one of these lands in
                # the NORMAL range (sqrt(2^-149) ~ 2^-74.5, deep normal grid).
                ("sqrt_minsub", min_sub),                      # E_x=-149 odd
                ("sqrt_minsub4", 4),                           # E_x=-147 odd
                ("sqrt_maxsub", max_sub),                      # E_x=-127 odd
                ("sqrt_sub_3", 3),
                ("sqrt_sub_5", 5),
                ("sqrt_sub_0x400000", 0x00400000),             # E_x=-136 even
                ("sqrt_sub_0x7fffff", 0x007FFFFF),
                ("sqrt_sub_power10", 1 << 10),
                ("sqrt_sub_power22", 1 << 22),
                ("sqrt_sub_near_minnorm_dn", 0x007FFFFF),      # just below min normal
                ("sqrt_minnorm_ulp_up", min_norm + 1),
                ("sqrt_neg_sub", sv(1, 0, 0x54321)),           # qNaN + invalid
            ]
        else:
            v += [
                # ---- FTZ grid (=0): positive subnormal inputs act as +0 ----
                ("ftz_sqrt_minsub", min_sub),
                ("ftz_sqrt_maxsub", max_sub),
                ("ftz_sqrt_sub_3", 3),
                ("ftz_sqrt_neg_minsub", sv(1, 0, 1)),          # -0 (sign kept)
                # tiny normals still produce normal results
                ("ftz_sqrt_minnorm", min_norm),
                ("ftz_sqrt_2minnorm", sv(0, 1, 1)),
            ]
        return v

    # ------------------------------------------------------------------
    # randomized sweep
    # ------------------------------------------------------------------
    def _random_single(self):
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
                                                  1 << 22, (1 << 22) - 1,
                                                  1 << 12, (1 << 23) - (1 << 12)]), fmt)

        r = rng.random()
        if not self.subnormal_support:
            if r < 0.70:
                return any_norm()
            if r < 0.85:
                return mant_extreme()
            if r < 0.93:
                return tiny_norm()
            return subn()                    # FTZ: folded to +0
        # =1 mode: subnormal-heavy mix
        if r < 0.30:
            return subn()
        if r < 0.50:
            return tiny_norm()
        if r < 0.65:
            return near_one()
        if r < 0.80:
            return mant_extreme()
        if r < 0.90:
            s = subn()
            return s | (1 << 31)           # negative subnormal -> qNaN
        return any_norm()

    async def run_comprehensive_tests(self):
        """Directed corners + seeded randomized sweep for this param value."""
        mode = "gradual-underflow" if self.subnormal_support else "ftz-regression"
        self.log.info(f"Starting {mode} sqrt tests "
                      f"(SUBNORMAL_SUPPORT={int(self.subnormal_support)})")

        for name, a in self._directed_vectors():
            await self.test_single_checked(a, f"directed_{name}")

        sweep_n = {'basic': 64, 'medium': 256, 'full': 1024}[self.test_level]
        for i in range(sweep_n):
            a = self._random_single()
            await self.test_single_checked(a, f"sweep_{i}")

        self.log.info(f"Latency: min={self.lat_min} max={self.lat_max} "
                      f"by class {self.lat_by_class}")
        self.print_summary()
        assert self.fail_count == 0, f"{self.fail_count} tests failed"


def get_fp32_sqrt_params():
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
async def fp32_sqrt_test(dut):
    """Directed + seeded-sweep exact-oracle tests for both SUBNORMAL_SUPPORT values."""
    subnormal_support = os.environ.get('SUBNORMAL_SUPPORT', '0') == '1'
    tb = FPSqrtTB(dut, FORMATS['fp32'], subnormal_support)
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'seed changed to {seed}')
    tb.print_settings()
    await tb.setup_clocks_and_reset()
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", get_fp32_sqrt_params())
def test_math_ieee754_2008_fp32_sqrt(request, params):
    """PyTest wrapper for FP32 square root."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common',
        'rtl_math': 'rtl/math'})
    dut_name = "math_ieee754_2008_fp32_sqrt"
    t_name = params['test_level']
    subnormal_support = params['subnormal_support']
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_{t_name}_{reg_level}_sn{int(subnormal_support)}"
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(

        repo_root=repo_root,

        module='math_ieee754_2008_fp32_sqrt'

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
