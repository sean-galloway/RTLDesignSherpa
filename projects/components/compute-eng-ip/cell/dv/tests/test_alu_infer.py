# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_alu_infer
# Purpose: TDD test suite for the ALU-INFER bf16 inference ALU
# Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
# Subsystem: cell
#
# Author: sean galloway
# Created: 2026-10-17

"""ALU-INFER TDD test suite.

Tests are written in strict TDD order:
  1. shell/handshake + copy + exact ROW_LATENCY timing + in-order
  2. add/sub golden
  3. mul
  4. min/max both sub-ops
  5. compare vs B and vs imm + flags format
  6. relu incl. -0/-inf/NaN
  7. mac CLEAR/ACC/DRAIN/HOLD
  8. elastic backpressure
  9. error opcode retires in order
 10. special-value grid
 11. mixed-opcode II=1 soak
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_repo_root, sim_build_path
from TBClasses.shared.test_levels import current_level, level_env, reg_level_grid
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from cov_utils.conftest_coverage import get_coverage_compile_args

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

from TBClasses.common.fp_testing import FPUtils, BF16
from TBClasses.common.bf16_testing import BF16Utils, BF16_SPECIAL_GRID, bf16_special_value_product


_LVL = current_level()
_D = {'gate': dict(seeds=[0xA1]), 'func': dict(seeds=[0, 1, 2, 3, 4, 5, 6, 7])}[_LVL]
_TIMEOUT_US = {'gate': 50, 'func': 200}[_LVL]
_REG_LEVEL = os.environ.get('REG_LEVEL', 'GATE').lower()


def _pack_bf16_line(lane0: int, lane1: int) -> int:
    return ((lane1 & 0xFFFF) << 16) | (lane0 & 0xFFFF)


def _unpack_bf16_line(line: int):
    return line & 0xFFFF, (line >> 16) & 0xFFFF


def _is_subnormal_bf16(x: int) -> bool:
    exp = (x >> 7) & 0xFF
    mant = x & 0x7F
    return (exp == 0) and (mant != 0)


def _ftz_bf16(x: int) -> int:
    """Flush a BF16 subnormal to signed zero; leave other values unchanged."""
    if _is_subnormal_bf16(x):
        return x & 0x8000
    return x


def _func_sel(opcode: int, sub_op: int = 0, reserved: int = 0) -> int:
    return (reserved << 7) | (sub_op << 5) | opcode


async def _apply_reset(dut):
    dut.aresetn.value = 0
    dut.valid.value = 0
    dut.result_ready.value = 0
    dut.op_line_a.value = 0
    dut.op_line_b.value = 0
    dut.threshold_imm.value = 0
    dut.func_sel.value = 0
    dut.acc_ctrl.value = 0
    await Timer(100, unit="ns")
    await RisingEdge(dut.clk)
    dut.aresetn.value = 1
    await RisingEdge(dut.clk)


async def _issue(dut, opcode, a=0, b=0, imm=0, sub_op=0, acc_ctrl=0):
    """Wait for ready, then present one issue-cycle of operands.

    Does not touch result_ready; the caller owns the consumer side.
    """
    dut.valid.value = 1
    dut.func_sel.value = _func_sel(opcode, sub_op)
    dut.op_line_a.value = a
    dut.op_line_b.value = b
    dut.threshold_imm.value = imm
    dut.acc_ctrl.value = acc_ctrl
    while True:
        await ReadOnly()
        if int(dut.ready.value) == 1:
            break
        await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.valid.value = 0


async def _wait_cycles(dut, n):
    for _ in range(n):
        await RisingEdge(dut.clk)


async def _recv_result(dut, timeout_cycles=64):
    """Block until result_valid&&result_ready, then return (line, flags)."""
    dut.result_ready.value = 1
    for _ in range(timeout_cycles):
        await ReadOnly()
        if int(dut.result_valid.value) == 1 and int(dut.result_ready.value) == 1:
            line = int(dut.result_line.value)
            flags = int(dut.result_flags.value)
            await RisingEdge(dut.clk)
            dut.result_ready.value = 0
            return line, flags
        await RisingEdge(dut.clk)
    raise AssertionError("Timeout waiting for result")


def _bf16_to_float(x: int) -> float:
    return BF16Utils.bf16_to_float(x)


def _float_to_bf16(x: float) -> int:
    return BF16Utils.float_to_bf16_rne(x)


def _expected_add(a: int, b: int) -> int:
    a = _ftz_bf16(a)
    b = _ftz_bf16(b)
    return _ftz_bf16(_float_to_bf16(_bf16_to_float(a) + _bf16_to_float(b)))


def _expected_sub(a: int, b: int) -> int:
    a = _ftz_bf16(a)
    b = _ftz_bf16(b)
    return _ftz_bf16(_float_to_bf16(_bf16_to_float(a) - _bf16_to_float(b)))


def _expected_mul(a: int, b: int) -> int:
    a = _ftz_bf16(a)
    b = _ftz_bf16(b)
    return _ftz_bf16(_float_to_bf16(_bf16_to_float(a) * _bf16_to_float(b)))


def _expected_min(a: int, b: int) -> int:
    fa, fb = _bf16_to_float(a), _bf16_to_float(b)
    # Match math_bf16_min NaN propagation: NaN returns the non-NaN operand.
    if BF16Utils.bf16_is_nan(a) and BF16Utils.bf16_is_nan(b):
        return a
    if BF16Utils.bf16_is_nan(a):
        return b
    if BF16Utils.bf16_is_nan(b):
        return a
    # Signed zeros: min returns -0 iff at least one operand is -0.
    if fa == 0.0 and fb == 0.0:
        return 0x8000 if ((a & 0x8000) | (b & 0x8000)) else 0x0000
    return _float_to_bf16(min(fa, fb))


def _expected_max(a: int, b: int) -> int:
    fa, fb = _bf16_to_float(a), _bf16_to_float(b)
    if BF16Utils.bf16_is_nan(a) and BF16Utils.bf16_is_nan(b):
        return a
    if BF16Utils.bf16_is_nan(a):
        return b
    if BF16Utils.bf16_is_nan(b):
        return a
    # Signed zeros: max returns -0 only when both operands are -0.
    if fa == 0.0 and fb == 0.0:
        return 0x8000 if ((a & 0x8000) & (b & 0x8000)) else 0x0000
    return _float_to_bf16(max(fa, fb))


def _expected_relu(a: int) -> int:
    if BF16Utils.bf16_is_nan(a):
        return a
    if a & 0x8000:
        return 0x0000
    return a


def _fp32_fma(a_bf16: int, b_bf16: int, c_fp32: int) -> int:
    """Return FP32 accumulator update, matching the math_bf16_fma library contract.

    The product of two BF16 values is exact in doubles.  Per the library
    (math_bf16_fma.sv), a product whose unbiased exponent is below the FP32
    minimum-normal range (|product| < 2^-126, w_prod_exp_adj < 1) is flushed
    to zero BEFORE the addend is applied, and an underflowed-product result
    returns the addend verbatim (w_prod_is_zero -> ow_result = i_c).  IEEE
    fused rounding would instead keep the product sign on the rounded zero;
    the ALU inherits the library's contract (the same proven-contract
    discipline as the adder/multiplier 1-ULP tolerance).  Otherwise the only
    rounding is the FP32 add.  Result is returned as FP32 bits.
    """
    prod = _bf16_to_float(a_bf16) * _bf16_to_float(b_bf16)
    acc = BF16Utils.fp32_to_float(c_fp32)
    if prod != 0.0 and abs(prod) < 2.0**-126:
        # Library FTZ on the product: result is the addend verbatim.
        return c_fp32
    sum_val = prod + acc
    # Clamp finite overflow to infinity so struct.pack never raises.
    if sum_val > 3.4028234e38:
        sum_val = float('inf')
    elif sum_val < -3.4028234e38:
        sum_val = float('-inf')
    return BF16Utils.float_to_fp32(sum_val)


def _bf16_from_fp32(fp32: int) -> int:
    return _float_to_bf16(BF16Utils.fp32_to_float(fp32))


def _bf16_is_nan(x: int) -> bool:
    return BF16Utils.bf16_is_nan(x)


def _bf16_match(a: int, b: int) -> bool:
    """Bit-exact BF16 comparison with NaN equivalence (sign/payload ignored)."""
    if _bf16_is_nan(a) and _bf16_is_nan(b):
        return True
    return a == b


def _bf16_is_zero(x: int) -> bool:
    return BF16Utils.bf16_is_zero(x)


def _bf16_is_inf(x: int) -> bool:
    return BF16Utils.bf16_is_inf(x)


def _bf16_ulp_diff(a: int, b: int) -> int:
    """Absolute ULP difference ignoring sign/payload; safe for NaN/special."""
    return abs((a & 0x7FFF) - (b & 0x7FFF))


def _bf16_addsub_match(got: int, exp: int, a: int, b: int) -> bool:
    """Match add/sub result to golden, matching BF16AdderTB contract.

    Exact match for NaN/special/zero/inf and for normal values.  Up to 1 ULP
    is tolerated only when |exp_a - exp_b| > 3 AND signs match, reflecting
    the library adder's 11-bit alignment precision limit (loses the tie-break
    bit for large exponent differences).  This is the same contract proven in
    bin/TBClasses/common/bf16_testing.py::BF16AdderTB.test_single_add.
    """
    if _bf16_is_nan(got) and _bf16_is_nan(exp):
        return True
    if got == exp:
        return True
    got_special = _bf16_is_zero(got) or _bf16_is_inf(got)
    exp_special = _bf16_is_zero(exp) or _bf16_is_inf(exp)
    if got_special or exp_special:
        return False
    exp_a = (a >> 7) & 0xFF
    exp_b = (b >> 7) & 0xFF
    if abs(exp_a - exp_b) <= 3:
        return False
    sign_match = (got >> 15) == (exp >> 15)
    return sign_match and _bf16_ulp_diff(got, exp) <= 1


def _bf16_mul_match(got: int, exp: int) -> bool:
    """Match mul result to golden, matching BF16MultiplierTB contract.

    Exact match for NaN/special/zero/inf.  Up to 1 ULP is tolerated for normal
    values when signs match.  This mirrors
    bin/TBClasses/common/bf16_testing.py::BF16MultiplierTB.test_single_mult.
    """
    if _bf16_is_nan(got) and _bf16_is_nan(exp):
        return True
    if got == exp:
        return True
    got_special = _bf16_is_zero(got) or _bf16_is_inf(got)
    exp_special = _bf16_is_zero(exp) or _bf16_is_inf(exp)
    if got_special or exp_special:
        return False
    sign_match = (got >> 15) == (exp >> 15)
    return sign_match and _bf16_ulp_diff(got, exp) <= 1


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_copy_timing(dut):
    """Test 1: shell/handshake, copy opcode, exact ROW_LATENCY timing, in-order."""
    log = dut._log
    log.info("=" * 80)
    log.info("Test 1: copy + handshake + ROW_LATENCY timing")
    log.info("=" * 80)

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    row_latency = int(os.environ.get('ROW_LATENCY', '4'))

    # Hold result_ready high so the pipeline drains; this proves II=1.
    dut.result_ready.value = 1

    # Single copy: result arrives exactly ROW_LATENCY cycles after the issue
    # edge.  _issue returns at the issue edge, so wait ROW_LATENCY cycles.
    a0 = _pack_bf16_line(0x3F80, 0x4000)  # 1.0, 2.0
    await _issue(dut, opcode=0, a=a0)
    await _wait_cycles(dut, row_latency)
    await ReadOnly()
    assert int(dut.result_valid.value) == 1, "result_valid not asserted at ROW_LATENCY"
    assert int(dut.result_line.value) == a0, f"copy result mismatch: got 0x{int(dut.result_line.value):08X}"
    assert int(dut.result_flags.value) == 0
    await RisingEdge(dut.clk)

    # Back-to-back copies: fill the pipeline (ROW_LATENCY in flight) and then
    # drain, checking exact latency and in-order delivery.
    num = row_latency
    sent = []
    for i in range(num):
        a = _pack_bf16_line(0x3F80 + i, 0x4000 + i)
        sent.append(a)
        await _issue(dut, opcode=0, a=a)

    # The first burst result arrives one cycle after the last issue edge (the
    # pipeline is full, so the head result is ready on the next cycle).
    await RisingEdge(dut.clk)
    for i in range(num):
        await ReadOnly()
        assert int(dut.result_valid.value) == 1, f"copy {i} result_valid missing"
        line = int(dut.result_line.value)
        assert line == sent[i], f"copy {i} mismatch: got 0x{line:08X}, exp 0x{sent[i]:08X}"
        assert int(dut.result_flags.value) == 0
        if i != num - 1:
            await RisingEdge(dut.clk)

    log.info(f"Test 1 PASSED (ROW_LATENCY={row_latency})")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_add_sub(dut):
    """Test 2: add/sub golden against Python float RNE reference."""
    log = dut._log
    log.info("Test 2: add/sub golden")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    cases = [
        (0x3F80, 0x4000, _expected_add),  # 1 + 2
        (0x3F80, 0xBF80, _expected_add),  # 1 + -1
        (0x4000, 0x3F80, _expected_sub),  # 2 - 1
        (0x3F80, 0x4000, _expected_sub),  # 1 - 2
        (0x4040, 0x3F80, _expected_add),  # 3 + 1
        (0xC000, 0x4000, _expected_add),  # -2 + 2
    ]

    for a_lane0, b_lane0, golden in cases:
        a_lane1 = a_lane0 ^ 0x8000  # opposite sign in lane 1 for variety
        a = _pack_bf16_line(a_lane0, a_lane1)
        b = _pack_bf16_line(b_lane0, b_lane0)
        opcode = 1 if golden is _expected_add else 2
        expected = _pack_bf16_line(golden(a_lane0, b_lane0), golden(a_lane1, b_lane0))

        await _issue(dut, opcode=opcode, a=a, b=b)
        line, flags = await _recv_result(dut)
        g0, e0 = line & 0xFFFF, expected & 0xFFFF
        g1, e1 = (line >> 16) & 0xFFFF, (expected >> 16) & 0xFFFF
        assert _bf16_addsub_match(g0, e0, a_lane0, b_lane0) and \
               _bf16_addsub_match(g1, e1, a_lane1, b_lane0), \
            f"{golden.__name__} mismatch: got 0x{line:08X}, exp 0x{expected:08X}"
        assert flags == 0

    log.info("Test 2 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_mul(dut):
    """Test 3: mul golden against Python float RNE reference."""
    log = dut._log
    log.info("Test 3: mul golden")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    cases = [
        (0x3F80, 0x4000),  # 1 * 2
        (0x4000, 0x4000),  # 2 * 2
        (0xBF80, 0x4000),  # -1 * 2
        (0x3F00, 0x4000),  # 0.5 * 2
        (0x0000, 0x7F80),  # 0 * inf
        (0x7F80, 0x7F80),  # inf * inf
    ]

    for a_lane0, b_lane0 in cases:
        a = _pack_bf16_line(a_lane0, a_lane0)
        b = _pack_bf16_line(b_lane0, b_lane0)
        expected = _pack_bf16_line(_expected_mul(a_lane0, b_lane0),
                                   _expected_mul(a_lane0, b_lane0))
        await _issue(dut, opcode=3, a=a, b=b)
        line, flags = await _recv_result(dut)
        g0, e0 = line & 0xFFFF, expected & 0xFFFF
        g1, e1 = (line >> 16) & 0xFFFF, (expected >> 16) & 0xFFFF
        assert _bf16_mul_match(g0, e0) and _bf16_mul_match(g1, e1), \
            f"mul mismatch: got 0x{line:08X}, exp 0x{expected:08X}"
        assert flags == 0

    log.info("Test 3 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_minmax(dut):
    """Test 4: min/max both sub-ops."""
    log = dut._log
    log.info("Test 4: min/max")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    cases = [
        (0x4000, 0x3F80),  # 2, 1
        (0xBF80, 0x3F80),  # -1, 1
        (0x7F80, 0x3F80),  # inf, 1
        (0x7FC0, 0x3F80),  # NaN, 1
    ]

    for a_lane0, b_lane0 in cases:
        a = _pack_bf16_line(a_lane0, b_lane0)
        b = _pack_bf16_line(b_lane0, a_lane0)
        exp_min = _pack_bf16_line(_expected_min(a_lane0, b_lane0),
                                  _expected_min(b_lane0, a_lane0))
        exp_max = _pack_bf16_line(_expected_max(a_lane0, b_lane0),
                                  _expected_max(b_lane0, a_lane0))

        await _issue(dut, opcode=5, sub_op=0, a=a, b=b)
        line, flags = await _recv_result(dut)
        assert line == exp_min, f"min mismatch: got 0x{line:08X}, exp 0x{exp_min:08X}"
        assert flags == 0

        await _issue(dut, opcode=5, sub_op=1, a=a, b=b)
        line, flags = await _recv_result(dut)
        assert line == exp_max, f"max mismatch: got 0x{line:08X}, exp 0x{exp_max:08X}"
        assert flags == 0

    log.info("Test 4 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_compare(dut):
    """Test 5: compare vs B and vs imm; flags packed low."""
    log = dut._log
    log.info("Test 5: compare")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    cases_vs_b = [
        (_pack_bf16_line(0x3F80, 0x4000), _pack_bf16_line(0x4000, 0x3F80)),  # lane0: 1<2, lane1: 2>1
        (_pack_bf16_line(0x7FC0, 0x3F80), _pack_bf16_line(0x3F80, 0x7FC0)),  # NaN unordered
    ]

    for a, b in cases_vs_b:
        a0, a1 = _unpack_bf16_line(a)
        b0, b1 = _unpack_bf16_line(b)
        exp_flags = ((1 if _bf16_to_float(a1) < _bf16_to_float(b1) else 0) << 1) | \
                    (1 if _bf16_to_float(a0) < _bf16_to_float(b0) else 0)

        await _issue(dut, opcode=6, sub_op=0, a=a, b=b)
        line, flags = await _recv_result(dut)
        assert line == 0, f"compare result_line must be zero, got 0x{line:08X}"
        assert (flags & 0x3) == exp_flags, f"compare flags mismatch: got 0x{flags:08X}, exp 0x{exp_flags:08X}"

    # Compare vs immediate: lane 0 = 1.0 < 2.0, lane 1 = 2.0 < 2.0 (false).
    a = _pack_bf16_line(0x3F80, 0x4000)
    imm = 0x4000
    exp_flags = 0x1  # only lane0 is less
    await _issue(dut, opcode=6, sub_op=1, a=a, imm=imm)
    line, flags = await _recv_result(dut)
    assert line == 0
    assert (flags & 0x3) == exp_flags

    log.info("Test 5 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_relu(dut):
    """Test 6: relu incl. negative, -0, +0, -inf, NaN."""
    log = dut._log
    log.info("Test 6: relu")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    cases = [
        _pack_bf16_line(0x3F80, 0xBF80),  # 1.0, -1.0
        _pack_bf16_line(0x0000, 0x8000),  # +0, -0
        _pack_bf16_line(0xFF80, 0x7FC0),  # -inf, NaN
    ]

    for a in cases:
        a0, a1 = _unpack_bf16_line(a)
        expected = _pack_bf16_line(_expected_relu(a0), _expected_relu(a1))
        await _issue(dut, opcode=7, a=a)
        line, flags = await _recv_result(dut)
        assert line == expected, f"relu mismatch: got 0x{line:08X}, exp 0x{expected:08X}"
        assert flags == 0

    log.info("Test 6 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_mac(dut):
    """Test 7: mac CLEAR/ACC/DRAIN/HOLD with FP32 accumulator."""
    log = dut._log
    log.info("Test 7: mac CLEAR/ACC/DRAIN/HOLD")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    def pack(a0, a1):
        return _pack_bf16_line(a0, a1)

    # CLEAR -> result should be +0.
    await _issue(dut, opcode=4, a=0, b=0, acc_ctrl=2)
    line, flags = await _recv_result(dut)
    assert line == 0, f"CLEAR result mismatch: got 0x{line:08X}"
    assert flags == 0

    acc = 0
    # ACC 2.0 * 1.0 -> acc = 2.0
    a = pack(0x4000, 0x4000)
    b = pack(0x3F80, 0x3F80)
    acc = _fp32_fma(0x4000, 0x3F80, acc)
    exp = _bf16_from_fp32(acc)
    await _issue(dut, opcode=4, a=a, b=b, acc_ctrl=1)
    line, flags = await _recv_result(dut)
    assert line == (exp << 16) | exp, f"ACC mismatch: got 0x{line:08X}, exp 0x{(exp << 16) | exp:08X}"
    assert flags == 0

    # ACC 1.0 * 1.0 -> acc = 3.0
    a = pack(0x3F80, 0x3F80)
    b = pack(0x3F80, 0x3F80)
    acc = _fp32_fma(0x3F80, 0x3F80, acc)
    exp = _bf16_from_fp32(acc)
    await _issue(dut, opcode=4, a=a, b=b, acc_ctrl=1)
    line, flags = await _recv_result(dut)
    assert line == (exp << 16) | exp
    assert flags == 0

    # DRAIN -> acc unchanged, result is rounded acc.
    await _issue(dut, opcode=4, a=0, b=0, acc_ctrl=3)
    line, flags = await _recv_result(dut)
    assert line == (exp << 16) | exp
    assert flags == 0

    # HOLD -> same.
    await _issue(dut, opcode=4, a=0, b=0, acc_ctrl=0)
    line, flags = await _recv_result(dut)
    assert line == (exp << 16) | exp
    assert flags == 0

    log.info("Test 7 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_backpressure(dut):
    """Test 8: elastic backpressure holds results and resumes in order."""
    log = dut._log
    log.info("Test 8: elastic backpressure")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    # Issue three copies; after the first result appears, stall the consumer.
    sent = [_pack_bf16_line(0x3F80 + i, 0x4000 + i) for i in range(3)]
    for a in sent:
        await _issue(dut, opcode=0, a=a)

    # Wait for the first result, then hold result_ready low for several cycles.
    while True:
        await ReadOnly()
        if int(dut.result_valid.value) == 1:
            first = int(dut.result_line.value)
            break
        await RisingEdge(dut.clk)
    assert first == sent[0]

    await RisingEdge(dut.clk)
    dut.result_ready.value = 0
    await _wait_cycles(dut, 5)

    # Result should still be offered and unchanged.
    await ReadOnly()
    assert int(dut.result_valid.value) == 1
    assert int(dut.result_line.value) == sent[0]

    # Drain the remaining results in order.
    await RisingEdge(dut.clk)
    dut.result_ready.value = 1
    for i in range(3):
        await ReadOnly()
        assert int(dut.result_valid.value) == 1, f"result {i} missing"
        assert int(dut.result_line.value) == sent[i], f"result {i} mismatch"
        await RisingEdge(dut.clk)
    dut.result_ready.value = 0

    log.info("Test 8 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_error_opcode(dut):
    """Test 9: out-of-range opcode retires in order and returns zero."""
    log = dut._log
    log.info("Test 9: error opcode retirement")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    sent = [
        (_pack_bf16_line(0x3F80, 0x4000), 0, 0),   # copy 1.0, 2.0
        (_pack_bf16_line(0x0000, 0x0000), 8, 0),   # invalid opcode -> zero
        (_pack_bf16_line(0x4040, 0x4080), 0, 0),   # copy 3.0, 4.0
    ]

    for a, opcode, sub_op in sent:
        await _issue(dut, opcode=opcode, sub_op=sub_op, a=a)

    expected = [sent[0][0], 0x00000000, sent[2][0]]
    for i, exp in enumerate(expected):
        line, flags = await _recv_result(dut)
        assert line == exp, f"result {i} mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
        assert flags == 0, f"result {i} flags mismatch: got 0x{flags:08X}"

    log.info("Test 9 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_special_grid(dut):
    """Test 10: special-value grid for add/sub/mul/minmax/compare/relu."""
    log = dut._log
    log.info("Test 10: special-value grid")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    grid = BF16_SPECIAL_GRID

    # Gate: small deterministic cross-section; func: exhaustive grid.
    if _LVL == 'gate':
        pairs = [
            (0, 0), (0, 1), (1, 4), (4, 4), (7, 8),
            (2, 3), (5, 6), (0, 7), (8, 8),
        ]
    else:
        pairs = [(i, j) for i in range(len(grid)) for j in range(len(grid))]

    def grid_value(idx):
        return grid[idx][1]

    for i, j in pairs:
        a0 = grid_value(i)
        b0 = grid_value(j)
        a1 = grid_value(j)
        b1 = grid_value(i)
        a = _pack_bf16_line(a0, a1)
        b = _pack_bf16_line(b0, b1)

        # add/sub: math_bf16_adder flushes subnormal inputs/outputs (FTZ).
        if not (_is_subnormal_bf16(a0) or _is_subnormal_bf16(b0) or _is_subnormal_bf16(a1) or _is_subnormal_bf16(b1)):
            exp = _pack_bf16_line(_expected_add(a0, b0), _expected_add(a1, b1))
            await _issue(dut, opcode=1, a=a, b=b)
            line, flags = await _recv_result(dut)
            assert _bf16_addsub_match(line & 0xFFFF, exp & 0xFFFF, a0, b0) and \
                   _bf16_addsub_match((line >> 16) & 0xFFFF, (exp >> 16) & 0xFFFF, a1, b1), \
                f"add grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
            assert flags == 0

            exp = _pack_bf16_line(_expected_sub(a0, b0), _expected_sub(a1, b1))
            await _issue(dut, opcode=2, a=a, b=b)
            line, flags = await _recv_result(dut)
            assert _bf16_addsub_match(line & 0xFFFF, exp & 0xFFFF, a0, b0) and \
                   _bf16_addsub_match((line >> 16) & 0xFFFF, (exp >> 16) & 0xFFFF, a1, b1), \
                f"sub grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
            assert flags == 0

        # mul: math_bf16_multiplier flushes subnormal inputs (FTZ).
        if not (_is_subnormal_bf16(a0) or _is_subnormal_bf16(b0) or _is_subnormal_bf16(a1) or _is_subnormal_bf16(b1)):
            exp = _pack_bf16_line(_expected_mul(a0, b0), _expected_mul(a1, b1))
            await _issue(dut, opcode=3, a=a, b=b)
            line, flags = await _recv_result(dut)
            assert _bf16_mul_match(line & 0xFFFF, exp & 0xFFFF) and \
                   _bf16_mul_match((line >> 16) & 0xFFFF, (exp >> 16) & 0xFFFF), \
                f"mul grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
            assert flags == 0

        # min
        exp = _pack_bf16_line(_expected_min(a0, b0), _expected_min(a1, b1))
        await _issue(dut, opcode=5, sub_op=0, a=a, b=b)
        line, flags = await _recv_result(dut)
        assert line == exp, f"min grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
        assert flags == 0

        # max
        exp = _pack_bf16_line(_expected_max(a0, b0), _expected_max(a1, b1))
        await _issue(dut, opcode=5, sub_op=1, a=a, b=b)
        line, flags = await _recv_result(dut)
        assert line == exp, f"max grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
        assert flags == 0

        # relu on operand A
        exp = _pack_bf16_line(_expected_relu(a0), _expected_relu(a1))
        await _issue(dut, opcode=7, a=a)
        line, flags = await _recv_result(dut)
        assert line == exp, f"relu grid ({i},{j}) mismatch: got 0x{line:08X}, exp 0x{exp:08X}"
        assert flags == 0

        # compare vs B: flags packed low, NaN unordered -> False.
        exp_flags = ((1 if _bf16_to_float(a1) < _bf16_to_float(b1) else 0) << 1) | \
                    (1 if _bf16_to_float(a0) < _bf16_to_float(b0) else 0)
        await _issue(dut, opcode=6, sub_op=0, a=a, b=b)
        line, flags = await _recv_result(dut)
        assert line == 0, f"compare grid ({i},{j}) result_line must be zero"
        assert (flags & 0x3) == exp_flags, f"compare grid ({i},{j}) flags mismatch: got 0x{flags:08X}, exp 0x{exp_flags:08X}"

    log.info("Test 10 PASSED")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_mixed_soak(dut):
    """Test 11: random mixed-opcode sequence retires in-order with golden check."""
    log = dut._log
    log.info("Test 11: mixed-opcode II=1 soak")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    count = {'gate': 32, 'func': 256}[_LVL]

    def rand_bf16():
        # Random 16-bit pattern excluding subnormals, which the BF16 rows
        # flush to zero (FTZ).
        while True:
            v = random.randint(0, 0xFFFF)
            if not _is_subnormal_bf16(v):
                return v

    for seed in _D['seeds']:
        random.seed(seed)

        # Per-lane FP32 accumulator state for MAC ops; reset each seed.  The
        # DUT's accumulator is architectural state and survives across the
        # seed loop (it clears only on acc_ctrl CLEAR or reset), so align the
        # hardware with the golden model by issuing one CLEAR mac before each
        # seed's sequence and draining its don't-care result.
        acc = [0, 0]
        await _issue(dut, opcode=4, a=0, b=0, acc_ctrl=2)
        await _recv_result(dut)

        def expected(opcode, sub_op, a, b, imm):
            a0, a1 = _unpack_bf16_line(a)
            b0, b1 = _unpack_bf16_line(b)
            nonlocal acc
            if opcode == 0:
                return a, 0
            elif opcode == 1:
                return _pack_bf16_line(_expected_add(a0, b0), _expected_add(a1, b1)), 0
            elif opcode == 2:
                return _pack_bf16_line(_expected_sub(a0, b0), _expected_sub(a1, b1)), 0
            elif opcode == 3:
                return _pack_bf16_line(_expected_mul(a0, b0), _expected_mul(a1, b1)), 0
            elif opcode == 4:
                # MAC: update accumulator and return BF16 view.
                for lane in range(2):
                    if acc_ctrl == 2:
                        acc[lane] = 0
                    elif acc_ctrl == 1:
                        acc[lane] = _fp32_fma(a0 if lane == 0 else a1,
                                              b0 if lane == 0 else b1,
                                              acc[lane])
                    # HOLD/DRAIN: acc unchanged
                return _pack_bf16_line(_bf16_from_fp32(acc[0]), _bf16_from_fp32(acc[1])), 0
            elif opcode == 5:
                if sub_op == 0:
                    return _pack_bf16_line(_expected_min(a0, b0), _expected_min(a1, b1)), 0
                else:
                    return _pack_bf16_line(_expected_max(a0, b0), _expected_max(a1, b1)), 0
            elif opcode == 6:
                exp_flags = ((1 if _bf16_to_float(a1) < _bf16_to_float(b1 if sub_op == 0 else imm) else 0) << 1) | \
                            (1 if _bf16_to_float(a0) < _bf16_to_float(b0 if sub_op == 0 else imm) else 0)
                return 0, exp_flags
            elif opcode == 7:
                return _pack_bf16_line(_expected_relu(a0), _expected_relu(a1)), 0
            else:
                return 0, 0

        issued = []
        results = []

        # Issue/drain mixed opcodes in order.  Each issue is followed by its
        # result receive, so the test is a functional soak; Test 1 already
        # proves the pipeline can sustain II=1 for copy.
        for idx in range(count):
            a = rand_bf16()
            b = rand_bf16()
            imm = rand_bf16() & 0xFFFF
            opcode = random.choice([0, 1, 2, 3, 4, 5, 6, 7, 8])
            sub_op = random.choice([0, 1])
            acc_ctrl = random.choice([0, 1, 2, 3])

            exp_line, exp_flags = expected(opcode, sub_op, a, b, imm)
            issued.append((opcode, sub_op, a, b, imm, acc_ctrl, exp_line, exp_flags))

            await _issue(dut, opcode=opcode, sub_op=sub_op, a=a, b=b, imm=imm, acc_ctrl=acc_ctrl)
            line, flags = await _recv_result(dut)
            results.append((line, flags))

        assert len(results) == count
        for i, (opcode, sub_op, a, b, imm, acc_ctrl, exp_line, exp_flags) in enumerate(issued):
            line, flags = results[i]
            a0, a1 = _unpack_bf16_line(a)
            b0, b1 = _unpack_bf16_line(b)
            if opcode in [1, 2]:
                assert _bf16_addsub_match(line & 0xFFFF, exp_line & 0xFFFF, a0, b0) and \
                       _bf16_addsub_match((line >> 16) & 0xFFFF, (exp_line >> 16) & 0xFFFF, a1, b1), \
                    f"seed={seed} soak {i} opcode={opcode} mismatch: got 0x{line:08X}, exp 0x{exp_line:08X}"
            elif opcode == 3:
                assert _bf16_mul_match(line & 0xFFFF, exp_line & 0xFFFF) and \
                       _bf16_mul_match((line >> 16) & 0xFFFF, (exp_line >> 16) & 0xFFFF), \
                    f"seed={seed} soak {i} opcode={opcode} mismatch: got 0x{line:08X}, exp 0x{exp_line:08X}"
            else:
                if line != exp_line:
                    log.error(f"MAC mismatch soak {i} seed={seed}: got 0x{line:08X}, exp 0x{exp_line:08X}")
                    log.error(f"  operands a=0x{a:08X} b=0x{b:08X} acc_ctrl={acc_ctrl}")
                    log.error(f"  acc_bank[0]=0x{int(dut.u_rows.u_acc.acc_bank[0].value):08X} acc_bank[1]=0x{int(dut.u_rows.u_acc.acc_bank[1].value):08X}")
                    log.error(f"  next_acc_bank[0]=0x{int(dut.u_rows.u_acc.next_acc_bank[0].value):08X} next_acc_bank[1]=0x{int(dut.u_rows.u_acc.next_acc_bank[1].value):08X}")
                    log.error(f"  fma_result[0]=0x{int(dut.u_rows.u_acc.fma_result[0].value):08X} fma_result[1]=0x{int(dut.u_rows.u_acc.fma_result[1].value):08X}")
                assert line == exp_line, \
                    f"seed={seed} soak {i} opcode={opcode} mismatch: got 0x{line:08X}, exp 0x{exp_line:08X}"
            assert (flags & 0x3) == (exp_flags & 0x3), \
                f"seed={seed} soak {i} opcode={opcode} flags mismatch: got 0x{flags:08X}, exp 0x{exp_flags:08X}"

    log.info(f"Test 11 PASSED ({len(_D['seeds'])} seeds)")


@cocotb.test(timeout_time=_TIMEOUT_US, timeout_unit='us')
async def cocotb_test_alu_infer_sub_ulp_corner(dut):
    """Test 12: directed SUB corner that exposes the library adder's 1-ULP tolerance.

    a = 0x78E5, b = 0x7611: exponent delta is |0xF1 - 0xEC| = 5 (>3), so the
    library adder's 11-bit alignment can lose the tie-break bit.  Exact IEEE
    RNE for the subtraction is 0x78E0; the library-accepted hardware result is
    0x78E1 (1 ULP high).  This test documents that the ALU-INFER DV contract
    matches the library adder's proven contract, not a strict bit-exact RNE
    reference.
    """
    log = dut._log
    log.info("Test 12: SUB 1-ULP corner (large exponent delta)")

    clk = Clock(dut.clk, 10, unit="ns")
    cocotb.start_soon(clk.start())
    await _apply_reset(dut)

    a_lane0, b_lane0 = 0x78E5, 0x7611
    a = _pack_bf16_line(a_lane0, a_lane0)
    b = _pack_bf16_line(b_lane0, b_lane0)
    exact_rne = _expected_sub(a_lane0, b_lane0)  # 0x78E0
    library_accepted = 0x78E1

    log.info(f"  exact RNE = 0x{exact_rne:04X}; library-accepted = 0x{library_accepted:04X}")

    await _issue(dut, opcode=2, a=a, b=b)
    line, flags = await _recv_result(dut)
    got_lane0 = line & 0xFFFF
    got_lane1 = (line >> 16) & 0xFFFF

    # The DUT must be within the 1-ULP tolerance for large exponent-delta SUB.
    assert _bf16_addsub_match(got_lane0, exact_rne, a_lane0, b_lane0), \
        f"SUB corner lane0 mismatch: got 0x{got_lane0:04X}, exact RNE 0x{exact_rne:04X}"
    assert _bf16_addsub_match(got_lane1, exact_rne, a_lane0, b_lane0), \
        f"SUB corner lane1 mismatch: got 0x{got_lane1:04X}, exact RNE 0x{exact_rne:04X}"
    assert flags == 0

    log.info(f"Test 12 PASSED (got 0x{got_lane0:04X})")


@pytest.mark.parametrize("row_latency", ['4', '6'])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alu_infer(request, test_level, row_latency):
    """Pytest wrapper for ALU-INFER tests."""
    enable_waves = bool(int(os.environ.get('WAVES', '0')))

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/compute-eng-ip/cell/rtl/filelists/alu_infer_top.f')

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-UNUSEDPARAM",
        "-Wno-UNUSEDSIGNAL",
    ]
    for inc in includes:
        compile_args.append(f"+incdir+{inc}")
    compile_args.extend(get_coverage_compile_args())

    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    test_name = f'{module}_{test_level}_rl{row_latency}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="alu_infer_top",
        module=module,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
        parameters={'ROW_LATENCY': row_latency},
        extra_env={**level_env(test_level), 'ROW_LATENCY': row_latency},
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
