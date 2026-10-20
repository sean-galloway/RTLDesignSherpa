# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: alu_infer_golden
# Purpose: Golden models for the ALU-INFER element formats and row families,
#          built on the rtl/math library's own reference models
# Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
# Subsystem: alu-infer
#
# Author: sean galloway
# Created: 2026-10-20

"""Golden models for the extended ALU-INFER rows.

Every floating-point row instantiates an rtl/math block, so its expected
value comes from the SAME reference model that block's own unit test uses
(bin/TBClasses/common/fp_testing.py and bf16_testing.py), with that test's
tolerance.  This is the MAS's built-in cross-check: an ALU/library divergence
is a wiring bug in exactly one of them.  The reference classes are TB classes;
their compute_expected methods only read format attributes, so a DUT-less
instance (``cls.__new__`` plus those attributes) evaluates them.

The int8 rows have no library block; their model is the saturating integer
arithmetic the MAS specifies, exactly.
"""

import os
import sys

from TBClasses.common.fp_testing import (
    FORMATS, FPUtils, FPAdderTB, FPMultiplierTB, FPComparatorTB, FPMaxMinTB,
    FPReluTB, FPLeakyReluTB, FPFMATB, FPSigmoidTB, FPTanhTB, FPGeluTB, FPSiluTB,
    FPConversionTB,
)
from TBClasses.common.bf16_testing import (
    BF16ReciprocalTB, BF16Exp2TB, BF16Log2TB, BF16Log2ScaleTB, BF16ScaleToInt8TB,
    IntToBF16TB,
)
from TBClasses.shared.utilities import get_repo_root

# The PWL table builder and bit-level row model live with the tool.
sys.path.insert(0, os.path.join(get_repo_root(),
                                'projects/components/compute-eng-ip/alu-infer/bin'))
import alu_infer_pwl as pwl  # noqa: E402

# ----------------------------------------------------------------------------
# Encodings (rtl/includes/alu_infer_pkg.sv)
# ----------------------------------------------------------------------------
FMT_BF16, FMT_INT8, FMT_FP32, FMT_FP8 = 0, 1, 2, 3
FMT_NAMES = {FMT_BF16: 'bf16', FMT_INT8: 'int8', FMT_FP32: 'fp32', FMT_FP8: 'fp8'}
LANE_BITS = {FMT_BF16: 16, FMT_INT8: 8, FMT_FP32: 32, FMT_FP8: 8}
FP_FORMAT = {FMT_BF16: FORMATS['bf16'], FMT_FP32: FORMATS['fp32'],
             FMT_FP8: FORMATS['fp8_e4m3']}

OP_COPY, OP_ADD, OP_SUB, OP_MUL, OP_MAC, OP_MINMAX, OP_CMP, OP_RELU = range(8)
OP_REDUCE, OP_PWL, OP_PWL_LUT, OP_CONST = 8, 9, 10, 11
OP_LEAKY, OP_GELU, OP_SIGMOID, OP_SILU, OP_TANH = 12, 13, 14, 15, 16
OP_RECIP, OP_EXP2, OP_LOG2, OP_QSCALE = 17, 18, 19, 20
OP_CVT, OP_ALTFMT = 21, 22

ACC_HOLD, ACC_ACCUM, ACC_CLEAR, ACC_DRAIN = 0, 1, 2, 3

ACT_OPS = (OP_LEAKY, OP_GELU, OP_SIGMOID, OP_SILU, OP_TANH)
BF16_ONLY_OPS = (OP_RECIP, OP_EXP2, OP_LOG2, OP_QSCALE)

# CVT pairs with a library converter (src, dst); same-format is a copy.
CVT_PAIRS = [(FMT_BF16, FMT_INT8), (FMT_BF16, FMT_FP32), (FMT_BF16, FMT_FP8),
             (FMT_INT8, FMT_BF16), (FMT_FP32, FMT_BF16), (FMT_FP32, FMT_FP8),
             (FMT_FP8, FMT_BF16), (FMT_FP8, FMT_FP32)]
CVT_ILLEGAL = [(FMT_INT8, FMT_FP32), (FMT_INT8, FMT_FP8), (FMT_FP32, FMT_INT8),
               (FMT_FP8, FMT_INT8)]


def func_sel(opcode: int, sub_op: int = 0, fmt: int = FMT_BF16) -> int:
    return ((fmt & 3) << 7) | ((sub_op & 3) << 5) | (opcode & 0x1F)


# ----------------------------------------------------------------------------
# Lanes
# ----------------------------------------------------------------------------


def n_lanes(fmt: int, line_w: int = 32) -> int:
    return line_w // LANE_BITS[fmt]


def split(line: int, fmt: int, line_w: int = 32) -> list:
    w = LANE_BITS[fmt]
    return [(line >> (i * w)) & ((1 << w) - 1) for i in range(line_w // w)]


def join(vals, fmt: int) -> int:
    w = LANE_BITS[fmt]
    out = 0
    for i, v in enumerate(vals):
        out |= (v & ((1 << w) - 1)) << (i * w)
    return out


def split_w(line: int, w: int, line_w: int = 32) -> list:
    return [(line >> (i * w)) & ((1 << w) - 1) for i in range(line_w // w)]


def join_w(vals, w: int) -> int:
    out = 0
    for i, v in enumerate(vals):
        out |= (v & ((1 << w) - 1)) << (i * w)
    return out


# ----------------------------------------------------------------------------
# Matching (the library tests' own contracts)
# ----------------------------------------------------------------------------


def fp_match(fmt_obj, got: int, exp: int, ulp: int = 1) -> bool:
    """FPBaseTB.check_result semantics: NaN == NaN, +0 == -0, inf exact,
    otherwise equal or within ``ulp`` with matching sign."""
    if FPUtils.is_nan(got, fmt_obj) and FPUtils.is_nan(exp, fmt_obj):
        return True
    gz, ez = FPUtils.is_zero(got, fmt_obj), FPUtils.is_zero(exp, fmt_obj)
    if gz and ez:
        return True
    if gz or ez or FPUtils.is_inf(got, fmt_obj) or FPUtils.is_inf(exp, fmt_obj):
        return got == exp
    if got == exp:
        return True
    mask = (1 << (fmt_obj.bits - 1)) - 1
    sign_ok = (got >> (fmt_obj.bits - 1)) == (exp >> (fmt_obj.bits - 1))
    return sign_ok and abs((got & mask) - (exp & mask)) <= ulp


def _ref(cls, **attrs):
    obj = cls.__new__(cls)
    obj.__dict__.update(attrs)
    return obj


# ----------------------------------------------------------------------------
# int8
# ----------------------------------------------------------------------------


def s8(x: int) -> int:
    x &= 0xFF
    return x - 256 if x & 0x80 else x


def sat8(x: int) -> int:
    return max(-128, min(127, x)) & 0xFF


def requant(v: int, sh: int) -> int:
    """sat8(round-half-up(v / 2^sh)), alu_infer_acc's int8 presentation."""
    r = v if sh == 0 else (v + (1 << (sh - 1))) >> sh
    return sat8(r)


def wrap32(x: int) -> int:
    x &= 0xFFFFFFFF
    return x - (1 << 32) if x & 0x80000000 else x


class Int8Model:
    """Saturating int8 rows (no library block; the MAS contract, exactly)."""

    @staticmethod
    def lane(opcode: int, sub_op: int, a: int, b: int, imm: int) -> int:
        a, b = s8(a), s8(b)
        if opcode == OP_ADD:
            return sat8(a + b)
        if opcode == OP_SUB:
            return sat8(a - b)
        if opcode == OP_MUL:
            return sat8(a * b)
        if opcode == OP_MINMAX:
            return (max(a, b) if sub_op & 1 else min(a, b)) & 0xFF
        if opcode == OP_RELU:
            return 0 if a < 0 else a
        if opcode == OP_CONST:
            return imm & 0xFF
        if opcode == OP_COPY:
            return a & 0xFF
        return 0

    @staticmethod
    def lt(a: int, b: int, imm: int, sub_op: int) -> int:
        return 1 if s8(a) < s8(imm if sub_op & 1 else b) else 0


# ----------------------------------------------------------------------------
# Floating-point formats (bf16 extended rows, fp32, fp8 e4m3)
# ----------------------------------------------------------------------------


class FpModel:
    """Library reference models for one floating-point element format."""

    def __init__(self, fmt: int, leaky_shift: int = 4):
        self.fmt = fmt
        self.f = FP_FORMAT[fmt]
        self.bits = self.f.bits
        self.sign = 1 << (self.bits - 1)
        self._add = _ref(FPAdderTB, fmt=self.f)
        self._mul = _ref(FPMultiplierTB, fmt=self.f)
        self._cmp = _ref(FPComparatorTB, fmt=self.f)
        self._min = _ref(FPMaxMinTB, fmt=self.f, is_max=False)
        self._max = _ref(FPMaxMinTB, fmt=self.f, is_max=True)
        self._relu = _ref(FPReluTB, fmt=self.f)
        self._act = {
            OP_LEAKY: _ref(FPLeakyReluTB, fmt=self.f, alpha_shift=leaky_shift,
                           alpha=2 ** (-leaky_shift)),
            OP_GELU: _ref(FPGeluTB, fmt=self.f),
            OP_SIGMOID: _ref(FPSigmoidTB, fmt=self.f),
            OP_SILU: _ref(FPSiluTB, fmt=self.f),
            OP_TANH: _ref(FPTanhTB, fmt=self.f),
        }

    def match(self, got: int, exp: int, ulp: int = 1) -> bool:
        return fp_match(self.f, got, exp, ulp)

    def lane(self, opcode: int, sub_op: int, a: int, b: int, imm_lane: int) -> int:
        if opcode == OP_ADD:
            return self._add.compute_expected(a, b)[0]
        if opcode == OP_SUB:
            return self._add.compute_expected(a, b ^ self.sign)[0]
        if opcode == OP_MUL:
            return self._mul.compute_expected(a, b)[0]
        if opcode == OP_MINMAX:
            return (self._max if sub_op & 1 else self._min).compute_expected(a, b)
        if opcode == OP_RELU:
            return self._relu.compute_expected(a)
        if opcode == OP_CONST:
            return imm_lane
        if opcode == OP_COPY:
            return a
        if opcode in self._act:
            return self._act[opcode].compute_expected(a)
        return 0

    def lt(self, a: int, b: int, imm_lane: int, sub_op: int) -> int:
        return 1 if self._cmp.compute_expected(a, imm_lane if sub_op & 1 else b)['lt'] else 0

    def exact(self, opcode: int) -> bool:
        """Rows the library tests check bit-exactly (no ULP slack)."""
        return opcode in (OP_COPY, OP_CONST, OP_MINMAX, OP_RELU)


def imm_lane(fmt: int, imm: int) -> int:
    """threshold_imm as one lane of the format (alu_infer_*_rows)."""
    if fmt == FMT_FP32:
        return (imm & 0xFFFF) << 16
    if fmt in (FMT_INT8, FMT_FP8):
        return imm & 0xFF
    return imm & 0xFFFF


# ----------------------------------------------------------------------------
# bf16-only library rows: reciprocal, exp2, log2, log2-scale
# ----------------------------------------------------------------------------

_RECIP = _ref(BF16ReciprocalTB)
_EXP2 = _ref(BF16Exp2TB, lut_depth=32)
_LOG2 = _ref(BF16Log2TB, lut_depth=32)
_QSCALE = _ref(BF16Log2ScaleTB)
_BF16 = FORMATS['bf16']


def bf16_special_row(opcode: int, x: int):
    """(expected, ulp tolerance) per the library unit test of that block."""
    if opcode == OP_RECIP:
        return _RECIP._compute_expected_reciprocal(x)[0], 2
    if opcode == OP_EXP2:
        return _EXP2._compute_expected_exp2(x)[0], 16
    if opcode == OP_LOG2:
        exp = _LOG2._compute_expected_log2(x)[0]
        return exp, (200 if ((exp >> 7) & 0xFF) < 125 else 16)
    if opcode == OP_QSCALE:
        return _QSCALE._compute_expected_log2_scale(x)[3], 0
    raise ValueError(opcode)


# ----------------------------------------------------------------------------
# Conversions
# ----------------------------------------------------------------------------

_SCALE_I8 = _ref(BF16ScaleToInt8TB)
_I8_TO_BF16 = _ref(IntToBF16TB, int_width=8)


def _conv(src_name: str, dst_name: str):
    return _ref(FPConversionTB, src_fmt=FORMATS[src_name], dst_fmt=FORMATS[dst_name])


_CONV = {
    (FMT_BF16, FMT_FP32): _conv('bf16', 'fp32'),
    (FMT_BF16, FMT_FP8): _conv('bf16', 'fp8_e4m3'),
    (FMT_FP32, FMT_BF16): _conv('fp32', 'bf16'),
    (FMT_FP32, FMT_FP8): _conv('fp32', 'fp8_e4m3'),
    (FMT_FP8, FMT_BF16): _conv('fp8_e4m3', 'bf16'),
    (FMT_FP8, FMT_FP32): _conv('fp8_e4m3', 'fp32'),
    ('alt', 0): _conv('bf16', 'fp16'),
    ('alt', 1): _conv('fp16', 'bf16'),
    ('alt', 2): _conv('bf16', 'fp8_e5m2'),
    ('alt', 3): _conv('fp8_e5m2', 'bf16'),
}

ALT_DST = {0: FORMATS['fp16'], 1: FORMATS['bf16'], 2: FORMATS['fp8_e5m2'],
           3: FORMATS['bf16']}


def cvt_expected(src: int, dst: int, a: int, b: int, imm: int, line_w: int = 32):
    """[(expected lane, lane bits, fmt object or 'int', tolerance)] for OP_CVT."""
    out = []
    if src == dst:
        return [(a, line_w, None, 0)]
    sw, dw = LANE_BITS[src], LANE_BITS[dst]
    a_l, b_l = split_w(a, sw, line_w), split_w(b, sw, line_w)
    n_dst = line_w // dw
    if dw < sw:                         # narrowing: A lanes, then B lanes
        srcs = (a_l + b_l)[:n_dst]
        srcs += [None] * (n_dst - len(srcs))
    else:                               # widening: part B[1:0] of A's lanes
        part = (b & 3) if (sw * 4 == dw) else (b & 1)
        srcs = a_l[part * n_dst:(part + 1) * n_dst]
    for v in srcs:
        if v is None:
            out.append((0, dw, None, 0))
        elif (src, dst) == (FMT_BF16, FMT_INT8):
            out.append((_SCALE_I8._compute_expected_scale_to_int8(v, imm)[0], 8, 'int', 1))
        elif (src, dst) == (FMT_INT8, FMT_BF16):
            out.append((_I8_TO_BF16._compute_expected_from_int(s8(v))[0], 16, _BF16, 1))
        else:
            ref = _CONV[(src, dst)]
            out.append((ref.compute_expected(v), dw, ref.dst_fmt, 1))
    return out


def alt_expected(sub_op: int, a: int, b: int, line_w: int = 32):
    ref = _CONV[('alt', sub_op)]
    if sub_op in (0, 1):                # same width, lane for lane
        srcs, dw = split_w(a, 16, line_w), 16
    elif sub_op == 2:                   # bf16 -> e5m2: A lanes then B lanes
        srcs, dw = split_w(a, 16, line_w) + split_w(b, 16, line_w), 8
    else:                               # e5m2 -> bf16: half B[0] of A's lanes
        n = line_w // 16
        srcs, dw = split_w(a, 8, line_w)[(b & 1) * n:(b & 1) * n + n], 16
    return [(ref.compute_expected(v), dw, ALT_DST[sub_op], 1) for v in srcs]


def lanes_match(got_line: int, expected, line_w: int = 32) -> bool:
    pos = 0
    for exp, w, fmt_obj, tol in expected:
        got = (got_line >> pos) & ((1 << w) - 1)
        pos += w
        if fmt_obj is None:
            ok = got == exp
        elif fmt_obj == 'int':
            ok = abs(s8(got) - s8(exp)) <= tol
        else:
            ok = fp_match(fmt_obj, got, exp, tol)
        if not ok:
            return False
    return True


# ----------------------------------------------------------------------------
# Accumulator rows
# ----------------------------------------------------------------------------

_FMA32 = _ref(FPFMATB, fmt=FORMATS['fp32'])
_ADD32 = _ref(FPAdderTB, fmt=FORMATS['fp32'])
_MAX32 = _ref(FPMaxMinTB, fmt=FORMATS['fp32'], is_max=True)
_TO_BF16 = _conv('fp32', 'bf16')
_TO_FP8 = _conv('fp32', 'fp8_e4m3')
_FP8_TO_BF16 = _conv('fp8_e4m3', 'bf16')


def fp8_to_bf16_exact(x: int) -> int:
    return _FP8_TO_BF16.compute_expected(x)


def fp32_fma_ref(a: int, b: int, c: int) -> int:
    return _FMA32.compute_expected(a, b, c)[0]


def fp32_add_ref(a: int, b: int) -> int:
    return _ADD32.compute_expected(a, b)[0]


def fp32_max_ref(a: int, b: int) -> int:
    return _MAX32.compute_expected(a, b)


def view_fp32_to_bf16(acc: int) -> int:
    return _TO_BF16.compute_expected(acc)


def view_fp32_to_fp8(acc: int) -> int:
    return _TO_FP8.compute_expected(acc)


# PWL re-exports so tests import one module.
build_pwl_table = pwl.build_table
pwl_entry_word = pwl.entry_word
pwl_eval = pwl.pwl_eval
pwl_seg_index = pwl.seg_index
PWL_FUNCS = pwl.FUNCS
PWL_DOMAIN = pwl.DOMAIN
bf16_rne = pwl.bf16_rne
bf16_float = pwl.bf16_float
bf16_fma_fp32 = pwl.bf16_fma_fp32
bf16_from_fp32_bits = pwl.bf16_from_fp32
