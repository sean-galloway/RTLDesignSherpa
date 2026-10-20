#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: alu_infer_pwl
# Purpose: Build the 256-entry piecewise-linear LUT for ALU-INFER's OP_PWL row
#          and model the row bit-for-bit
#
# Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
# Subsystem: alu-infer
#
# Author: sean galloway
# Created: 2026-10-20

"""PWL LUT builder and bit-level model for alu_infer_pwl.sv.

The segment index of a bf16 x is {sign, octave[3:0], mant[6:4]} with
octave = exp - 120 clamped to [0, 15]: |x| in [2^-7, 2^9) at 8 segments per
octave.  |x| < 2^-7 falls in segment {sign,0,0}; |x| >= 2^9, inf and NaN in
{sign,15,7}.  An entry is {slope bf16 [31:16], intercept bf16 [15:0]} and the
row computes bf16(fma(slope, x, intercept)).

Each segment is fitted by least squares over its range, the slope rounded to
bf16, and the intercept refitted against the rounded slope before it is
rounded too -- the slope's rounding error is what dominates otherwise.

usage:
  alu_infer_pwl.py <sigmoid|tanh|gelu|exp|silu> [--hex out.hex] [--report]
    --hex     write 256 lines of 8 hex digits, entry i on line i
    --report  print max abs / rel error of the modeled row over a sweep
"""

import argparse
import math
import struct
import sys

FUNCS = {
    'sigmoid': lambda x: 1.0 / (1.0 + math.exp(-x)) if x > -700 else 0.0,
    'tanh': math.tanh,
    'gelu': lambda x: 0.5 * x * (1.0 + math.erf(x / math.sqrt(2.0))),
    'silu': lambda x: x / (1.0 + math.exp(-x)) if x > -700 else 0.0,
    'exp': lambda x: math.exp(x) if x < 88.7 else float('inf'),
}

# Sweep domain per function for --report and the testbench's accuracy bound.
# exp is reported where softmax uses it (x - max <= 0, plus headroom):
# log-spaced segments are an octave wide at large |x|, too coarse for exp
# there, and exp(-16) is already below bf16's useful range for softmax.
DOMAIN = {'sigmoid': (-12.0, 12.0), 'tanh': (-12.0, 12.0), 'gelu': (-12.0, 12.0),
          'silu': (-12.0, 12.0), 'exp': (-16.0, 4.0)}

# ---------------------------------------------------------------------------
# bf16 / fp32 bit helpers (no cocotb; the testbench imports these)
# ---------------------------------------------------------------------------


def fp32_bits(f: float) -> int:
    try:
        return struct.unpack('>I', struct.pack('>f', f))[0]
    except OverflowError:
        return 0x7F800000 if f > 0 else 0xFF800000


def fp32_float(u: int) -> float:
    return struct.unpack('>f', struct.pack('>I', u & 0xFFFFFFFF))[0]


def bf16_float(x: int) -> float:
    return fp32_float((x & 0xFFFF) << 16)


def bf16_from_fp32(u: int) -> int:
    """RNE fp32 -> bf16 on the bit pattern (NaN stays a quiet NaN)."""
    if (u & 0x7F800000) == 0x7F800000 and (u & 0x007FFFFF):
        return ((u >> 16) | 0x0040) & 0xFFFF
    lsb = (u >> 16) & 1
    return ((u + 0x7FFF + lsb) >> 16) & 0xFFFF


def bf16_rne(f: float) -> int:
    if math.isnan(f):
        return 0x7FC0
    return bf16_from_fp32(fp32_bits(f))


def bf16_fma_fp32(a: int, b: int, c32: int) -> int:
    """math_bf16_fma contract: exact product; an FP32-underflowing product
    (|p| < 2^-126) is flushed and the addend returned verbatim; one fp32
    rounding of the sum."""
    p = bf16_float(a) * bf16_float(b)
    if p != 0.0 and abs(p) < 2.0 ** -126:
        return c32
    s = p + fp32_float(c32)
    if s > 3.4028234663852886e38:
        s = float('inf')
    elif s < -3.4028234663852886e38:
        s = float('-inf')
    return fp32_bits(s)


# ---------------------------------------------------------------------------
# Segments
# ---------------------------------------------------------------------------


def seg_index(x: int) -> int:
    s, e, m = (x >> 15) & 1, (x >> 7) & 0xFF, x & 0x7F
    if e < 120:
        return s << 7
    if e > 135:
        return (s << 7) | (15 << 3) | 7
    return (s << 7) | ((e - 120) << 3) | (m >> 4)


def seg_range(idx: int):
    """(sign, lo, hi) of |x| covered by segment idx."""
    s, o, m = (idx >> 7) & 1, (idx >> 3) & 0xF, idx & 7
    base = 2.0 ** (o - 7)
    lo, hi = base * (1 + m / 8), base * (1 + (m + 1) / 8)
    if o == 0 and m == 0:
        lo = 0.0
    return s, lo, hi


def fit_segment(f, idx: int, n: int = 64):
    s, lo, hi = seg_range(idx)
    xs = [lo + (hi - lo) * (k + 0.5) / n for k in range(n)]
    if s:
        xs = [-x for x in xs]
    ys = [f(x) for x in xs]
    if any(math.isinf(y) for y in ys):
        return 0x0000, bf16_rne(ys[-1] if s == 0 else 0.0)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx if sxx else 0.0
    sb = bf16_rne(slope)
    slope_r = bf16_float(sb)
    icpt = sum(y - slope_r * x for x, y in zip(xs, ys)) / n
    return sb, bf16_rne(icpt)


def build_table(name: str):
    f = FUNCS[name]
    return [fit_segment(f, i) for i in range(256)]


def entry_word(slope: int, icpt: int) -> int:
    return ((slope & 0xFFFF) << 16) | (icpt & 0xFFFF)


def pwl_eval(table, x: int) -> int:
    """Bit-level model of one alu_infer_pwl lane."""
    slope, icpt = table[seg_index(x)]
    x_inf = ((x >> 7) & 0xFF) == 0xFF and (x & 0x7F) == 0
    if x_inf and (slope & 0x7FFF) == 0:
        return icpt
    return bf16_from_fp32(bf16_fma_fp32(slope, x, (icpt & 0xFFFF) << 16))


def sweep_error(name: str, table, n: int = 4001):
    f = FUNCS[name]
    lo, hi = DOMAIN[name]
    worst_abs = worst_rel = 0.0
    for k in range(n):
        x = bf16_rne(lo + (hi - lo) * k / (n - 1))
        xf = bf16_float(x)
        y = bf16_float(pwl_eval(table, x))
        ref = f(xf)
        if math.isinf(ref) or math.isnan(y):
            continue
        err = abs(y - ref)
        worst_abs = max(worst_abs, err)
        if abs(ref) > 2.0 ** -6:
            worst_rel = max(worst_rel, err / abs(ref))
    return worst_abs, worst_rel


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('func', choices=sorted(FUNCS))
    ap.add_argument('--hex', help='write the table as 256 hex words')
    ap.add_argument('--report', action='store_true', help='print the modeled error')
    args = ap.parse_args(argv)

    table = build_table(args.func)
    if args.hex:
        with open(args.hex, 'w') as fh:
            for slope, icpt in table:
                fh.write(f'{entry_word(slope, icpt):08x}\n')
        print(f'wrote {args.hex} (256 entries)')
    if args.report or not args.hex:
        a, r = sweep_error(args.func, table)
        lo, hi = DOMAIN[args.func]
        print(f'{args.func}: max abs error {a:.3e}, max rel error {r:.3e} over [{lo:g}, {hi:g}]')
    return 0


if __name__ == '__main__':
    sys.exit(main())
