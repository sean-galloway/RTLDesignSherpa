# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: alu_infer_ext_tests
# Purpose: Scenarios for the ALU-INFER element formats and the roadmap/growth
#          rows (reduce, PWL LUT, const, library activations, conversions)
# Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
# Subsystem: alu-infer
#
# Author: sean galloway
# Created: 2026-10-20

"""Extended-row scenarios, mixed into AluInferTB.

Every check runs through the same GAXI BFMs as the v1 scenarios
(``_make_packet`` / ``issue_burst`` / ``recv_packets``); invocations go out
as bursts so the elastic pipeline streams while the golden models check
each retired line.  Golden values come from alu_infer_golden, which wraps
the rtl/math library's own reference models.
"""

import math
import random

from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.common.fp_testing import FPTestValues, FPUtils, special_value_grid

from .alu_infer_golden import (
    FMT_BF16, FMT_INT8, FMT_FP32, FMT_FP8, FMT_NAMES, FP_FORMAT,
    OP_COPY, OP_ADD, OP_SUB, OP_MUL, OP_MAC, OP_MINMAX, OP_CMP, OP_RELU,
    OP_REDUCE, OP_PWL, OP_PWL_LUT, OP_CONST, OP_CVT, OP_ALTFMT, OP_RECIP,
    ACT_OPS, BF16_ONLY_OPS, CVT_PAIRS, ACC_HOLD, ACC_ACCUM, ACC_CLEAR, ACC_DRAIN,
    Int8Model, FpModel, imm_lane, split, join, s8, requant, wrap32,
    bf16_special_row, cvt_expected, alt_expected, lanes_match, fp_match,
    fp32_fma_ref, fp32_add_ref, fp32_max_ref, fp8_to_bf16_exact,
    view_fp32_to_bf16, view_fp32_to_fp8,
    build_pwl_table, pwl_entry_word, pwl_eval, PWL_FUNCS, PWL_DOMAIN,
    bf16_rne, bf16_float, bf16_fma_fp32, bf16_from_fp32_bits,
)

# Value-set depth per TEST_LEVEL, in fp_testing's vocabulary.
VALUE_LEVEL = {'gate': 'simple', 'func': 'basic', 'full': 'medium'}

# Modeled PWL accuracy bounds (bin/alu_infer_pwl.py --report, with margin):
# abs error over the function's domain, exp as relative error.
PWL_BOUND = {'sigmoid': ('abs', 5e-3), 'tanh': ('abs', 5e-3), 'gelu': ('abs', 1e-2),
             'silu': ('abs', 2e-2), 'exp': ('rel', 4e-2)}


class AluInferExtTests:
    """Mixin: the extended scenarios.  Relies on AluInferTB's BFM helpers."""

    # ------------------------------------------------------------------
    # Batched stimulus/check
    # ------------------------------------------------------------------

    def _values(self, fmt):
        level = VALUE_LEVEL.get(self.level, 'basic')
        if fmt == FMT_INT8:
            n = {'simple': 24, 'basic': 96, 'medium': 256}[level]
            fixed = [0x00, 0x01, 0x7F, 0x80, 0x81, 0xFF, 0x40, 0xC0]
            return fixed + [random.randint(0, 255) for _ in range(n)]
        f = FP_FORMAT[fmt]
        return [v for _, v in special_value_grid(f)] + FPTestValues.get_all_test_values(f, level)

    def _line_of(self, fmt, pool):
        return join([random.choice(pool) for _ in range(self.line_w // {0: 16, 1: 8, 2: 32, 3: 8}[fmt])],
                    fmt)

    async def run_cases(self, cases, chunk=48, label=''):
        """Issue cases as bursts; check every retired line with its checker.

        A case is a dict: op, a, b, imm, sub_op, fmt, acc_ctrl, check.  The
        checker takes (line, flags) and returns an error string or None.
        """
        self.drain_results()
        errors = []
        for start in range(0, len(cases), chunk):
            grp = cases[start:start + chunk]
            pkts = [self._make_packet(c['op'], a=c.get('a', 0), b=c.get('b', 0),
                                      imm=c.get('imm', 0), sub_op=c.get('sub_op', 0),
                                      acc_ctrl=c.get('acc_ctrl', 0), fmt=c.get('fmt', 0))
                    for c in grp]
            await self.issue_burst(pkts)
            res = await self.recv_packets(len(grp), timeout_cycles=4 * len(grp) + 256)
            for i, (c, r) in enumerate(zip(grp, res)):
                why = c['check'](int(r.line), int(r.flags))
                if why:
                    errors.append(f"{label}[{start + i}] op={c['op']} sub={c.get('sub_op', 0)} "
                                  f"fmt={FMT_NAMES[c.get('fmt', 0)]} a=0x{c.get('a', 0):08X} "
                                  f"b=0x{c.get('b', 0):08X} imm=0x{c.get('imm', 0):04X}: {why}")
        for e in errors[:12]:
            self.log.error(e)
        assert not errors, f"{label}: {len(errors)} of {len(cases)} cases failed"
        return len(cases)

    # ------------------------------------------------------------------
    # Element formats: the elementwise rows
    # ------------------------------------------------------------------

    def _elementwise_cases(self, fmt, ops):
        pool = self._values(fmt)
        model = None if fmt == FMT_INT8 else FpModel(fmt)
        cases = []
        n_cases = {'gate': 12, 'func': 48, 'full': 160}.get(self.level, 48)

        for op, sub_op in ops:
            for _ in range(n_cases):
                a, b = self._line_of(fmt, pool), self._line_of(fmt, pool)
                imm = random.choice(pool) & 0xFFFF if fmt != FMT_FP32 else random.choice(pool) >> 16
                cases.append(dict(op=op, sub_op=sub_op, fmt=fmt, a=a, b=b, imm=imm,
                                  check=self._elementwise_checker(fmt, model, op, sub_op, a, b, imm)))
        return cases

    def _elementwise_checker(self, fmt, model, op, sub_op, a, b, imm):
        al, bl = split(a, fmt, self.line_w), split(b, fmt, self.line_w)
        il = imm_lane(fmt, imm)

        def check(line, flags):
            gl = split(line, fmt, self.line_w)
            if op == OP_CMP:
                if line != 0:
                    return f"compare result_line must be 0, got 0x{line:08X}"
                if fmt == FMT_INT8:
                    exp = [Int8Model.lt(x, y, il, sub_op) for x, y in zip(al, bl)]
                else:
                    exp = [model.lt(x, y, il, sub_op) for x, y in zip(al, bl)]
                want = sum(v << i for i, v in enumerate(exp))
                return None if flags == want else f"flags 0x{flags:X}, expected 0x{want:X}"
            if flags != 0:
                return f"flags 0x{flags:X} on a non-compare row"
            for i, (g, x, y) in enumerate(zip(gl, al, bl)):
                if fmt == FMT_INT8:
                    e = Int8Model.lane(op, sub_op, x, y, il)
                    ok = g == e
                else:
                    e = model.lane(op, sub_op, x, y, il)
                    ok = fp_match(model.f, g, e, 0) if model.exact(op) else model.match(g, e)
                if not ok:
                    return f"lane {i}: got 0x{g:X}, expected 0x{e:X}"
            return None
        return check

    ELEMENTWISE = [(OP_COPY, 0), (OP_ADD, 0), (OP_SUB, 0), (OP_MUL, 0), (OP_MINMAX, 0),
                   (OP_MINMAX, 1), (OP_CMP, 0), (OP_CMP, 1), (OP_RELU, 0), (OP_CONST, 0)]

    async def test_fmt_int8(self):
        """int8 rows: saturating add/sub/mul, min/max, compare, relu, const."""
        self.log.info("=== fmt_int8 ===")
        n = await self.run_cases(self._elementwise_cases(FMT_INT8, self.ELEMENTWISE), label='int8')
        self.log.info(f"fmt_int8 PASSED ({n} invocations)")

    async def test_fmt_fp32(self):
        """fp32 rows on the IEEE 754-2008 blocks (adder on the adder port)."""
        self.log.info("=== fmt_fp32 ===")
        n = await self.run_cases(self._elementwise_cases(FMT_FP32, self.ELEMENTWISE), label='fp32')
        self.log.info(f"fmt_fp32 PASSED ({n} invocations)")

    async def test_fmt_fp8(self):
        """fp8 e4m3 rows on the math_fp8_e4m3_* blocks."""
        self.log.info("=== fmt_fp8 ===")
        n = await self.run_cases(self._elementwise_cases(FMT_FP8, self.ELEMENTWISE), label='fp8')
        self.log.info(f"fmt_fp8 PASSED ({n} invocations)")

    async def test_const(self):
        """const: threshold_imm broadcast into every lane, in every format."""
        self.log.info("=== const ===")
        cases = []
        for fmt in (FMT_BF16, FMT_INT8, FMT_FP32, FMT_FP8):
            for imm in (0x0000, 0x3F80, 0xBF80, 0x7F80, 0x7FC0, 0x00A5, 0x1234):
                exp = join([imm_lane(fmt, imm)] * (self.line_w // {0: 16, 1: 8, 2: 32, 3: 8}[fmt]), fmt)
                cases.append(dict(op=OP_CONST, fmt=fmt, imm=imm, a=random.getrandbits(32),
                                  check=lambda l, f, e=exp: None if (l, f) == (e, 0)
                                  else f"got 0x{l:08X}/0x{f:X}, expected 0x{e:08X}"))
        n = await self.run_cases(cases, label='const')
        self.log.info(f"const PASSED ({n} invocations)")

    # ------------------------------------------------------------------
    # Library activation rows
    # ------------------------------------------------------------------

    async def test_act(self):
        """Activations (bf16/fp32/fp8) and bf16 reciprocal/exp2/log2/qscale,
        each against its library block's own reference and tolerance."""
        self.log.info("=== act ===")
        cases = []
        n_cases = {'gate': 8, 'func': 32, 'full': 96}.get(self.level, 32)
        for fmt in (FMT_BF16, FMT_FP32, FMT_FP8):
            model = FpModel(fmt)
            pool = self._values(fmt)
            for op in ACT_OPS:
                for _ in range(n_cases):
                    a = self._line_of(fmt, pool)
                    cases.append(dict(op=op, fmt=fmt, a=a,
                                      check=self._act_checker(fmt, model, op, a)))
        pool = self._values(FMT_BF16)
        for op in BF16_ONLY_OPS:
            for _ in range(n_cases):
                a = self._line_of(FMT_BF16, pool)
                cases.append(dict(op=op, fmt=FMT_BF16, a=a,
                                  check=self._bf16_special_checker(op, a)))
        n = await self.run_cases(cases, label='act')
        self.log.info(f"act PASSED ({n} invocations)")

    def _act_checker(self, fmt, model, op, a):
        def check(line, flags):
            for i, (g, x) in enumerate(zip(split(line, fmt, self.line_w), split(a, fmt, self.line_w))):
                e = model.lane(op, 0, x, 0, 0)
                if not model.match(g, e):
                    return f"lane {i} x=0x{x:X}: got 0x{g:X}, expected 0x{e:X}"
            return None if flags == 0 else f"flags 0x{flags:X}"
        return check

    def _bf16_special_checker(self, op, a):
        bf16 = FP_FORMAT[FMT_BF16]

        def check(line, flags):
            for i, (g, x) in enumerate(zip(split(line, FMT_BF16, self.line_w),
                                           split(a, FMT_BF16, self.line_w))):
                e, tol = bf16_special_row(op, x)
                ok = (g == e) if tol == 0 else fp_match(bf16, g, e, tol)
                if not ok:
                    return f"lane {i} x=0x{x:04X}: got 0x{g:04X}, expected 0x{e:04X} (tol {tol})"
            return None if flags == 0 else f"flags 0x{flags:X}"
        return check

    # ------------------------------------------------------------------
    # Conversions
    # ------------------------------------------------------------------

    async def test_cvt(self):
        """OP_CVT for every library pair (narrowing packs A then B; widening
        takes the B[1:0] part) and OP_ALTFMT's bf16 <-> fp16/e5m2."""
        self.log.info("=== cvt ===")
        cases = []
        n_cases = {'gate': 6, 'func': 24, 'full': 64}.get(self.level, 24)
        for src, dst in CVT_PAIRS + [(f, f) for f in (FMT_BF16, FMT_INT8, FMT_FP32, FMT_FP8)]:
            pool = self._values(src)
            for k in range(n_cases):
                a, b = self._line_of(src, pool), self._line_of(src, pool)
                b = (b & ~3) | (k & 3)          # walk the widening part select
                imm = random.choice([0x3F80, 0x4000, 0x3E00, 0x4300, 0x3C00])
                exp = cvt_expected(src, dst, a, b, imm, self.line_w)
                cases.append(dict(op=OP_CVT, fmt=src, sub_op=dst, a=a, b=b, imm=imm,
                                  check=lambda l, f, e=exp: None if lanes_match(l, e) and f == 0
                                  else f"got 0x{l:08X}, expected lanes {[hex(x[0]) for x in e]}"))
        bf_pool = self._values(FMT_BF16)
        for sub_op in range(4):
            for k in range(n_cases):
                a = self._line_of(FMT_BF16, bf_pool) if sub_op != 3 else random.getrandbits(32)
                b = (self._line_of(FMT_BF16, bf_pool) & ~1) | (k & 1)
                exp = alt_expected(sub_op, a, b, self.line_w)
                cases.append(dict(op=OP_ALTFMT, fmt=FMT_BF16, sub_op=sub_op, a=a, b=b,
                                  check=lambda l, f, e=exp: None if lanes_match(l, e) and f == 0
                                  else f"got 0x{l:08X}, expected lanes {[hex(x[0]) for x in e]}"))
        n = await self.run_cases(cases, label='cvt')
        self.log.info(f"cvt PASSED ({n} invocations)")

    # ------------------------------------------------------------------
    # Accumulator rows: MAC in every format, REDUCE sum/max and the fold
    # ------------------------------------------------------------------

    def _acc_lanes(self, fmt):
        return self.line_w // {FMT_BF16: 16, FMT_INT8: 8, FMT_FP32: 32, FMT_FP8: 8}[fmt]

    def _acc_step(self, fmt, kind, acc, a_l, b_l):
        """One ACCUMULATE on the golden bank (kind: 'mac', 'sum', 'max')."""
        out = []
        for i, c in enumerate(acc):
            if fmt == FMT_INT8:
                x, y = s8(a_l[i]), s8(b_l[i])
                cs = wrap32(c)
                v = max(cs, x) if kind == 'max' else cs + (x if kind == 'sum' else x * y)
                out.append(wrap32(v) & 0xFFFFFFFF)
            elif fmt == FMT_FP32:
                if kind == 'max':
                    out.append(fp32_max_ref(c, a_l[i]))
                else:
                    out.append(fp32_fma_ref(a_l[i], 0x3F800000 if kind == 'sum' else b_l[i], c))
            else:
                x = fp8_to_bf16_exact(a_l[i]) if fmt == FMT_FP8 else a_l[i]
                y = fp8_to_bf16_exact(b_l[i]) if fmt == FMT_FP8 else b_l[i]
                if kind == 'max':
                    out.append(fp32_max_ref(c, x << 16))
                else:
                    out.append(bf16_fma_fp32(x, 0x3F80 if kind == 'sum' else y, c))
        return out

    def _acc_view(self, fmt, bank, imm, fold=None):
        """Expected presentation: [(lane, bits, fmt object | None, tol)]."""
        n = self._acc_lanes(fmt)
        vals = list(bank[:n])
        tol_view = 1
        if fold is not None:
            if fmt == FMT_INT8:
                t = sum(wrap32(v) for v in vals) if fold == 'sum' else max(wrap32(v) for v in vals)
                vals = [wrap32(t) & 0xFFFFFFFF] * n
            else:
                t = vals[0]
                for v in vals[1:]:
                    t = fp32_add_ref(t, v) if fold == 'sum' else fp32_max_ref(t, v)
                vals = [t] * n
        if fmt == FMT_INT8:
            return [(requant(wrap32(v), imm & 0x1F), 8, None, 0) for v in vals]
        if fmt == FMT_FP32:
            # The fp32 bank comes from math_ieee754_2008_fp32_fma, checked at
            # its library test's 1-ULP contract (FPFMATB reference).
            return [(v, 32, FP_FORMAT[FMT_FP32], 1) for v in vals]
        if fmt == FMT_FP8:
            return [(view_fp32_to_fp8(v), 8, FP_FORMAT[FMT_FP8], tol_view) for v in vals]
        return [(view_fp32_to_bf16(v), 16, FP_FORMAT[FMT_BF16], tol_view) for v in vals]

    def _acc_pool(self, fmt):
        """Accumulator stimulus: finite values of moderate range, so a chain
        stays informative instead of saturating to inf in a few steps.  No
        subnormals: every row is FTZ (open item M3), which the v1 soak's
        stimulus already respects."""
        if fmt == FMT_INT8:
            return list(range(256))
        f = FP_FORMAT[fmt]
        pool = []
        for v in self._values(fmt):
            if FPUtils.is_subnormal(v, f):
                continue
            fv = FPUtils.to_float(v, f)
            if math.isfinite(fv) and (fv == 0.0 or 2.0 ** -20 < abs(fv) < 2.0 ** 20):
                pool.append(v)
        return pool

    async def _acc_chain(self, fmt, kind, steps, fold_kinds=(None,)):
        """CLEAR, then `steps` ACCUMULATEs, then DRAIN (+ fold views).

        The bank state is golden-exact for bf16/fp8/int8.  fp32 presents the
        bank verbatim, so after each step the golden bank re-syncs from the
        DUT (the library FMA reference is checked at its 1-ULP tolerance).
        """
        op = OP_MAC if kind == 'mac' else OP_REDUCE
        sub = {'mac': 0, 'sum': 0, 'max': 1}[kind]
        n = self._acc_lanes(fmt)
        pool = self._acc_pool(fmt)
        imm = random.choice([0, 0, 2, 4]) if fmt == FMT_INT8 else 0
        clear = 0xFF800000 if (kind == 'max' and fmt != FMT_INT8) else \
            (0x80000000 if kind == 'max' else 0)
        bank = [clear] * n
        line_w = self.line_w
        errors = []

        def check_view(line, view, tag):
            if not lanes_match(line, view, line_w):
                errors.append(f"{FMT_NAMES[fmt]} {kind} {tag}: got 0x{line:08X}, "
                              f"expected {[hex(v[0]) for v in view]}")
                return False
            return True

        self.drain_results()
        await self.issue(op, sub_op=sub, fmt=fmt, acc_ctrl=ACC_CLEAR, imm=imm)
        line, _ = await self.recv_result()
        check_view(line, self._acc_view(fmt, bank, imm), 'clear')

        for k in range(steps):
            a, b = self._line_of(fmt, pool), self._line_of(fmt, pool)
            a_l, b_l = split(a, fmt, line_w), split(b, fmt, line_w)
            bank = self._acc_step(fmt, kind, bank, a_l, b_l)
            await self.issue(op, sub_op=sub, fmt=fmt, acc_ctrl=ACC_ACCUM, a=a, b=b, imm=imm)
            line, _ = await self.recv_result()
            ok = check_view(line, self._acc_view(fmt, bank, imm), f'step {k}')
            if fmt == FMT_FP32:
                bank = split(line, FMT_FP32, line_w)     # re-sync (exact view)
            if not ok:
                break

        for ctrl in (ACC_DRAIN, ACC_HOLD):
            await self.issue(op, sub_op=sub, fmt=fmt, acc_ctrl=ctrl, imm=imm)
            line, _ = await self.recv_result()
            check_view(line, self._acc_view(fmt, bank, imm), f'ctrl {ctrl}')

        if op == OP_REDUCE:
            for fk in fold_kinds:
                if fk is None:
                    continue
                await self.issue(op, sub_op=sub | 2, fmt=fmt, acc_ctrl=ACC_DRAIN, imm=imm)
                line, _ = await self.recv_result()
                check_view(line, self._acc_view(fmt, bank, imm, fold=fk), f'fold {fk}')
        for e in errors[:8]:
            self.log.error(e)
        assert not errors, f"{len(errors)} accumulator mismatches"

    async def test_reduce(self):
        """REDUCE sum/max in every format: identity CLEAR, span accumulate,
        DRAIN/HOLD, cross-lane fold broadcast."""
        self.log.info("=== reduce ===")
        steps = {'gate': 6, 'func': 24, 'full': 64}.get(self.level, 24)
        for fmt in (FMT_BF16, FMT_INT8, FMT_FP32, FMT_FP8):
            await self._acc_chain(fmt, 'sum', steps, fold_kinds=('sum',))
            await self._acc_chain(fmt, 'max', steps, fold_kinds=('max',))
        self.log.info("reduce PASSED")

    async def test_mac_formats(self):
        """MAC chains in int8 (int32 accumulate, requantize shift), fp32 and fp8."""
        self.log.info("=== mac_formats ===")
        steps = {'gate': 6, 'func': 32, 'full': 96}.get(self.level, 32)
        for fmt in (FMT_INT8, FMT_FP32, FMT_FP8):
            await self._acc_chain(fmt, 'mac', steps)
        self.log.info("mac_formats PASSED")

    async def test_mac_chain(self):
        """A dependent bf16 MAC chain of >100 steps streamed at II=1: every
        step's view exact, one retirement per clock (the single-cycle
        accumulate loop at any MAC_LATENCY)."""
        steps = {'gate': 104, 'func': 160, 'full': 512}.get(self.level, 160)
        self.log.info(f"=== mac_chain: {steps} dependent steps at II=1 ===")
        self.drain_results()
        await self.issue(OP_MAC, acc_ctrl=ACC_CLEAR)
        await self.recv_result()

        pool = self._acc_pool(FMT_BF16)
        bank = [0, 0]
        pkts, expect = [], []
        for _ in range(steps):
            a, b = self._line_of(FMT_BF16, pool), self._line_of(FMT_BF16, pool)
            a_l, b_l = split(a, FMT_BF16, self.line_w), split(b, FMT_BF16, self.line_w)
            bank = [bf16_fma_fp32(a_l[i], b_l[i], bank[i]) for i in range(2)]
            expect.append(join([bf16_from_fp32_bits(v) for v in bank], FMT_BF16))
            pkts.append(self._make_packet(OP_MAC, a=a, b=b, acc_ctrl=ACC_ACCUM))
        await self.issue_burst(pkts)
        res = await self.recv_packets(steps, timeout_cycles=steps + 256)
        for k, (r, e) in enumerate(zip(res, expect)):
            assert int(r.line) == e, f"chain step {k}: got 0x{int(r.line):08X}, expected 0x{e:08X}"
        issue_t = [int(p.end_time) for p in pkts]
        ret_t = [int(r.end_time) for r in res]
        for k in range(1, steps):
            assert issue_t[k] - issue_t[k - 1] == self.CLK_NS, f"issue bubble before step {k}"
            assert ret_t[k] - ret_t[k - 1] == self.CLK_NS, f"retire bubble before step {k}"
        self.log.info(f"mac_chain PASSED ({steps} steps, II=1, MAC_LATENCY={self.mac_latency})")

    # ------------------------------------------------------------------
    # PWL LUT activation
    # ------------------------------------------------------------------

    async def load_pwl_table(self, table):
        pkts = [self._make_packet(OP_PWL_LUT, a=pwl_entry_word(s, c), b=i, sub_op=0)
                for i, (s, c) in enumerate(table)]
        self.drain_results()
        await self.issue_burst(pkts)
        res = await self.recv_packets(len(pkts), timeout_cycles=len(pkts) + 256)
        assert all(int(r.line) == 0 for r in res), "LUT write must retire a zero line"

    async def test_pwl(self):
        """PWL LUT: load a table in-band, read entries back, evaluate
        bit-exactly against the row model, and bound the approximation."""
        funcs = ['sigmoid', 'exp'] if self.level == 'gate' else list(PWL_FUNCS)
        n_pts = {'gate': 48, 'func': 192, 'full': 512}.get(self.level, 192)
        for name in funcs:
            self.log.info(f"=== pwl: {name} ===")
            table = build_pwl_table(name)
            await self.load_pwl_table(table)

            # Read-back: sub_op 1 returns entry B[7:0].
            idx = random.sample(range(256), 8)
            cases = [dict(op=OP_PWL_LUT, sub_op=1, b=i,
                          check=lambda l, f, e=pwl_entry_word(*table[i]): None if l == e
                          else f"readback 0x{l:08X}, expected 0x{e:08X}") for i in idx]

            lo, hi = PWL_DOMAIN[name]
            xs = [bf16_rne(lo + (hi - lo) * random.random()) for _ in range(n_pts)]
            xs += [0x0000, 0x8000, 0x7F80, 0xFF80, 0x7FC0, 0x0001, 0x3C00, 0xBC00,
                   0x4400, 0xC400, 0x5000, 0xD000]
            worst = 0.0
            kind, bound = PWL_BOUND[name]
            for j in range(0, len(xs), 2):
                pair = xs[j:j + 2] + ([0] if len(xs[j:j + 2]) == 1 else [])
                a = join(pair, FMT_BF16)
                exp = join([pwl_eval(table, x) for x in pair], FMT_BF16)
                for x, y in zip(pair, split(exp, FMT_BF16, 32)):
                    xf, ref = bf16_float(x), None
                    if lo <= xf <= hi:
                        ref = PWL_FUNCS[name](xf)
                    if ref is not None and math.isfinite(ref):
                        err = abs(bf16_float(y) - ref)
                        if kind == 'rel':
                            err = err / abs(ref) if abs(ref) > 2.0 ** -6 else 0.0
                        worst = max(worst, err)
                cases.append(dict(op=OP_PWL, a=a, check=lambda l, f, e=exp: None
                                  if lanes_match(l, [(v, 16, FP_FORMAT[FMT_BF16], 0)
                                                     for v in split(e, FMT_BF16, 32)]) and f == 0
                                  else f"got 0x{l:08X}, expected 0x{e:08X}"))
            await self.run_cases(cases, label=f'pwl_{name}')
            assert worst <= bound, f"pwl {name}: {kind} error {worst:.3e} > bound {bound:.1e}"
            self.log.info(f"pwl {name} PASSED (bit-exact, worst {kind} error {worst:.3e})")

    # ------------------------------------------------------------------
    # Softmax: the rows composed the way a gatling program would use them
    # ------------------------------------------------------------------

    async def _one(self, op, **kw):
        await self.issue(op, **kw)
        line, _ = await self.recv_result()
        return line

    async def test_softmax(self):
        """softmax over a vector of bf16 lines, the PRD roadmap's motivating
        sequence: REDUCE max + fold, SUB, PWL exp, REDUCE sum + fold, RECIP,
        MUL.  Each step's results feed the next (issuer-paced feedback).
        Checked against float softmax within the bf16/PWL error budget."""
        n_lines = {'gate': 4, 'func': 8, 'full': 16}.get(self.level, 8)
        trials = {'gate': 2, 'func': 6, 'full': 12}.get(self.level, 6)
        self.log.info(f"=== softmax: {trials} vectors of {2 * n_lines} elements ===")
        await self.load_pwl_table(build_pwl_table('exp'))
        worst = 0.0
        for t in range(trials):
            xs = [[bf16_rne(random.uniform(-6.0, 6.0)) for _ in range(2)] for _ in range(n_lines)]
            lines = [join(x, FMT_BF16) for x in xs]

            # 1. m = max over every element, broadcast to both lanes.
            await self._one(OP_REDUCE, sub_op=1, acc_ctrl=ACC_CLEAR)
            for ln in lines:
                await self._one(OP_REDUCE, sub_op=1, acc_ctrl=ACC_ACCUM, a=ln)
            m_line = await self._one(OP_REDUCE, sub_op=3, acc_ctrl=ACC_DRAIN)
            # 2-3. e = exp(x - m), via the PWL row.
            es = []
            for ln in lines:
                d = await self._one(OP_SUB, a=ln, b=m_line)
                es.append(await self._one(OP_PWL, a=d))
            # 4. s = sum of e, broadcast.
            await self._one(OP_REDUCE, sub_op=0, acc_ctrl=ACC_CLEAR)
            for e in es:
                await self._one(OP_REDUCE, sub_op=0, acc_ctrl=ACC_ACCUM, a=e)
            s_line = await self._one(OP_REDUCE, sub_op=2, acc_ctrl=ACC_DRAIN)
            # 5-6. p = e * (1 / s).
            r_line = await self._one(OP_RECIP, a=s_line)
            ps = [await self._one(OP_MUL, a=e, b=r_line) for e in es]

            xf = [bf16_float(v) for x in xs for v in x]
            mx = max(xf)
            den = sum(math.exp(v - mx) for v in xf)
            ref = [math.exp(v - mx) / den for v in xf]
            got = [bf16_float(v) for p in ps for v in split(p, FMT_BF16, self.line_w)]
            m_got = split(m_line, FMT_BF16, self.line_w)
            assert m_got == [bf16_rne(mx)] * 2, \
                f"vector {t}: max fold 0x{m_line:08X}, expected {mx}"
            err = max(abs(g - r) for g, r in zip(got, ref))
            worst = max(worst, err)
            assert err <= 2e-2, f"vector {t}: softmax error {err:.3e} (got {got}, ref {ref})"
            assert abs(sum(got) - 1.0) <= 5e-2, f"vector {t}: softmax sums to {sum(got)}"
        self.log.info(f"softmax PASSED (worst element error {worst:.3e})")

    # ------------------------------------------------------------------
    # Natural latency per result port
    # ------------------------------------------------------------------

    async def test_latency(self):
        """Every port at its natural latency: combinational 0, adders
        ADDER_LATENCY, multipliers MUL_LATENCY, accumulator MAC_LATENCY --
        in every format that uses the port -- and in-order retirement when
        a slow port's result is ahead of fast ones."""
        self.log.info("=== latency ===")
        one, two = 0x3F803F80, 0x40004000
        f32_one, f32_two = 0x3F800000, 0x40000000
        expect = [
            ('copy', dict(op=OP_COPY, a=one), 0),
            ('bf16 add', dict(op=OP_ADD, a=one, b=two), self.adder_latency),
            ('bf16 mul', dict(op=OP_MUL, a=one, b=two), self.mul_latency),
            ('bf16 mac', dict(op=OP_MAC, a=one, b=two, acc_ctrl=ACC_ACCUM), self.mac_latency),
        ]
        if self.en.get('EN_REDUCE', 1):
            expect.append(('bf16 reduce', dict(op=OP_REDUCE, a=one, acc_ctrl=ACC_ACCUM),
                           self.mac_latency))
        if self.en.get('EN_FP32', 1):
            expect += [('fp32 add', dict(op=OP_ADD, a=f32_one, b=f32_two, fmt=FMT_FP32),
                        self.adder_latency),
                       ('fp32 mul', dict(op=OP_MUL, a=f32_one, b=f32_two, fmt=FMT_FP32),
                        self.mul_latency)]
        if self.en.get('EN_INT8', 1):
            expect.append(('int8 add', dict(op=OP_ADD, a=0x01020304, b=0x01010101, fmt=FMT_INT8), 0))
        if self.en.get('EN_FP8', 1):
            expect.append(('fp8 mul', dict(op=OP_MUL, a=0x38383838, b=0x40404040, fmt=FMT_FP8), 0))
        if self.en.get('EN_PWL', 1):
            expect.append(('pwl', dict(op=OP_PWL, a=one), 0))

        self.drain_results()
        for name, c, lat in expect:
            pkt = self._make_packet(c['op'], a=c.get('a', 0), b=c.get('b', 0),
                                    acc_ctrl=c.get('acc_ctrl', 0), fmt=c.get('fmt', 0))
            await self.issue_master.send(pkt)
            r = await self.recv_packet()
            got = (int(r.end_time) - int(pkt.end_time)) // self.CLK_NS
            assert got == lat, f"{name}: retired {got} cycles after issue, expected {lat}"
            self.log.info(f"  {name}: {got}")

        # Slowest port first, fast rows behind it: retirement stays in order.
        slow = max(expect, key=lambda e: e[2])
        burst = [slow[1], dict(op=OP_COPY, a=0x11112222), dict(op=OP_RELU, a=0xBF803F80)]
        pkts = [self._make_packet(c['op'], a=c.get('a', 0), b=c.get('b', 0),
                                  acc_ctrl=c.get('acc_ctrl', 0), fmt=c.get('fmt', 0)) for c in burst]
        await self.issue_burst(pkts)
        res = await self.recv_packets(3)
        assert int(res[1].line) == 0x11112222 and int(res[2].line) == 0x00003F80, \
            "fast rows behind the slow port retired out of order"
        assert int(res[0].end_time) - int(pkts[0].end_time) >= slow[2] * self.CLK_NS
        self.log.info(f"latency PASSED (slowest port {slow[0]} = {slow[2]})")

    # ------------------------------------------------------------------
    # err_opcode sampling
    # ------------------------------------------------------------------

    async def _count_err_pulses(self):
        """Count issue edges with err_opcode high (sampled in ReadOnly, the
        same phase the issue master's handshake resolves in)."""
        while True:
            await ReadOnly()
            if int(self.dut.valid.value) and int(self.dut.ready.value) and \
                    int(self.dut.err_opcode.value):
                self.err_pulses += 1
            await RisingEdge(self.dut.clk)
