# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: tetrad_golden
# Purpose: Expected result lines for a gatling tetrad: what each cell's
#          alu-infer ALU returns for the operand lines a POP x0 issues, from
#          alu-infer's own golden model (alu_infer_golden, built on the
#          rtl/math reference models), and the line comparison that model's
#          tests use.
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Created: 2026-11-26

"""A bf16 cell model for the tetrad tests.

``CellModel`` takes one cell's configuration and the sequence of POP x0
invocations (operand lines plus acc_ctrl) and returns the expected
``(line, lanes)`` list a PUSH x0 retires, where ``lanes`` is the per-lane
tolerance spec ``alu_infer_golden.lanes_match`` checks.  The compare row
returns its mask, which PUSH x0 writes as ``result_line | result_flags``.
"""

import alu_infer_golden as g

BF16 = g.FP_FORMAT[g.FMT_BF16]
LANES = 2                         # 32-bit line, 2 bf16 lanes


def bf16_pool(rng, n: int) -> list:
    """Finite normal bf16 values of moderate range (no subnormals: every row
    is FTZ), so sums and products stay informative."""
    out = []
    for _ in range(n):
        sign = rng.getrandbits(1)
        exp = rng.randint(118, 136)
        man = rng.getrandbits(7)
        out.append((sign << 15) | (exp << 7) | man)
    return out


def bf16_line(rng) -> int:
    a, b = bf16_pool(rng, 2)
    return a | (b << 16)


class CellModel:
    """Expected results for one cell configured with ``opcode``/``sub_op``."""

    def __init__(self, opcode: int, sub_op: int = 0, threshold: int = 0):
        self.opcode, self.sub_op, self.threshold = opcode, sub_op, threshold
        self.model = g.FpModel(g.FMT_BF16)
        self.bank = [0] * LANES                # fp32 accumulator, per lane

    @property
    def func_sel(self) -> int:
        return g.func_sel(self.opcode, self.sub_op, g.FMT_BF16)

    @property
    def op_lines(self) -> int:
        return 2 if self.opcode in (g.OP_ADD, g.OP_SUB, g.OP_MUL, g.OP_MAC, g.OP_MINMAX) else 1

    def step(self, a: int, b: int, acc: int) -> list:
        """One invocation: the expected lane spec of its result line."""
        a_l, b_l = g.split(a, g.FMT_BF16), g.split(b, g.FMT_BF16)
        if self.opcode == g.OP_MAC:
            if acc == g.ACC_CLEAR:
                self.bank = [0] * LANES
            elif acc == g.ACC_ACCUM:
                self.bank = [g.pwl.bf16_fma_fp32(a_l[i], b_l[i], self.bank[i])
                             for i in range(LANES)]
            return [(g.view_fp32_to_bf16(v), 16, BF16, 1) for v in self.bank]
        if self.opcode == g.OP_CMP:
            imm = g.imm_lane(g.FMT_BF16, self.threshold)
            mask = sum(self.model.lt(a_l[i], b_l[i], imm, self.sub_op) << i
                       for i in range(LANES))
            return [(mask, 32, None, 0)]
        tol = 0 if self.model.exact(self.opcode) else 1
        return [(self.model.lane(self.opcode, self.sub_op, a_l[i], b_l[i], 0), 16,
                 BF16 if tol else None, tol) for i in range(LANES)]


def line_ok(got: int, spec: list) -> bool:
    return g.lanes_match(got, spec)


def spec_str(spec: list) -> str:
    return "[" + ", ".join(f"0x{v:0{w // 4}x}" for v, w, _, _ in spec) + "]"
