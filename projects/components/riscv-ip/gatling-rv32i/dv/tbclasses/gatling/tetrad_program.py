# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: tetrad_program
# Purpose: the hand-assembled tetrad program and its stimulus, authored once:
#          the DV test (dv/tests/test_gatling_tetrad.py) and the Nexys A7
#          board host (projects/fpga-systems/NexysA7/riscv-ip/gatling/bin/
#          gatling_tetrad_programs.py) both build their run from here.
#
# Created: 2026-11-26

"""The tetrad program.

One binary for all four contexts (contexts are implicit, PRD 7 item 2); the
cells differ only in their configuration, as they would after the in-band
cfg stream: a MAC, an ADD, a RELU and a COMPARE cell.

    CFG   x5, 1            ; credit batch register = this cell's FLUSH word
    POP   x0, CLEAR        ; first invocation clears the MAC bank
    PUSH  x0
    li    x7, N
  loop:
    POP   x0, ACCUM        ; acc_ctrl is ignored by the non-MAC rows
    PUSH  x0
    addi  x7, x7, -1
    bne   x7, x0, loop
    li    x8, 1
    KICK  x8               ; this context's group-done event
    li    x6, 0xF
    WAIT  x6               ; the tetrad barrier
    FLUSH x5               ; drain to {tag, dest}
    ECTX
"""

from dataclasses import dataclass
from typing import List

import alu_infer_golden as g

from gatling import xcell_asm as xa
from gatling.tetrad_golden import CellModel, bf16_line

CELLS = (
    lambda: CellModel(g.OP_MAC),
    lambda: CellModel(g.OP_ADD),
    lambda: CellModel(g.OP_RELU),
    lambda: CellModel(g.OP_CMP, sub_op=1, threshold=0x0000),   # lane < +0
)


def tetrad_program(n: int) -> xa.Prog:
    p = xa.Prog().emit(xa.cfg(5, 1), xa.pop(0, xa.ACC_CLEAR), xa.push(0), xa.li(7, n))
    p.label("loop").emit(xa.pop(0, xa.ACC_ACCUM), xa.push(0), xa.addi(7, 7, -1)).bne(7, 0, "loop")
    p.emit(xa.li(8, 1), xa.kick(8), xa.li(6, 0xF), xa.wait(6), xa.flush(5), xa.ectx())
    return p


def flush_word(c: int) -> int:
    """Cell ``c``'s FLUSH word: {tag[18:15], dest[14:0]}."""
    return ((0x3 + c) << 15) | (0x0100 * (c + 1) + 0x2A)


@dataclass
class CellRun:
    """One cell's run: its model, the lines it is fed, the expected results."""
    model: CellModel
    word: int
    lines: List[int]
    specs: List[list]

    @property
    def dest(self) -> int:
        return self.word & 0x7FFF

    @property
    def tag(self) -> int:
        return self.word >> 15


def build_runs(rng, n_ctx: int, count: int) -> List[CellRun]:
    """Per cell: CLEAR + ``count`` ACCUMULATE invocations of random bf16
    lines, and the golden result spec of each."""
    runs = []
    for c in range(n_ctx):
        m = CELLS[c % len(CELLS)]()
        lines, specs = [], []
        for acc in [xa.ACC_CLEAR] + [xa.ACC_ACCUM] * count:
            a = bf16_line(rng)
            b = bf16_line(rng) if m.op_lines == 2 else 0
            lines += [a, b] if m.op_lines == 2 else [a]
            specs.append(m.step(a, b, acc))
        runs.append(CellRun(m, flush_word(c), lines, specs))
    return runs
