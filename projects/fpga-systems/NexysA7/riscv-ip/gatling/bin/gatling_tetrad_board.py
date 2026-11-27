#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host-side driver for gatling build-tetrad (gatling_tetrad_nexysa7_top).

The memory system (programs, run control, per-context status) is
gatling_mem_bram at 0x0_0000, exactly as on build-bram, so this extends
GatlingBoard.  The cell harness sits at 0x4_0000; its offsets mirror the map
in the RTL header (rtl/gatling_tetrad_harness.sv) -- the one place an offset
is written down on the host side.

The bridge is INJECTABLE: the same driver runs the board over pyserial or a
cocotb sim over make_uart_channel (dv/tests/test_gatling_tetrad_board_uart.py).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple

from gatling_board import GatlingBoard

HARNESS_BASE = 0x4_0000
HARNESS_ID = 0x5454_5244          # "TTRD"
IN_DEPTH = 32
OUT_DEPTH = 32

CELL_REGS = {"FUNC": 0x00, "LINES": 0x04, "THR": 0x08, "BATCH": 0x0C, "FILL": 0x10,
             "DRAIN": 0x14, "FLUSH": 0x18, "KICK": 0x1C, "KICKCNT": 0x20,
             "STAT": 0x24, "CONSUMED": 0x28}
REG_ID = HARNESS_BASE + 0x100
REG_FLAGS = HARNESS_BASE + 0x104
REG_CLEAR = HARNESS_BASE + 0x108


def cell_reg(cell: int, name: str) -> int:
    return HARNESS_BASE + 0x40 * cell + CELL_REGS[name]


@dataclass(frozen=True)
class FlushCapture:
    valid: bool
    kicks_at_capture: int
    count: int
    tag: int
    dest: int

    @classmethod
    def decode(cls, v: int) -> "FlushCapture":
        return cls(valid=bool(v >> 31), kicks_at_capture=(v >> 24) & 0x7F,
                   count=(v >> 20) & 0xF, tag=(v >> 15) & 0xF, dest=v & 0x7FFF)


@dataclass(frozen=True)
class CellStat:
    stall_seen: int        # bit per funct3 the context was seen stalled on
    stalled: bool
    event: bool
    alu_err: bool
    underflow: bool

    @classmethod
    def decode(cls, v: int) -> "CellStat":
        return cls(stall_seen=v & 0xFF, stalled=bool(v >> 8 & 1), event=bool(v >> 9 & 1),
                   alu_err=bool(v >> 10 & 1), underflow=bool(v >> 11 & 1))


class TetradBoard(GatlingBoard):
    """build-tetrad over UART: GatlingBoard's program memory and run control,
    plus each cell's configuration, fill, drain and observers."""

    def harness_id(self) -> int:
        return self.read(REG_ID)

    def flags(self) -> Tuple[int, int, int]:
        """(event_flags, done, ctx_stalled), one bit per context."""
        v = self.read(REG_FLAGS)
        return v & 0xF, (v >> 4) & 0xF, (v >> 8) & 0xF

    def clear_observers(self) -> None:
        self.write(REG_CLEAR, 1)

    def configure(self, cell: int, func_sel: int, op_lines: int, threshold: int,
                  credit_batch: int) -> None:
        self.write(cell_reg(cell, "FUNC"), func_sel & 0x1FF)
        self.write(cell_reg(cell, "LINES"), op_lines & 0x3)
        self.write(cell_reg(cell, "THR"), threshold & 0xFFFF)
        self.write(cell_reg(cell, "BATCH"), credit_batch & 0xFFFF_FFFF)

    def occupancy(self, cell: int) -> Tuple[int, int]:
        """(input-memory lines, result-memory lines)."""
        v = self.read(cell_reg(cell, "FILL"))
        return v & 0xFF, (v >> 8) & 0xFF

    def fill(self, cell: int, line: int) -> None:
        self.write(cell_reg(cell, "FILL"), line & 0xFFFF_FFFF)

    def drain(self, cell: int) -> int:
        return self.read(cell_reg(cell, "DRAIN"))

    def flush(self, cell: int) -> FlushCapture:
        """Read (and so release) cell's captured FLUSH command."""
        return FlushCapture.decode(self.read(cell_reg(cell, "FLUSH")))

    def kick(self, cell: int) -> Tuple[int, int]:
        """(last kick value, kicks seen)."""
        return self.read(cell_reg(cell, "KICK")), self.read(cell_reg(cell, "KICKCNT"))

    def stat(self, cell: int) -> CellStat:
        return CellStat.decode(self.read(cell_reg(cell, "STAT")))

    def consumed(self, cell: int) -> int:
        return self.read(cell_reg(cell, "CONSUMED"))
