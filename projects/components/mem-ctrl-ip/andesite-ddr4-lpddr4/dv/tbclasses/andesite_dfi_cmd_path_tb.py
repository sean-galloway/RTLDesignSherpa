# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 seang galloway

"""Testbench for `andesite_dfi_cmd_path` (TASK-016 t3).

Drives the widened {ap,col,row,bg,bank,rank,op} word through the valid/ready
port and reads the REGISTERED DFI pin vector plus the fire strobes. The pin
golden table is the P1 formatter suite's anchored set (MAS Table 2.3 /
docs/kmaps/generated/01_ddr4_command_table.md) -- this block's contract is
that the pipeline preserves the formatter's encoding exactly, one cycle
later, with the MRS/ZQCL payload arriving on the stream ROW field.
"""

import os
import subprocess
import sys

import cocotb
from cocotb.triggers import RisingEdge, Timer

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = os.path.join(_repo_root, "bin")
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

from TBClasses.shared.tbbase import TBBase    # noqa: E402

# dram_op_e (andesite_pkg)
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x0, 0x1, 0x2, 0x3, 0x4, 0x5
OP_PRE, OP_PREA, OP_REF, OP_REFPB = 0x6, 0x7, 0x8, 0x9
OP_MRS, OP_ZQCS, OP_ZQCL = 0xA, 0xB, 0xC

# P1 formatter golden (MAS Table 2.3), reused verbatim from
# test_andesite_dfi_cmd_formatter: (op, bank, bg, row, col) ->
# (cs, act, ras, cas, we, bank, bg, address)
GOLDEN = [
    (OP_NOP,  1, 2, 0x1234, 0x55,  (0, 1, 1, 1, 1, 1, 2, 0x55)),
    (OP_ACT,  1, 2, 0x155,  0x0,   (0, 0, 1, 1, 1, 1, 2, 0x155)),
    (OP_RD,   3, 1, 0x0,    0x2AA, (0, 1, 1, 0, 1, 3, 1, 0x2AA)),
    (OP_WR,   3, 1, 0x0,    0x2AA, (0, 1, 1, 0, 0, 3, 1, 0x2AA)),
    (OP_RDA,  3, 1, 0x0,    0x401, (0, 1, 1, 0, 1, 3, 1, 0x401)),
    (OP_MRS,  3, 0, 0x0,    0x14,  (0, 0, 0, 0, 0, 3, 0, 0x14)),
    (OP_REF,  0, 0, 0x0,    0x0,   (0, 0, 0, 0, 1, 0, 0, 0x0)),
    (OP_PRE,  2, 0, 0x0,    0x0,   (0, 1, 0, 1, 0, 2, 0, 0x0)),
    (OP_PREA, 2, 0, 0x0,    0x400, (0, 1, 0, 1, 0, 2, 0, 0x400)),
    (OP_ZQCS, 0, 0, 0x0,    0x0,   (0, 1, 1, 1, 0, 0, 0, 0x0)),
    (OP_ZQCL, 0, 0, 0x0,    0x400, (0, 1, 1, 1, 0, 0, 0, 0x400)),
]


class AndesiteDfiCmdPathTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_BANKS = int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH = int(os.environ.get('ROW_WIDTH', '14'))
        self.COL_WIDTH = int(os.environ.get('COL_WIDTH', '10'))
        self.RKW = 1
        self.BKW = max(1, (self.NUM_BANKS - 1).bit_length())
        self.BGW = 2
        self.OP_W = 5            # andesite_pkg widened dram_op_e one bit (OP_MPC)
        self.CMD_DW = (self.OP_W + self.RKW + self.BKW + self.BGW
                       + self.ROW_WIDTH + self.COL_WIDTH + 1)
        self.pins = []           # registered pin captures, one per accept
        self.strobes = []        # (wr_fire, rd_fire) per accepted beat window

    async def setup(self):
        await self.start_clock('dfi_clk', freq=10, units='ns')
        self.dut.dfi_rstn.value = 0
        self.dut.cmd_valid_i.value = 0
        self.dut.cmd_data_i.value = 0
        self.dut.memtype_i.value = 2          # MEMTYPE_DDR4
        self.dut.parity_en_i.value = 0
        self.dut.rd_op_ready_i.value = 1
        self.dut.wr_op_ready_i.value = 1
        await self.wait_clocks('dfi_clk', 4)
        self.dut.dfi_rstn.value = 1
        await self.wait_clocks('dfi_clk', 2)

    def pack(self, op, bank=0, bg=0, row=0, col=0, ap=0, rank=0):
        word = (ap & 1)
        word = (word << self.COL_WIDTH) | (col & ((1 << self.COL_WIDTH) - 1))
        word = (word << self.ROW_WIDTH) | (row & ((1 << self.ROW_WIDTH) - 1))
        word = (word << self.BGW) | (bg & ((1 << self.BGW) - 1))
        word = (word << self.BKW) | (bank & ((1 << self.BKW) - 1))
        word = (word << self.RKW) | (rank & ((1 << self.RKW) - 1))
        word = (word << self.OP_W) | (op & ((1 << self.OP_W) - 1))
        return word

    async def issue(self, op, bank=0, bg=0, row=0, col=0, ap=0):
        """One command, accepted on the next edge.

        Sampling point: one settle step AFTER the accept edge. The strobe
        flops and the formatter register on that same edge, so pins, fire
        strobes, and parity all show the command at that instant; the next
        edge (with valid deasserted) re-registers NOP and the strobes clear.
        Returns (pins, (wr_fire, rd_fire), parity) at the sampling instant.
        """
        d = self.dut
        d.cmd_data_i.value = self.pack(op, bank, bg, row, col, ap)
        d.cmd_valid_i.value = 1
        await RisingEdge(d.dfi_clk)          # accept edge
        await Timer(1, 'ps')                 # settle: registered outputs show it
        pins = self.read_pins()
        strobes = (int(d.wr_fire_o.value), int(d.rd_fire_o.value))
        parity = int(d.dfi_parity_in_o.value)
        d.cmd_valid_i.value = 0
        d.cmd_data_i.value = 0
        await RisingEdge(d.dfi_clk)          # NOP re-registers; ready next issue
        return pins, strobes, parity

    def read_pins(self):
        d = self.dut
        return (int(d.dfi_cs_o.value), int(d.dfi_act_n_o.value),
                int(d.dfi_ras_n_o.value), int(d.dfi_cas_n_o.value),
                int(d.dfi_we_n_o.value), int(d.dfi_bank_o.value),
                int(d.dfi_bg_o.value), int(d.dfi_address_o.value))

    async def accepted(self):
        return (int(self.dut.cmd_valid_i.value)
                and int(self.dut.cmd_ready_o.value))
