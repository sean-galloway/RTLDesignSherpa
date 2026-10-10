# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Testbench for `andesite_dfi_cmd_formatter`.

Drives the internal-op interface and samples the DFI 4.0 command pins after
the registered pipeline latency. Expected values come from the kmap anchor
(docs/kmaps/generated/01_ddr4_command_table.md, from MAS Table 2.3) -- the
truth table is the contract, not an implementation detail.
"""

import subprocess
import sys

from cocotb.triggers import RisingEdge

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = _repo_root + "/bin"
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

# dram_op_e (andesite_pkg) -- 5-bit encoding, carried values 0-15 + OP_MPC.
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x00, 0x01, 0x02, 0x03, 0x04, 0x05
OP_PRE, OP_PREA, OP_REF, OP_REFPB = 0x06, 0x07, 0x08, 0x09
OP_MRS, OP_ZQCS, OP_ZQCL = 0x0A, 0x0B, 0x0C
OP_NAMES = {OP_NOP: 'NOP', OP_ACT: 'ACT', OP_RD: 'RD', OP_RDA: 'RDA',
            OP_WR: 'WR', OP_WRA: 'WRA', OP_PRE: 'PRE', OP_PREA: 'PREA',
            OP_REF: 'REF', OP_REFPB: 'REFPB', OP_MRS: 'MRS',
            OP_ZQCS: 'ZQCS', OP_ZQCL: 'ZQCL'}


class AndesiteDfiCmdFormatterTB:
    def __init__(self, dut):
        self.dut = dut

    async def setup_clock(self, period_ns=10):
        import cocotb
        from cocotb.clock import Clock
        self._clk = Clock(self.dut.clk, period_ns, units="ns")
        await cocotb.start(self._clk.start())

    async def reset(self):
        self.dut.rst_n.value = 0
        self.dut.op_i.value = 0
        self.dut.bank_i.value = 0
        self.dut.bg_i.value = 0
        self.dut.row_i.value = 0
        self.dut.col_i.value = 0
        self.dut.rank_i.value = 0
        self.dut.memtype_i.value = 0x2      # MEMTYPE_DDR4
        self.dut.parity_en_i.value = 0
        for _ in range(3):
            await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)

    async def issue(self, op, bank=0, bg=0, row=0, col=0, rank=0):
        """Present a command and return the sampled DFI pin tuple after the
        registered pipeline latency (2 edges: one to capture, one to appear)."""
        self.dut.op_i.value = op
        self.dut.bank_i.value = bank
        self.dut.bg_i.value = bg
        self.dut.row_i.value = row
        self.dut.col_i.value = col
        self.dut.rank_i.value = rank
        await RisingEdge(self.dut.clk)
        await RisingEdge(self.dut.clk)
        d = self.dut
        return (int(d.dfi_cs.value), int(d.dfi_act_n.value),
                int(d.dfi_ras_n.value), int(d.dfi_cas_n.value),
                int(d.dfi_we_n.value), int(d.dfi_bank.value),
                int(d.dfi_bg.value), int(d.dfi_address.value))
