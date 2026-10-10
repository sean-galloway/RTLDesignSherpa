# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Testbench for `andesite_mode_register`.

Drives the write/readback port and samples the derived outputs. Expected
values for the six review-verified bit selects are stated absolutely; the
Q1-placeholder selects (DBI enables, MPR page, LPDDR4 ODT) are asserted
RELATIVE to the same localparam constant the RTL uses -- the test verifies
the wiring, and the Q1 cold-storage read changes one constant on both sides.
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

MEMTYPE_DDR4 = 0x2

# Q1-placeholder bit selects -- MUST match the RTL's Q1 localparam block.
# The review verified FGR (MR3[8:6]), RTT_NOM (MR1[10:8]), RTT_WR (MR2[11:9]),
# RTT_PARK (MR5[8:6]), CA parity latency (MR5[2:0]), write leveling (MR1[7]).
# These four are wiring-only until the JESD79-4/JESD209-4 cold-storage read.
Q1_MR5_RD_DBI_BIT = 12
Q1_MR5_WR_DBI_BIT = 11
Q1_MR3_MPR_PAGE_LSB = 1   # 2-bit field at [2:1]


class AndesiteModeRegisterTB:
    def __init__(self, dut):
        self.dut = dut

    async def setup_clock(self, period_ns=10):
        import cocotb
        from cocotb.clock import Clock
        self._clk = Clock(self.dut.clk, period_ns, units="ns")
        await cocotb.start(self._clk.start())

    async def reset(self):
        self.dut.rst_n.value = 0
        self.dut.memtype_i.value = MEMTYPE_DDR4
        self.dut.rank_i.value = 0
        self.dut.wr_en_i.value = 0
        self.dut.wr_addr_i.value = 0
        self.dut.wr_data_i.value = 0
        self.dut.rd_en_i.value = 0
        self.dut.rd_addr_i.value = 0
        for _ in range(3):
            await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)

    async def write_mr(self, addr, data):
        self.dut.wr_addr_i.value = addr
        self.dut.wr_data_i.value = data
        self.dut.wr_en_i.value = 1
        await RisingEdge(self.dut.clk)
        self.dut.wr_en_i.value = 0
        await RisingEdge(self.dut.clk)

    async def read_mr(self, addr):
        self.dut.rd_addr_i.value = addr
        self.dut.rd_en_i.value = 1
        await RisingEdge(self.dut.clk)
        self.dut.rd_en_i.value = 0
        await RisingEdge(self.dut.clk)
        return int(self.dut.rd_data_o.value)
