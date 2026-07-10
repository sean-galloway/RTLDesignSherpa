# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Dual-clock testbench for `pumice_dfi_cdc` — the single controller<->PHY CDC.

Two independent clocks (ctl_clk, dfi_clk at different rates). Checks every
crossing (all gaxi_fifo_async): cmd + wrdata (ctl->phy) and rddata (phy->ctl)
arrive lossless + in order; init_start/init_complete event tokens set their
sticky latches across the boundary.
"""

import os
import sys
import random
import subprocess
from collections import deque

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402


class PumiceDfiCdcTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.CMD_DW = self.convert_to_int(os.environ.get('CMD_DW', '32'))
        self.WD_DW  = self.convert_to_int(os.environ.get('WD_DW', '72'))
        self.RD_DW  = self.convert_to_int(os.environ.get('RD_DW', '66'))
        self.cmd_seen = deque()
        self.wd_seen  = deque()
        self.rd_seen  = deque()

    async def start(self, ctl_ns=10, dfi_ns=4):
        # Two ASYNCHRONOUS clocks at different rates.
        cocotb.start_soon(Clock(self.dut.ctl_clk, ctl_ns, units='ns').start())
        cocotb.start_soon(Clock(self.dut.dfi_clk, dfi_ns, units='ns').start())
        self._idle()
        self.dut.ctl_rstn.value = 0
        self.dut.dfi_rstn.value = 0
        for _ in range(6):
            await RisingEdge(self.dut.ctl_clk)
        self.dut.ctl_rstn.value = 1
        self.dut.dfi_rstn.value = 1
        for _ in range(4):
            await RisingEdge(self.dut.ctl_clk)
        cocotb.start_soon(self._phy_cmd_sink())
        cocotb.start_soon(self._phy_wd_sink())
        cocotb.start_soon(self._ctl_rd_sink())

    def _idle(self):
        self.dut.cmd_valid_i.value = 0
        self.dut.cmd_data_i.value = 0
        self.dut.wd_valid_i.value = 0
        self.dut.wd_data_i.value = 0
        self.dut.init_start_i.value = 0
        self.dut.rd_ready_i.value = 1
        self.dut.pcmd_ready_i.value = 1
        self.dut.pwd_ready_i.value = 1
        self.dut.prd_valid_i.value = 0
        self.dut.prd_data_i.value = 0
        self.dut.pinit_complete_i.value = 0

    # ---- sinks --------------------------------------------------------------
    async def _phy_cmd_sink(self):
        while True:
            await RisingEdge(self.dut.dfi_clk)
            if int(self.dut.pcmd_valid_o.value) and int(self.dut.pcmd_ready_i.value):
                self.cmd_seen.append(int(self.dut.pcmd_data_o.value))

    async def _phy_wd_sink(self):
        while True:
            await RisingEdge(self.dut.dfi_clk)
            if int(self.dut.pwd_valid_o.value) and int(self.dut.pwd_ready_i.value):
                self.wd_seen.append(int(self.dut.pwd_data_o.value))

    async def _ctl_rd_sink(self):
        while True:
            await RisingEdge(self.dut.ctl_clk)
            if int(self.dut.rd_valid_o.value) and int(self.dut.rd_ready_i.value):
                self.rd_seen.append(int(self.dut.rd_data_o.value))

    # ---- drivers ------------------------------------------------------------
    async def push_cmd(self, vals):
        for v in vals:
            self.dut.cmd_data_i.value = v
            self.dut.cmd_valid_i.value = 1
            await RisingEdge(self.dut.ctl_clk)
            while int(self.dut.cmd_ready_o.value) == 0:
                await RisingEdge(self.dut.ctl_clk)
        self.dut.cmd_valid_i.value = 0

    async def push_wd(self, vals):
        for v in vals:
            self.dut.wd_data_i.value = v
            self.dut.wd_valid_i.value = 1
            await RisingEdge(self.dut.ctl_clk)
            while int(self.dut.wd_ready_o.value) == 0:
                await RisingEdge(self.dut.ctl_clk)
        self.dut.wd_valid_i.value = 0

    async def push_rd(self, vals):
        for v in vals:
            self.dut.prd_data_i.value = v
            self.dut.prd_valid_i.value = 1
            await RisingEdge(self.dut.dfi_clk)
            while int(self.dut.prd_ready_o.value) == 0:
                await RisingEdge(self.dut.dfi_clk)
        self.dut.prd_valid_i.value = 0
