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

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_fub_bfm import fub_consumer, fub_producer   # noqa: E402


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
        self._build_bfms()
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

    def _build_bfms(self, profile="backtoback"):
        """BFMs on both sides of the CDC. Each is bound to ITS OWN clock --
        cmd/wd/rd are ctl_clk, pcmd/pwd/prd are dfi_clk. Getting that wrong
        is the whole hazard this fub exists to test, so it is explicit.

        init_start_i / pinit_complete_i are level handshake-free control
        signals (no ready), so they stay hand-driven.
        """
        ctl, dfi = self.dut.ctl_clk, self.dut.dfi_clk
        self.cmd_bfm = fub_producer(
            self.dut, "cmd", ctl, profile=profile, log=self.log,
            valid="cmd_valid_i", ready="cmd_ready_o",
            fields={'data': ("cmd_data_i", max(1, len(self.dut.cmd_data_i)))})
        self.wd_bfm = fub_producer(
            self.dut, "wd", ctl, profile=profile, log=self.log,
            valid="wd_valid_i", ready="wd_ready_o",
            fields={'data': ("wd_data_i", max(1, len(self.dut.wd_data_i)))})
        self.prd_bfm = fub_producer(
            self.dut, "prd", dfi, profile=profile, log=self.log,
            valid="prd_valid_i", ready="prd_ready_o",
            fields={'data': ("prd_data_i", max(1, len(self.dut.prd_data_i)))})
        self.rd_bfm = fub_consumer(
            self.dut, "rd", ctl, profile=profile, log=self.log,
            valid="rd_valid_o", ready="rd_ready_i",
            fields={'data': ("rd_data_o", max(1, len(self.dut.rd_data_o)))})
        self.pcmd_bfm = fub_consumer(
            self.dut, "pcmd", dfi, profile=profile, log=self.log,
            valid="pcmd_valid_o", ready="pcmd_ready_i",
            fields={'data': ("pcmd_data_o", max(1, len(self.dut.pcmd_data_o)))})
        self.pwd_bfm = fub_consumer(
            self.dut, "pwd", dfi, profile=profile, log=self.log,
            valid="pwd_valid_o", ready="pwd_ready_i",
            fields={'data': ("pwd_data_o", max(1, len(self.dut.pwd_data_o)))})

    def _idle(self):
        # Every valid/ready port is BFM-owned; only the two level controls
        # remain.
        self.dut.init_start_i.value = 0
        self.dut.pinit_complete_i.value = 0

    # ---- sinks --------------------------------------------------------------
    async def _sink(self, bfm, clk, out):
        """Drain a consumer BFM's captures into `out`, in order."""
        while True:
            await RisingEdge(clk)
            while bfm._recvQ:
                out.append(bfm._recvQ.popleft().data)

    async def _phy_cmd_sink(self):
        await self._sink(self.pcmd_bfm, self.dut.dfi_clk, self.cmd_seen)

    async def _phy_wd_sink(self):
        await self._sink(self.pwd_bfm, self.dut.dfi_clk, self.wd_seen)

    async def _ctl_rd_sink(self):
        await self._sink(self.rd_bfm, self.dut.ctl_clk, self.rd_seen)

    # ---- drivers ------------------------------------------------------------
    async def push_cmd(self, vals):
        for v in vals:
            await self.cmd_bfm.send(self.cmd_bfm.create_packet(data=v))

    async def push_wd(self, vals):
        for v in vals:
            await self.wd_bfm.send(self.wd_bfm.create_packet(data=v))

    async def push_rd(self, vals):
        for v in vals:
            await self.prd_bfm.send(self.prd_bfm.create_packet(data=v))
