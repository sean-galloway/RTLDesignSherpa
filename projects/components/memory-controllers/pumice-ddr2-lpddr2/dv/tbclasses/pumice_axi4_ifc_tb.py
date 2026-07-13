# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Integration testbench for `pumice_axi4_ifc`.

The TB plays three external roles at once:
  * host AXI4 master  (drive AW/W/AR, observe B/R)
  * scheduler         (read the CAM oldest ports; drive wr_commit / rd_issue)
  * DFI data path     (consume wr commit-data; produce rd return-data)

Flow proven:
  1. host write burst -> lands in the wr CAM (B returns via commit).
  2. host read to the SAME address -> SNARF hit -> R == written data.
  3. host read to an unwritten address -> MISS -> rd CAM -> scheduler issues +
     DFI returns -> R == DFI data.
  4. wr commit -> cm_rd stream == written data.
"""

import os
import sys
import subprocess
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402

BURST_INCR = 1


class PumiceAxi4IfcTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.AXI_DATA_WIDTH = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '64'))
        self.DRAM_BEAT_WIDTH = self.convert_to_int(os.environ.get('DRAM_BEAT_WIDTH', '64'))
        self.BL = self.convert_to_int(os.environ.get('BL', '4'))
        self.SW = self.AXI_DATA_WIDTH // 8
        self.GEAR = self.AXI_DATA_WIDTH // self.DRAM_BEAT_WIDTH
        self.EXP_BEATS = self.BL // self.GEAR
        self.b_ids = deque()
        self.r_out = deque()    # completed R bursts: list of (rid,rdata,rlast,rresp)
        self.cm_out = deque()   # completed wr commit bursts: list of data

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 6)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 6)
        cocotb.start_soon(self._mon_b())
        cocotb.start_soon(self._mon_r())
        cocotb.start_soon(self._mon_cm())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.bank_lsb_i.value  = 10   # ROW_MAJOR (bank_lsb == COL_WIDTH)
        self.dut.hash_en_i.value   = 0
        self.dut.hash_seed_i.value = 0
        for s in ['awid', 'awaddr', 'awlen', 'awsize', 'awburst', 'awlock', 'awcache',
                  'awprot', 'awqos', 'awregion', 'awuser', 'awvalid',
                  'wdata', 'wstrb', 'wlast', 'wuser', 'wvalid',
                  'arid', 'araddr', 'arlen', 'arsize', 'arburst', 'arlock', 'arcache',
                  'arprot', 'arqos', 'arregion', 'aruser', 'arvalid']:
            getattr(self.dut, f's_axi_{s}').value = 0
        self.dut.s_axi_awsize.value = (self.SW).bit_length() - 1
        self.dut.s_axi_arsize.value = (self.SW).bit_length() - 1
        self.dut.s_axi_awburst.value = BURST_INCR
        self.dut.s_axi_arburst.value = BURST_INCR
        self.dut.s_axi_bready.value = 1
        self.dut.s_axi_rready.value = 1
        # scheduler / DFI idle
        self.dut.wr_sched_lu_valid_i.value = 0
        self.dut.wr_sched_lu_bank_i.value = 0
        self.dut.wr_sched_lu_row_i.value = 0
        self.dut.wr_commit_valid_i.value = 0
        self.dut.wr_commit_slot_i.value = 0
        self.dut.wr_cm_rd_ready_i.value = 1
        self.dut.rd_sched_lu_valid_i.value = 0
        self.dut.rd_sched_lu_bank_i.value = 0
        self.dut.rd_sched_lu_row_i.value = 0
        self.dut.rd_issue_valid_i.value = 0
        self.dut.rd_issue_slot_i.value = 0
        self.dut.rd_dfi_ret_valid_i.value = 0
        self.dut.rd_dfi_ret_data_i.value = 0
        self.dut.rd_dfi_ret_resp_i.value = 0
        self.dut.rd_dfi_ret_last_i.value = 0

    # ---- monitors -----------------------------------------------------------
    async def _mon_b(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_bvalid.value) and int(self.dut.s_axi_bready.value):
                self.b_ids.append(int(self.dut.s_axi_bid.value))

    async def _mon_r(self):
        cur = []
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_rvalid.value) and int(self.dut.s_axi_rready.value):
                cur.append((int(self.dut.s_axi_rid.value), int(self.dut.s_axi_rdata.value),
                            int(self.dut.s_axi_rlast.value), int(self.dut.s_axi_rresp.value)))
                if int(self.dut.s_axi_rlast.value):
                    self.r_out.append(cur); cur = []

    async def _mon_cm(self):
        cur = []
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.wr_cm_rd_valid_o.value) and int(self.dut.wr_cm_rd_ready_i.value):
                cur.append(int(self.dut.wr_cm_rd_data_o.value))
                if int(self.dut.wr_cm_rd_last_o.value):
                    self.cm_out.append(cur); cur = []

    # ---- host AXI driver ----------------------------------------------------
    # await-then-check: transfer completes on the edge where ready is first 1
    # (valid held); deassert immediately after — no double-accept.
    async def _wait_ready(self, sig, name, bound=500):
        for _ in range(bound):
            await RisingEdge(self.dut.aclk)
            if int(sig.value) == 1:
                return
        raise AssertionError(f"handshake stuck: {name} never asserted")

    async def _drive_aw(self, addr, wid):
        self.dut.s_axi_awid.value = wid
        self.dut.s_axi_awaddr.value = addr
        self.dut.s_axi_awlen.value = self.EXP_BEATS - 1
        self.dut.s_axi_awvalid.value = 1
        await self._wait_ready(self.dut.s_axi_awready, "s_axi_awready")
        self.dut.s_axi_awvalid.value = 0

    async def _drive_w(self, data):
        n = len(data)
        for i, d in enumerate(data):
            self.dut.s_axi_wdata.value = d
            self.dut.s_axi_wstrb.value = (1 << self.SW) - 1
            self.dut.s_axi_wlast.value = 1 if i == n - 1 else 0
            self.dut.s_axi_wvalid.value = 1
            await self._wait_ready(self.dut.s_axi_wready, "s_axi_wready")
        self.dut.s_axi_wvalid.value = 0
        self.dut.s_axi_wlast.value = 0

    async def write(self, addr, wid, data):
        aw = cocotb.start_soon(self._drive_aw(addr, wid))
        w = cocotb.start_soon(self._drive_w(data))
        await aw
        await w

    async def read_ar(self, addr, rid):
        self.dut.s_axi_arid.value = rid
        self.dut.s_axi_araddr.value = addr
        self.dut.s_axi_arlen.value = self.EXP_BEATS - 1
        self.dut.s_axi_arvalid.value = 1
        await self._wait_ready(self.dut.s_axi_arready, "s_axi_arready")
        self.dut.s_axi_arvalid.value = 0

    # ---- scheduler / DFI roles ---------------------------------------------
    async def commit_wr(self):
        """Commit the oldest write; return the cm_rd burst."""
        for _ in range(200):
            if int(self.dut.wr_oldest_valid_o.value):
                break
            await RisingEdge(self.dut.aclk)
        slot = int(self.dut.wr_oldest_slot_o.value)
        while int(self.dut.wr_commit_ready_o.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.wr_commit_slot_i.value = slot
        self.dut.wr_commit_valid_i.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.wr_commit_valid_i.value = 0
        for _ in range(200):
            if self.cm_out:
                return self.cm_out.popleft()
            await RisingEdge(self.dut.aclk)
        return None

    async def service_rd(self, data, resp=0):
        """Issue the oldest pending read, then drive its DFI return data."""
        for _ in range(200):
            if int(self.dut.rd_oldest_valid_o.value):
                break
            await RisingEdge(self.dut.aclk)
        slot = int(self.dut.rd_oldest_slot_o.value)
        while int(self.dut.rd_issue_ready_o.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.rd_issue_slot_i.value = slot
        self.dut.rd_issue_valid_i.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.rd_issue_valid_i.value = 0
        # DFI return stream
        n = len(data)
        for i, d in enumerate(data):
            self.dut.rd_dfi_ret_data_i.value = d
            self.dut.rd_dfi_ret_resp_i.value = resp
            self.dut.rd_dfi_ret_last_i.value = 1 if i == n - 1 else 0
            self.dut.rd_dfi_ret_valid_i.value = 1
            await RisingEdge(self.dut.aclk)
            while int(self.dut.rd_dfi_ret_ready_o.value) == 0:
                await RisingEdge(self.dut.aclk)
        self.dut.rd_dfi_ret_valid_i.value = 0
        self.dut.rd_dfi_ret_last_i.value = 0

    async def wait_r(self, timeout=400):
        for _ in range(timeout):
            if self.r_out:
                return self.r_out.popleft()
            await RisingEdge(self.dut.aclk)
        return None
