# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_wr_intake` — the dumb AXI4 write intake.

Contract under test (see rtl/PUMICE_AXI4_IFC_UARCH.md):
  * One AXI burst == one DFI burst: (awlen+1)*GEAR == BL.
  * AW metadata decodes to {rank,bank,row,col} on aw_push (row-major here).
  * W beats pass through the wr-data FIFO unchanged: {data,strb,last}.
  * B is commit-driven: emitted only when the TB (acting as downstream) pulses
    wr_done — one B per burst, bid == awid.
  * Ragged burst ((awlen+1)*GEAR != BL) -> aw_push_err + bresp=SLVERR.

The TB drives the AXI slave port directly and plays the downstream consumer:
aw_push_ready / wdata_ready / bready held high; monitors capture each boundary.
"""

import os
import sys
import random
import subprocess

import cocotb
from cocotb.triggers import RisingEdge

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402

RESP_OKAY   = 0
RESP_SLVERR = 2
BURST_INCR  = 1


class PumiceWrIntakeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.AXI_DATA_WIDTH = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '64'))
        self.DRAM_BEAT_WIDTH = self.convert_to_int(os.environ.get('DRAM_BEAT_WIDTH', '64'))
        self.NUM_RANKS   = self.convert_to_int(os.environ.get('NUM_RANKS', '1'))
        self.NUM_BANKS   = self.convert_to_int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH   = self.convert_to_int(os.environ.get('ROW_WIDTH', '14'))
        self.COL_WIDTH   = self.convert_to_int(os.environ.get('COL_WIDTH', '10'))
        self.BYTE_OFFSET_WIDTH = self.convert_to_int(os.environ.get('BYTE_OFFSET_WIDTH', '3'))
        self.BL          = self.convert_to_int(os.environ.get('BL', '4'))
        self.SW          = self.AXI_DATA_WIDTH // 8
        self.GEAR        = self.AXI_DATA_WIDTH // self.DRAM_BEAT_WIDTH
        self.EXP_BEATS   = self.BL // self.GEAR
        self.BKW         = max(1, (self.NUM_BANKS - 1).bit_length())

        # boundary capture queues
        self.aw_push = []    # (rank,bank,row,col,id,err)
        self.wdata   = []    # (data,strb,last)
        self.bresp   = []    # (bid,bresp)

    # ---- three mandatory methods --------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._mon_aw_push())
        cocotb.start_soon(self._mon_wdata())
        cocotb.start_soon(self._mon_b())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.bank_lsb_i.value  = 10   # ROW_MAJOR (bank_lsb == COL_WIDTH)
        self.dut.hash_en_i.value   = 0
        self.dut.hash_seed_i.value = 0
        self.dut.s_axi_awid.value = 0
        self.dut.s_axi_awaddr.value = 0
        self.dut.s_axi_awlen.value = 0
        self.dut.s_axi_awsize.value = (self.AXI_DATA_WIDTH // 8).bit_length() - 1
        self.dut.s_axi_awburst.value = BURST_INCR
        self.dut.s_axi_awlock.value = 0
        self.dut.s_axi_awcache.value = 0
        self.dut.s_axi_awprot.value = 0
        self.dut.s_axi_awqos.value = 0
        self.dut.s_axi_awregion.value = 0
        self.dut.s_axi_awuser.value = 0
        self.dut.s_axi_awvalid.value = 0
        self.dut.s_axi_wdata.value = 0
        self.dut.s_axi_wstrb.value = 0
        self.dut.s_axi_wlast.value = 0
        self.dut.s_axi_wuser.value = 0
        self.dut.s_axi_wvalid.value = 0
        self.dut.s_axi_bready.value = 1
        # downstream always ready
        self.dut.aw_push_ready_i.value = 1
        self.dut.wdata_ready_i.value = 1
        self.dut.wr_done_valid_i.value = 0
        self.dut.wr_done_id_i.value = 0
        self.dut.wr_done_resp_i.value = 0

    # ---- monitors -----------------------------------------------------------
    async def _mon_aw_push(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.aw_push_valid_o.value) and int(self.dut.aw_push_ready_i.value):
                self.aw_push.append((
                    int(self.dut.aw_push_rank_o.value),
                    int(self.dut.aw_push_bank_o.value),
                    int(self.dut.aw_push_row_o.value),
                    int(self.dut.aw_push_col_o.value),
                    int(self.dut.aw_push_id_o.value),
                    int(self.dut.aw_push_err_o.value),
                ))

    async def _mon_wdata(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.wdata_valid_o.value) and int(self.dut.wdata_ready_i.value):
                self.wdata.append((
                    int(self.dut.wdata_o.value),
                    int(self.dut.wstrb_o.value),
                    int(self.dut.wlast_o.value),
                ))

    async def _mon_b(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_bvalid.value) and int(self.dut.s_axi_bready.value):
                self.bresp.append((
                    int(self.dut.s_axi_bid.value),
                    int(self.dut.s_axi_bresp.value),
                ))

    # ---- expected address decode (row-major mirror of addr_mapper) ----------
    def decode(self, addr):
        word = addr >> self.BYTE_OFFSET_WIDTH
        col  = word & ((1 << self.COL_WIDTH) - 1)
        bank = (word >> self.COL_WIDTH) & ((1 << self.BKW) - 1)
        row  = (word >> (self.COL_WIDTH + self.BKW)) & ((1 << self.ROW_WIDTH) - 1)
        rank = 0
        if self.NUM_RANKS > 1:
            rank = (word >> (self.COL_WIDTH + self.BKW + self.ROW_WIDTH)) \
                   & ((1 << (self.NUM_RANKS - 1).bit_length()) - 1)
        return (rank, bank, row, col)

    # ---- driver -------------------------------------------------------------
    async def drive_aw(self, addr, wid, beats):
        self.dut.s_axi_awid.value = wid
        self.dut.s_axi_awaddr.value = addr
        self.dut.s_axi_awlen.value = beats - 1
        self.dut.s_axi_awvalid.value = 1
        await RisingEdge(self.dut.aclk)
        while int(self.dut.s_axi_awready.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.s_axi_awvalid.value = 0

    async def drive_w(self, data_list, strb=None):
        n = len(data_list)
        for i, d in enumerate(data_list):
            self.dut.s_axi_wdata.value = d
            self.dut.s_axi_wstrb.value = (1 << self.SW) - 1 if strb is None else strb[i]
            self.dut.s_axi_wlast.value = 1 if i == n - 1 else 0
            self.dut.s_axi_wvalid.value = 1
            await RisingEdge(self.dut.aclk)
            while int(self.dut.s_axi_wready.value) == 0:
                await RisingEdge(self.dut.aclk)
        self.dut.s_axi_wvalid.value = 0
        self.dut.s_axi_wlast.value = 0

    async def pulse_wr_done(self, wid, resp=RESP_OKAY):
        self.dut.wr_done_valid_i.value = 1
        self.dut.wr_done_id_i.value = wid
        self.dut.wr_done_resp_i.value = resp
        await RisingEdge(self.dut.aclk)
        self.dut.wr_done_valid_i.value = 0

    async def write_burst(self, addr, wid, data_list, strb=None):
        """Drive AW then the W beats concurrently (AW held until accepted)."""
        aw = cocotb.start_soon(self.drive_aw(addr, wid, len(data_list)))
        w  = cocotb.start_soon(self.drive_w(data_list, strb))
        await aw
        await w
