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

Everything is BFM-driven (PUMICE-014) -- the TB sets no interface signals:
  * `s_axi_*` write channels: AXI4MasterWrite via PumiceAxiBfm (owns bready).
  * `aw_push_*` / `wdata_*`: GAXI SLAVE BFMs. They drive `ready` with a real
    randomizer profile instead of a hardwired 1, and capture the payload --
    so the old hand-rolled monitor coroutines are gone with the hand
    driving. Pass a backpressure profile to prove the DUT tolerates a
    stalled downstream, which `ready = 1` never could.
  * `wr_done_*` has NO ready -- it is a valid-only strobe, not a handshake,
    so no BFM can pace it; it stays a small named method.
  * B is observed by a read-only monitor: the AXI master owns bready, and
    the sequence result does not carry bresp, which the SLVERR check needs.
    Observing is not poking.
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

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_axi_bfm import PumiceAxiBfm      # noqa: E402
from tbclasses.pumice_fub_bfm import fub_consumer      # noqa: E402

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
        self._writes = []    # in-flight BFM write tasks (B is commit-driven)

    # ---- three mandatory methods --------------------------------------------
    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self._build_bfms()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._drain_aw_push())
        cocotb.start_soon(self._drain_wdata())
        cocotb.start_soon(self._mon_b())

    def _build_bfms(self, profile="backtoback"):
        """AXI4 write master on s_axi + GAXI slaves on the two fub outputs."""
        self.axi = PumiceAxiBfm(self.dut, data_width=self.AXI_DATA_WIDTH,
                                bl_words=self.EXP_BEATS, clock=self.dut.aclk,
                                profile=profile, read=False, log=self.log)
        self.aw_push_bfm = fub_consumer(
            self.dut, "aw_push", self.dut.aclk, profile=profile, log=self.log,
            valid="aw_push_valid_o", ready="aw_push_ready_i",
            fields={'rank': ("aw_push_rank_o", max(1, (self.NUM_RANKS - 1).bit_length())),
                    'bank': ("aw_push_bank_o", self.BKW),
                    'row':  ("aw_push_row_o",  self.ROW_WIDTH),
                    'col':  ("aw_push_col_o",  self.COL_WIDTH),
                    'id':   ("aw_push_id_o",   8),
                    'err':  ("aw_push_err_o",  1)})
        self.wdata_bfm = fub_consumer(
            self.dut, "wdata", self.dut.aclk, profile=profile, log=self.log,
            valid="wdata_valid_o", ready="wdata_ready_i",
            fields={'data': ("wdata_o", self.AXI_DATA_WIDTH),
                    'strb': ("wstrb_o", self.SW),
                    'last': ("wlast_o", 1)})

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.bank_lsb_i.value  = 10   # ROW_MAJOR (bank_lsb == COL_WIDTH)
        self.dut.hash_en_i.value   = 0
        self.dut.hash_seed_i.value = 0
        # NO interface signals here. The AXI4 master owns every s_axi_*
        # (bready included) and the GAXI slaves own aw_push_ready_i /
        # wdata_ready_i. A second driver on a BFM-owned signal is a
        # conflict, not a convenience.
        self.dut.wr_done_valid_i.value = 0
        self.dut.wr_done_id_i.value = 0
        self.dut.wr_done_resp_i.value = 0

    # ---- monitors -----------------------------------------------------------
    # The two drains below only RESHAPE what the GAXI slaves already
    # captured into the tuple form the tests assert on -- they read a BFM
    # queue, they do not touch the bus.
    async def _drain_aw_push(self):
        while True:
            await RisingEdge(self.dut.aclk)
            while self.aw_push_bfm._recvQ:
                p = self.aw_push_bfm._recvQ.popleft()
                self.aw_push.append((p.rank, p.bank, p.row, p.col, p.id, p.err))

    async def _drain_wdata(self):
        while True:
            await RisingEdge(self.dut.aclk)
            while self.wdata_bfm._recvQ:
                p = self.wdata_bfm._recvQ.popleft()
                self.wdata.append((p.data, p.strb, p.last))

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
    async def pulse_wr_done(self, wid, resp=RESP_OKAY):
        self.dut.wr_done_valid_i.value = 1
        self.dut.wr_done_id_i.value = wid
        self.dut.wr_done_resp_i.value = resp
        await RisingEdge(self.dut.aclk)
        self.dut.wr_done_valid_i.value = 0

    async def write_burst(self, addr, wid, data_list, strb=None):
        """Issue one AXI write burst through the master BFM.

        Deliberately does NOT block through B: B is commit-driven here, so
        it only appears after the caller pulses wr_done. Blocking on the
        BFM write would deadlock against that. So the burst runs as a
        background task and we return once the fub outputs show it landed
        (one aw_push, then wdata quiescent) -- both read off the BFM
        queues, not off the bus.
        """
        want_aw = len(self.aw_push) + 1
        self._writes.append(cocotb.start_soon(self.axi.write(addr, data_list, wid)))
        for _ in range(2000):
            await RisingEdge(self.dut.aclk)
            if len(self.aw_push) >= want_aw:
                break
        # let the W beats drain: settle until the count stops moving
        stable, last = 0, len(self.wdata)
        while stable < 5:
            await RisingEdge(self.dut.aclk)
            if len(self.wdata) == last:
                stable += 1
            else:
                stable, last = 0, len(self.wdata)
