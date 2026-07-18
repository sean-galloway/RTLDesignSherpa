# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_rd_intake` — dumb AXI4 read intake + snarf.

Mocks the two external sources:
  * wr CAM snarf: `snarf_hit_i` is driven per-AR (the TB knows each AR's hit
    status), and a snarf-data server streams the captured burst on the
    snarf_rd_* channel in snarf-admit order.
  * DFI read-return: a server streams DRAM bursts on dfi_rd_* in ar_push order.

Checks: MISS -> ar_push emitted + R sourced from DFI; HIT -> R sourced from
snarf (youngest); R returns in AR order across an interleave of both.
"""

import os
import sys
import subprocess
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, Edge, First

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402

RESP_OKAY = 0
BURST_INCR = 1


class PumiceRdIntakeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.AXI_DATA_WIDTH = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '64'))
        self.DRAM_BEAT_WIDTH = self.convert_to_int(os.environ.get('DRAM_BEAT_WIDTH', '64'))
        self.NUM_RANKS = self.convert_to_int(os.environ.get('NUM_RANKS', '1'))
        self.NUM_BANKS = self.convert_to_int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH = self.convert_to_int(os.environ.get('ROW_WIDTH', '14'))
        self.COL_WIDTH = self.convert_to_int(os.environ.get('COL_WIDTH', '10'))
        self.BYTE_OFFSET_WIDTH = self.convert_to_int(os.environ.get('BYTE_OFFSET_WIDTH', '3'))
        self.BL = self.convert_to_int(os.environ.get('BL', '4'))
        self.GEAR = self.AXI_DATA_WIDTH // self.DRAM_BEAT_WIDTH
        self.EXP_BEATS = self.BL // self.GEAR
        self.BKW = max(1, (self.NUM_BANKS - 1).bit_length())

        self.snarf_q = deque()     # bursts (list of beats) to stream on snarf_rd
        self.dfi_q   = deque()     # (burst, resp) to stream on dfi_rd
        self.ar_push = []          # (rank,bank,row,col,id)
        self.r_beats = []          # (rid, rdata, rlast, rresp)
        self.hitset  = set()       # decoded keys the mock wr CAM holds (snarf hits)

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._cam_model())
        cocotb.start_soon(self._snarf_server())
        cocotb.start_soon(self._dfi_server())
        cocotb.start_soon(self._mon_ar_push())
        cocotb.start_soon(self._mon_r())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.bank_lsb_i.value  = 10   # ROW_MAJOR (bank_lsb == COL_WIDTH)
        self.dut.hash_en_i.value   = 0
        self.dut.hash_seed_i.value = 0
        self.dut.s_axi_arid.value = 0
        self.dut.s_axi_araddr.value = 0
        self.dut.s_axi_arlen.value = 0
        self.dut.s_axi_arsize.value = (self.AXI_DATA_WIDTH // 8).bit_length() - 1
        self.dut.s_axi_arburst.value = BURST_INCR
        self.dut.s_axi_arlock.value = 0
        self.dut.s_axi_arcache.value = 0
        self.dut.s_axi_arprot.value = 0
        self.dut.s_axi_arqos.value = 0
        self.dut.s_axi_arregion.value = 0
        self.dut.s_axi_aruser.value = 0
        self.dut.s_axi_arvalid.value = 0
        self.dut.s_axi_rready.value = 1
        self.dut.snarf_hit_i.value = 0
        self.dut.snarf_rd_valid_i.value = 0
        self.dut.snarf_rd_data_i.value = 0
        self.dut.snarf_rd_last_i.value = 0
        self.dut.dfi_rd_valid_i.value = 0
        self.dut.dfi_rd_data_i.value = 0
        self.dut.dfi_rd_last_i.value = 0
        self.dut.dfi_rd_resp_i.value = 0
        self.dut.ar_push_ready_i.value = 1

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

    # ---- mock wr CAM: COMBINATIONAL snarf hit from the intake's own probe ---
    # React to probe changes (not the clock) so snarf_hit_i is valid within the
    # same cycle the intake makes its combinational admission decision.
    @staticmethod
    def _rd(sig):
        try:
            return int(sig.value)
        except Exception:
            return 0

    def _update_hit(self):
        if self._rd(self.dut.snarf_probe_valid_o):
            key = (self._rd(self.dut.snarf_probe_rank_o),
                   self._rd(self.dut.snarf_probe_bank_o),
                   self._rd(self.dut.snarf_probe_row_o),
                   self._rd(self.dut.snarf_probe_col_o))
            self.dut.snarf_hit_i.value = 1 if key in self.hitset else 0
        else:
            self.dut.snarf_hit_i.value = 0

    async def _cam_model(self):
        sigs = [self.dut.snarf_probe_valid_o, self.dut.snarf_probe_bank_o,
                self.dut.snarf_probe_row_o, self.dut.snarf_probe_col_o,
                self.dut.snarf_probe_rank_o]
        while True:
            self._update_hit()
            await First(*[Edge(s) for s in sigs])

    # ---- source servers -----------------------------------------------------
    async def _stream(self, q, val_sig, data_sig, last_sig, rdy_sig, resp_sig=None):
        while True:
            while not q:
                await RisingEdge(self.dut.aclk)
            item = q.popleft()
            burst = item[0] if resp_sig is not None else item
            resp = item[1] if resp_sig is not None else None
            n = len(burst)
            for i, d in enumerate(burst):
                data_sig.value = d
                last_sig.value = 1 if i == n - 1 else 0
                if resp_sig is not None:
                    resp_sig.value = resp
                val_sig.value = 1
                await RisingEdge(self.dut.aclk)
                while int(rdy_sig.value) == 0:
                    await RisingEdge(self.dut.aclk)
            val_sig.value = 0

    async def _snarf_server(self):
        await self._stream(self.snarf_q, self.dut.snarf_rd_valid_i,
                           self.dut.snarf_rd_data_i, self.dut.snarf_rd_last_i,
                           self.dut.snarf_rd_ready_o)

    async def _dfi_server(self):
        await self._stream(self.dfi_q, self.dut.dfi_rd_valid_i,
                           self.dut.dfi_rd_data_i, self.dut.dfi_rd_last_i,
                           self.dut.dfi_rd_ready_o, resp_sig=self.dut.dfi_rd_resp_i)

    # ---- monitors -----------------------------------------------------------
    async def _mon_ar_push(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.ar_push_valid_o.value) and int(self.dut.ar_push_ready_i.value):
                self.ar_push.append((
                    int(self.dut.ar_push_rank_o.value),
                    int(self.dut.ar_push_bank_o.value),
                    int(self.dut.ar_push_row_o.value),
                    int(self.dut.ar_push_col_o.value),
                    int(self.dut.ar_push_id_o.value),
                ))

    async def _mon_r(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_rvalid.value) and int(self.dut.s_axi_rready.value):
                self.r_beats.append((
                    int(self.dut.s_axi_rid.value),
                    int(self.dut.s_axi_rdata.value),
                    int(self.dut.s_axi_rlast.value),
                    int(self.dut.s_axi_rresp.value),
                ))

    # ---- driver -------------------------------------------------------------
    async def read_burst(self, addr, rid, hit, data, resp=RESP_OKAY):
        """Issue one AR; queue its data on the matching source. `hit` marks the
        address as present in the mock wr CAM (snarf) via the hit-set; the CAM
        model drives snarf_hit_i off the intake's probe (skid-latency safe)."""
        if hit:
            self.hitset.add(self.decode(addr))
            self.snarf_q.append(list(data))
        else:
            self.dfi_q.append((list(data), resp))

        self.dut.s_axi_arid.value = rid
        self.dut.s_axi_araddr.value = addr
        self.dut.s_axi_arlen.value = self.EXP_BEATS - 1
        self.dut.s_axi_arvalid.value = 1
        await RisingEdge(self.dut.aclk)
        while int(self.dut.s_axi_arready.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.s_axi_arvalid.value = 0
