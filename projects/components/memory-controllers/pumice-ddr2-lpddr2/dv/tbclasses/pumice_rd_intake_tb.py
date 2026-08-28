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

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_axi_bfm import PumiceAxiBfm                    # noqa: E402
from tbclasses.pumice_fub_bfm import fub_consumer, fub_producer      # noqa: E402

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
        self._reads  = []          # in-flight BFM read tasks

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self._build_bfms()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._cam_model())
        cocotb.start_soon(self._snarf_server())
        cocotb.start_soon(self._dfi_server())
        cocotb.start_soon(self._drain_ar_push())
        cocotb.start_soon(self._mon_r())

    def _build_bfms(self, profile="backtoback"):
        """AXI4 read master on s_axi, a GAXI slave on the ar_push output and
        GAXI masters on the two read-data sources. Nothing here is driven by
        hand (PUMICE-014); the BFMs own valid/ready AND the payload."""
        self.axi = PumiceAxiBfm(self.dut, data_width=self.AXI_DATA_WIDTH,
                                bl_words=self.EXP_BEATS, clock=self.dut.aclk,
                                profile=profile, write=False, log=self.log)
        self.ar_push_bfm = fub_consumer(
            self.dut, "ar_push", self.dut.aclk, profile=profile, log=self.log,
            valid="ar_push_valid_o", ready="ar_push_ready_i",
            fields={'rank': ("ar_push_rank_o", max(1, (self.NUM_RANKS - 1).bit_length())),
                    'bank': ("ar_push_bank_o", self.BKW),
                    'row':  ("ar_push_row_o",  self.ROW_WIDTH),
                    'col':  ("ar_push_col_o",  self.COL_WIDTH),
                    'id':   ("ar_push_id_o",   8)})
        self.snarf_bfm = fub_producer(
            self.dut, "snarf_rd", self.dut.aclk, profile=profile, log=self.log,
            valid="snarf_rd_valid_i", ready="snarf_rd_ready_o",
            fields={'data': ("snarf_rd_data_i", self.AXI_DATA_WIDTH),
                    'last': ("snarf_rd_last_i", 1)})
        self.dfi_bfm = fub_producer(
            self.dut, "dfi_rd", self.dut.aclk, profile=profile, log=self.log,
            valid="dfi_rd_valid_i", ready="dfi_rd_ready_o",
            fields={'data': ("dfi_rd_data_i", self.AXI_DATA_WIDTH),
                    'last': ("dfi_rd_last_i", 1),
                    'resp': ("dfi_rd_resp_i", 2)})

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.bank_lsb_i.value  = 10   # ROW_MAJOR (bank_lsb == COL_WIDTH)
        self.dut.hash_en_i.value   = 0
        self.dut.hash_seed_i.value = 0
        # NO interface signals here: the AXI read master owns s_axi_* (rready
        # included), the GAXI slave owns ar_push_ready_i, and the two GAXI
        # masters own the snarf_rd_*/dfi_rd_* valid + payload. snarf_hit_i is
        # NOT an interface -- it is the combinational answer to the intake's
        # probe, so the CAM model below still drives it.
        self.dut.snarf_hit_i.value = 0

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
    async def _stream(self, q, bfm, with_resp=False):
        """Stream queued bursts out of a GAXI master, one packet per beat.

        The BFM sets valid and every payload field and honours the DUT's
        ready, so the old hand-rolled beat loop (drive data/last/valid, then
        spin on ready) is gone entirely.
        """
        while True:
            while not q:
                await RisingEdge(self.dut.aclk)
            item = q.popleft()
            burst = item[0] if with_resp else item
            resp = item[1] if with_resp else None
            n = len(burst)
            for i, d in enumerate(burst):
                kw = {'data': d, 'last': 1 if i == n - 1 else 0}
                if with_resp:
                    kw['resp'] = resp
                await bfm.send(bfm.create_packet(**kw))

    async def _snarf_server(self):
        await self._stream(self.snarf_q, self.snarf_bfm)

    async def _dfi_server(self):
        await self._stream(self.dfi_q, self.dfi_bfm, with_resp=True)

    # ---- monitors -----------------------------------------------------------
    # Reshapes what the GAXI slave already captured into the tuple form the
    # tests assert on -- reads a BFM queue, does not touch the bus.
    async def _drain_ar_push(self):
        while True:
            await RisingEdge(self.dut.aclk)
            while self.ar_push_bfm._recvQ:
                p = self.ar_push_bfm._recvQ.popleft()
                self.ar_push.append((p.rank, p.bank, p.row, p.col, p.id))

    # R is OBSERVED, not driven: the AXI read master owns rready, but the
    # sequence result does not carry per-beat rid/rlast/rresp, which the
    # tests check. Observing is not poking.
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

        # Issue the AR through the read master. It runs as a background task
        # because the R data only appears once the snarf/dfi server streams
        # it, and callers issue several ARs before checking; blocking here
        # would serialise what the DUT is meant to overlap. Return once the
        # decoded command shows up on ar_push -- read off the BFM queue.
        want = len(self.ar_push) + 1
        self._reads.append(cocotb.start_soon(self.axi.read(addr, rid)))
        for _ in range(2000):
            await RisingEdge(self.dut.aclk)
            if len(self.ar_push) >= want:
                break
