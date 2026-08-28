# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Integration testbench for `pumice_axi4_ifc`.

The TB plays three external roles at once:
  * host AXI4 master  (drive AW/W/AR, observe B/R)
  * scheduler         (derive oldest from the exported sch_valid/sch_older
                       vectors; drive wr_commit / rd_issue)
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

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_axi_bfm import PumiceAxiBfm                    # noqa: E402
from tbclasses.pumice_fub_bfm import fub_consumer, fub_producer      # noqa: E402

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
        self._axi_tasks = []    # in-flight BFM bursts (B/R are commit-driven)

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self._build_bfms()
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 6)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 6)
        cocotb.start_soon(self._mon_b())
        cocotb.start_soon(self._mon_r())
        cocotb.start_soon(self._drain_cm())

    def _build_bfms(self, profile="backtoback"):
        """Every interface on this DUT comes from a BFM (PUMICE-014):
        AXI4 masters on s_axi, GAXI masters on the two scheduler-side
        request ports and the DFI return stream, and a GAXI slave on the
        commit read-back. The BFMs drive valid/ready AND the payload."""
        self.axi = PumiceAxiBfm(self.dut, data_width=self.AXI_DATA_WIDTH,
                                bl_words=self.EXP_BEATS, clock=self.dut.aclk,
                                profile=profile, log=self.log)
        ptrw = max(1, len(self.dut.wr_commit_slot_i))
        self.wr_commit_bfm = fub_producer(
            self.dut, "wr_commit", self.dut.aclk, profile=profile, log=self.log,
            valid="wr_commit_valid_i", ready="wr_commit_ready_o",
            fields={'slot': ("wr_commit_slot_i", ptrw)})
        self.rd_issue_bfm = fub_producer(
            self.dut, "rd_issue", self.dut.aclk, profile=profile, log=self.log,
            valid="rd_issue_valid_i", ready="rd_issue_ready_o",
            fields={'slot': ("rd_issue_slot_i", max(1, len(self.dut.rd_issue_slot_i)))})
        self.dfi_ret_bfm = fub_producer(
            self.dut, "rd_dfi_ret", self.dut.aclk, profile=profile, log=self.log,
            valid="rd_dfi_ret_valid_i", ready="rd_dfi_ret_ready_o",
            fields={'data': ("rd_dfi_ret_data_i", self.AXI_DATA_WIDTH),
                    'resp': ("rd_dfi_ret_resp_i", 2),
                    'last': ("rd_dfi_ret_last_i", 1)})
        self.cm_rd_bfm = fub_consumer(
            self.dut, "wr_cm_rd", self.dut.aclk, profile=profile, log=self.log,
            valid="wr_cm_rd_valid_o", ready="wr_cm_rd_ready_i",
            fields={'data': ("wr_cm_rd_data_o", self.AXI_DATA_WIDTH),
                    'strb': ("wr_cm_rd_strb_o", self.SW),
                    'last': ("wr_cm_rd_last_o", 1)})

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.bank_lsb_i.value  = 10   # ROW_MAJOR (bank_lsb == COL_WIDTH)
        self.dut.hash_en_i.value   = 0
        self.dut.hash_seed_i.value = 0
        # NO interface signals here. Every valid/ready port on this DUT is
        # BFM-owned: s_axi_* by the AXI masters (bready/rready included),
        # wr_commit / rd_issue / rd_dfi_ret by GAXI masters, and
        # wr_cm_rd_ready_i by a GAXI slave. A second driver on a BFM-owned
        # signal is a conflict, not a convenience.
        # (the CAM lookup ports are internalized in pumice_axi4_ifc, tied to '0;
        #  the scheduler consumes the exported wr_sch_*_o / rd_sch_*_o vectors)

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

    # Reshapes what the GAXI slave captured into per-burst lists; reads a
    # BFM queue, does not touch the bus.
    async def _drain_cm(self):
        cur = []
        while True:
            await RisingEdge(self.dut.aclk)
            while self.cm_rd_bfm._recvQ:
                p = self.cm_rd_bfm._recvQ.popleft()
                cur.append(p.data)
                if p.last:
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

    async def write(self, addr, wid, data):
        """One AXI write burst via the master BFM.

        Runs as a background task: B here is commit-driven, so it only
        appears after the caller drives wr_commit. Blocking on the BFM
        write would deadlock against that.
        """
        self._axi_tasks.append(
            cocotb.start_soon(self.axi.write(addr, data, wid)))
        await self.wait_clocks('aclk', 2)

    async def read_ar(self, addr, rid):
        """Issue one AR via the master BFM; R arrives once service_rd runs."""
        self._axi_tasks.append(cocotb.start_soon(self.axi.read(addr, rid)))
        await self.wait_clocks('aclk', 2)

    # ---- scheduler / DFI roles ---------------------------------------------
    @staticmethod
    def _pick_oldest(valid_bits, older_bits, n):
        """Emulate the CAM's oldest-valid pick from the exported scheduler
        vectors (the dedicated oldest_* ports are internalized now). sch_valid[i]
        = schedulable; sch_older[i*n + j] == 1 iff entry i is older than entry j.
        The oldest schedulable slot is older than every OTHER schedulable slot."""
        valids = [i for i in range(n) if (valid_bits >> i) & 1]
        for i in valids:
            if all((older_bits >> (i * n + j)) & 1 for j in valids if j != i):
                return i
        return None

    def _wr_oldest_slot(self):
        n = len(self.dut.wr_sch_valid_o.value)
        return self._pick_oldest(int(self.dut.wr_sch_valid_o.value),
                                 int(self.dut.wr_sch_older_o.value), n)

    def _rd_oldest_slot(self):
        n = len(self.dut.rd_sch_valid_o.value)
        return self._pick_oldest(int(self.dut.rd_sch_valid_o.value),
                                 int(self.dut.rd_sch_older_o.value), n)

    async def commit_wr(self):
        """Commit the oldest write; return the cm_rd burst."""
        slot = None
        for _ in range(200):
            slot = self._wr_oldest_slot()
            if slot is not None:
                break
            await RisingEdge(self.dut.aclk)
        await self.wr_commit_bfm.send(
            self.wr_commit_bfm.create_packet(slot=slot))
        for _ in range(200):
            if self.cm_out:
                return self.cm_out.popleft()
            await RisingEdge(self.dut.aclk)
        return None

    async def service_rd(self, data, resp=0):
        """Issue the oldest pending read, then drive its DFI return data."""
        slot = None
        for _ in range(200):
            slot = self._rd_oldest_slot()
            if slot is not None:
                break
            await RisingEdge(self.dut.aclk)
        await self.rd_issue_bfm.send(
            self.rd_issue_bfm.create_packet(slot=slot))
        # DFI return stream -- one packet per beat; the BFM sets valid and
        # every field and honours rd_dfi_ret_ready_o.
        n = len(data)
        for i, d in enumerate(data):
            await self.dfi_ret_bfm.send(self.dfi_ret_bfm.create_packet(
                data=d, resp=resp, last=1 if i == n - 1 else 0))

    async def wait_r(self, timeout=400):
        for _ in range(timeout):
            if self.r_out:
                return self.r_out.popleft()
            await RisingEdge(self.dut.aclk)
        return None
