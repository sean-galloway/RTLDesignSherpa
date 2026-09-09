# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_rd_cmd_cam` -- the read SCHEDULING window.

Since 2026-09-08 the CAM no longer buffers read data: an entry lives from
insert to ISSUE, carrying the return ring's ticket. Key checks: inserts in AR
order carry their tickets; the scheduling vectors / oldest / lookups see the
valid entries; an issue frees the entry (sch_valid drops, the slot is reusable)
and forwards the entry's ticket on iss_*; a full window backpressures insert.
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
from tbclasses.pumice_fub_bfm import fub_consumer, fub_producer   # noqa: E402


class PumiceRdCmdCamTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_ENTRIES = self.convert_to_int(os.environ.get('NUM_ENTRIES', '8'))
        self.N_SCHED_LU  = self.convert_to_int(os.environ.get('N_SCHED_LU', '4'))
        self.NUM_BANKS   = self.convert_to_int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH   = self.convert_to_int(os.environ.get('ROW_WIDTH', '14'))
        self.COL_WIDTH   = self.convert_to_int(os.environ.get('COL_WIDTH', '10'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))
        self.RD_RET_DEPTH = self.convert_to_int(os.environ.get('RD_RET_DEPTH', '32'))
        self.BKW  = max(1, (self.NUM_BANKS - 1).bit_length())
        self.PTRW = max(1, (self.NUM_ENTRIES - 1).bit_length())
        self.TW   = max(1, (self.RD_RET_DEPTH - 1).bit_length())
        self.iss_out = deque()     # tickets forwarded on iss_*, in issue order

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self._build_bfms()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._mon_iss())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        # sched_lu_* is a combinational lookup request (no ready) -- not a
        # handshake, so it stays TB-driven. age_thresh is a config level.
        self.dut.sched_lu_valid_i.value = 0
        self.dut.sched_lu_bank_i.value = 0
        self.dut.sched_lu_row_i.value = 0
        self.dut.age_thresh_i.value = 0

    def _build_bfms(self, profile="backtoback"):
        self.ins_bfm = fub_producer(
            self.dut, "ins", self.dut.aclk, profile=profile, log=self.log,
            valid="ins_valid_i", ready="ins_ready_o",
            fields={'bank':   ("ins_bank_i",   max(1, len(self.dut.ins_bank_i))),
                    'row':    ("ins_row_i",    max(1, len(self.dut.ins_row_i))),
                    'col':    ("ins_col_i",    max(1, len(self.dut.ins_col_i))),
                    'id':     ("ins_id_i",     max(1, len(self.dut.ins_id_i))),
                    'qos':    ("ins_qos_i",    4),
                    'ticket': ("ins_ticket_i", max(1, len(self.dut.ins_ticket_i)))})
        self.issue_bfm = fub_producer(
            self.dut, "issue", self.dut.aclk, profile=profile, log=self.log,
            valid="issue_valid_i", ready="issue_ready_o",
            fields={'slot': ("issue_slot_i", max(1, len(self.dut.issue_slot_i)))})
        self.iss_bfm = fub_consumer(
            self.dut, "iss", self.dut.aclk, profile=profile, log=self.log,
            valid="iss_valid_o", ready="iss_ready_i",
            fields={'ticket': ("iss_ticket_o", max(1, len(self.dut.iss_ticket_o)))})

    def set_iss_ready(self, accepting: bool):
        """Downstream (ring issue_q) backpressure, through the BFM."""
        self.iss_bfm.set_ready_policy('always' if accepting else 'stall')

    async def _mon_iss(self):
        while True:
            await RisingEdge(self.dut.aclk)
            while self.iss_bfm._recvQ:
                p = self.iss_bfm._recvQ.popleft()
                self.iss_out.append(p.ticket)

    async def insert(self, bank, row, col, rid, ticket=0, qos=0):
        await self.ins_bfm.send(self.ins_bfm.create_packet(
            bank=bank, row=row, col=col, id=rid, qos=qos, ticket=ticket))

    async def issue(self, slot):
        await self.issue_bfm.send(self.issue_bfm.create_packet(slot=slot))

    def sch_valid(self):
        return int(self.dut.sch_valid_o.value)

    def ins_ready(self):
        return int(self.dut.ins_ready_o.value)

    def oldest(self):
        return (int(self.dut.oldest_valid_o.value),
                int(self.dut.oldest_bank_o.value),
                int(self.dut.oldest_row_o.value),
                int(self.dut.oldest_col_o.value),
                int(self.dut.oldest_id_o.value),
                int(self.dut.oldest_slot_o.value))

    def head_rel(self):
        """Relative age of the OLDEST SCHEDULABLE (valid) entry, 0 when none."""
        return int(self.dut.sch_head_rel_o.value)

    async def sched_query(self, queries):
        vbits = bank_pack = row_pack = 0
        for j, (v, b, r) in enumerate(queries):
            if v:
                vbits |= (1 << j)
            bank_pack |= (b & ((1 << self.BKW) - 1)) << (j * self.BKW)
            row_pack  |= (r & ((1 << self.ROW_WIDTH) - 1)) << (j * self.ROW_WIDTH)
        self.dut.sched_lu_valid_i.value = vbits
        self.dut.sched_lu_bank_i.value = bank_pack
        self.dut.sched_lu_row_i.value = row_pack
        await RisingEdge(self.dut.aclk)
        hit = int(self.dut.sched_lu_hit_o.value)
        slot_all = int(self.dut.sched_lu_slot_o.value)
        col_all  = int(self.dut.sched_lu_col_o.value)
        id_all   = int(self.dut.sched_lu_id_o.value)
        out = []
        for j in range(len(queries)):
            out.append(((hit >> j) & 1,
                        (slot_all >> (j * self.PTRW)) & ((1 << self.PTRW) - 1),
                        (col_all >> (j * self.COL_WIDTH)) & ((1 << self.COL_WIDTH) - 1),
                        (id_all >> (j * self.AXI_ID_WIDTH)) & ((1 << self.AXI_ID_WIDTH) - 1)))
        self.dut.sched_lu_valid_i.value = 0
        return out

    async def wait_iss(self, n, limit=200):
        for _ in range(limit):
            if len(self.iss_out) >= n:
                return
            await RisingEdge(self.dut.aclk)
        raise AssertionError(f"only {len(self.iss_out)}/{n} tickets forwarded on iss_*")
