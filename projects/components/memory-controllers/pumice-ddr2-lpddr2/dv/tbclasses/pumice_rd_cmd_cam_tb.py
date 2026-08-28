# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_rd_cmd_cam` — outstanding-read reorder buffer.

Key check: inserts in AR order, ISSUE in a different order (row-hit reorder),
DFI returns in ISSUE order, and drain releases in AR order (the reorder).
Also: oldest not-issued port + scheduler oldest-match lookups.
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
        self.AXI_DATA_WIDTH = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '64'))
        self.BL = self.convert_to_int(os.environ.get('BL', '4'))
        self.BKW = max(1, (self.NUM_BANKS - 1).bit_length())
        self.PTRW = max(1, (self.NUM_ENTRIES - 1).bit_length())
        self.drain_out = deque()   # completed drain bursts: list of (id,data,resp)

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self._build_bfms()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._mon_drain())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        # ins / issue / dfi_ret / drain are BFM-owned (see _build_bfms).
        # sched_lu_* is NOT a handshake -- sched_lu_valid_i has no matching
        # ready, it is a combinational lookup request -- so it stays here.
        self.dut.sched_lu_valid_i.value = 0
        self.dut.sched_lu_bank_i.value = 0
        self.dut.sched_lu_row_i.value = 0

    def _build_bfms(self, profile="backtoback"):
        self.ins_bfm = fub_producer(
            self.dut, "ins", self.dut.aclk, profile=profile, log=self.log,
            valid="ins_valid_i", ready="ins_ready_o",
            fields={'bank': ("ins_bank_i", max(1, len(self.dut.ins_bank_i))),
                    'row':  ("ins_row_i",  max(1, len(self.dut.ins_row_i))),
                    'col':  ("ins_col_i",  max(1, len(self.dut.ins_col_i))),
                    'id':   ("ins_id_i",   max(1, len(self.dut.ins_id_i)))})
        self.issue_bfm = fub_producer(
            self.dut, "issue", self.dut.aclk, profile=profile, log=self.log,
            valid="issue_valid_i", ready="issue_ready_o",
            fields={'slot': ("issue_slot_i", max(1, len(self.dut.issue_slot_i)))})
        self.dfi_ret_bfm = fub_producer(
            self.dut, "dfi_ret", self.dut.aclk, profile=profile, log=self.log,
            valid="dfi_ret_valid_i", ready="dfi_ret_ready_o",
            fields={'data': ("dfi_ret_data_i", max(1, len(self.dut.dfi_ret_data_i))),
                    'resp': ("dfi_ret_resp_i", 2),
                    'last': ("dfi_ret_last_i", 1)})
        self.drain_bfm = fub_consumer(
            self.dut, "drain", self.dut.aclk, profile=profile, log=self.log,
            valid="drain_valid_o", ready="drain_ready_i",
            fields={'id':   ("drain_id_o",   max(1, len(self.dut.drain_id_o))),
                    'data': ("drain_data_o", max(1, len(self.dut.drain_data_o))),
                    'resp': ("drain_resp_o", 2),
                    'last': ("drain_last_o", 1)})

    def set_drain_ready(self, accepting: bool):
        """Consumer-side backpressure on drain, through the BFM."""
        self.drain_bfm.set_ready_policy('always' if accepting else 'stall')

    async def _mon_drain(self):
        """Reshape the drain BFM's captures into per-burst lists."""
        cur = []
        while True:
            await RisingEdge(self.dut.aclk)
            while self.drain_bfm._recvQ:
                p = self.drain_bfm._recvQ.popleft()
                cur.append((p.id, p.data, p.resp))
                if p.last:
                    self.drain_out.append(cur)
                    cur = []

    async def insert(self, bank, row, col, rid):
        """Insert via the BFM, which holds valid until ins_ready_o -- what
        the protocol requires of a producer."""
        await self.ins_bfm.send(self.ins_bfm.create_packet(
            bank=bank, row=row, col=col, id=rid))

    def oldest(self):
        return (int(self.dut.oldest_valid_o.value),
                int(self.dut.oldest_bank_o.value),
                int(self.dut.oldest_row_o.value),
                int(self.dut.oldest_col_o.value),
                int(self.dut.oldest_id_o.value),
                int(self.dut.oldest_slot_o.value))

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

    async def issue(self, slot):
        await self.issue_bfm.send(self.issue_bfm.create_packet(slot=slot))

    async def dfi_return(self, data, resp=0):
        n = len(data)
        for i, d in enumerate(data):
            await self.dfi_ret_bfm.send(self.dfi_ret_bfm.create_packet(
                data=d, resp=resp, last=1 if i == n - 1 else 0))
