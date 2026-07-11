# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_wr_data_cam`.

Exercises all ports:
  * insert + fill -> a pending write in an SRAM slot
  * oldest port   -> always the min-age valid entry (scheduler fallback)
  * snarf lookup  -> youngest match (WAW returns newest data), streamed out
  * sched lookup  -> oldest match on {bank,row} across N generic ports
  * commit        -> stream SRAM[slot] then evict (slot frees, oldest advances)
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


class PumiceWrDataCamTB(TBBase):
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

        self.snarf_out = deque()   # completed snarf bursts (list of beats)
        self.cm_out    = deque()   # completed commit bursts

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)
        cocotb.start_soon(self._mon_stream(self.dut.snarf_rd_valid_o, self.dut.snarf_rd_ready_i,
                                           self.dut.snarf_rd_data_o, self.dut.snarf_rd_last_o,
                                           self.snarf_out))
        cocotb.start_soon(self._mon_stream(self.dut.cm_rd_valid_o, self.dut.cm_rd_ready_i,
                                           self.dut.cm_rd_data_o, self.dut.cm_rd_last_o,
                                           self.cm_out))

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.ins_valid_i.value = 0
        self.dut.ins_bank_i.value = 0
        self.dut.ins_row_i.value = 0
        self.dut.ins_col_i.value = 0
        self.dut.ins_id_i.value = 0
        self.dut.wd_valid_i.value = 0
        self.dut.wd_data_i.value = 0
        self.dut.wd_strb_i.value = (1 << (self.AXI_DATA_WIDTH // 8)) - 1
        self.dut.wd_last_i.value = 0
        self.dut.snarf_probe_valid_i.value = 0
        self.dut.snarf_probe_bank_i.value = 0
        self.dut.snarf_probe_row_i.value = 0
        self.dut.snarf_probe_col_i.value = 0
        self.dut.snarf_probe_id_i.value = 0
        self.dut.snarf_probe_len_i.value = self.BL - 1   # matching burst length
        self.dut.snarf_accept_i.value = 0
        self.dut.snarf_rd_ready_i.value = 1
        self.dut.sched_lu_valid_i.value = 0
        self.dut.sched_lu_bank_i.value = 0
        self.dut.sched_lu_row_i.value = 0
        self.dut.commit_valid_i.value = 0
        self.dut.commit_slot_i.value = 0
        self.dut.cm_rd_ready_i.value = 1

    async def _mon_stream(self, val, rdy, data, last, out):
        cur = []
        while True:
            await RisingEdge(self.dut.aclk)
            if int(val.value) and int(rdy.value):
                cur.append(int(data.value))
                if int(last.value):
                    out.append(cur)
                    cur = []

    # ---- insert + fill ------------------------------------------------------
    async def write_entry(self, bank, row, col, wid, data):
        # insert command
        self.dut.ins_bank_i.value = bank
        self.dut.ins_row_i.value = row
        self.dut.ins_col_i.value = col
        self.dut.ins_id_i.value = wid
        self.dut.ins_valid_i.value = 1
        await RisingEdge(self.dut.aclk)
        while int(self.dut.ins_ready_o.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.ins_valid_i.value = 0
        # fill data beats
        n = len(data)
        for i, d in enumerate(data):
            self.dut.wd_data_i.value = d
            self.dut.wd_last_i.value = 1 if i == n - 1 else 0
            self.dut.wd_valid_i.value = 1
            await RisingEdge(self.dut.aclk)
            while int(self.dut.wd_ready_o.value) == 0:
                await RisingEdge(self.dut.aclk)
        self.dut.wd_valid_i.value = 0
        self.dut.wd_last_i.value = 0

    # ---- oldest port --------------------------------------------------------
    def oldest(self):
        return (int(self.dut.oldest_valid_o.value),
                int(self.dut.oldest_bank_o.value),
                int(self.dut.oldest_row_o.value),
                int(self.dut.oldest_col_o.value),
                int(self.dut.oldest_id_o.value),
                int(self.dut.oldest_slot_o.value))

    # ---- snarf --------------------------------------------------------------
    async def snarf(self, bank, row, col, rid=0, arlen=None):
        """Probe; if hit, accept (latch youngest slot) and return the streamed
        burst. A hit now also requires matching AXI id and burst length (arlen
        defaults to BL-1, the only admitted write length). Returns
        (hit, burst_or_None)."""
        self.dut.snarf_probe_bank_i.value = bank
        self.dut.snarf_probe_row_i.value = row
        self.dut.snarf_probe_col_i.value = col
        self.dut.snarf_probe_id_i.value = rid
        self.dut.snarf_probe_len_i.value = (self.BL - 1) if arlen is None else arlen
        self.dut.snarf_probe_valid_i.value = 1
        await RisingEdge(self.dut.aclk)
        hit = int(self.dut.snarf_hit_o.value)
        if hit:
            self.dut.snarf_accept_i.value = 1
            await RisingEdge(self.dut.aclk)
            self.dut.snarf_accept_i.value = 0
        self.dut.snarf_probe_valid_i.value = 0
        if not hit:
            return (0, None)
        for _ in range(200):
            if self.snarf_out:
                return (1, self.snarf_out.popleft())
            await RisingEdge(self.dut.aclk)
        return (1, None)

    # ---- scheduler lookups --------------------------------------------------
    async def sched_query(self, queries):
        """queries: list of (valid, bank, row) length <= N_SCHED_LU.
        Returns list of (hit, slot, col, id, age)."""
        vbits = 0
        bank_pack = 0
        row_pack = 0
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
        age_all  = int(self.dut.sched_lu_age_o.value)
        out = []
        for j in range(len(queries)):
            out.append((
                (hit >> j) & 1,
                (slot_all >> (j * self.PTRW)) & ((1 << self.PTRW) - 1),
                (col_all >> (j * self.COL_WIDTH)) & ((1 << self.COL_WIDTH) - 1),
                (id_all >> (j * self.AXI_ID_WIDTH)) & ((1 << self.AXI_ID_WIDTH) - 1),
                (age_all >> (j * 16)) & 0xFFFF,
            ))
        self.dut.sched_lu_valid_i.value = 0
        return out

    # ---- commit -------------------------------------------------------------
    async def commit(self, slot):
        while int(self.dut.commit_ready_o.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.commit_slot_i.value = slot
        self.dut.commit_valid_i.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.commit_valid_i.value = 0
        for _ in range(200):
            if self.cm_out:
                return self.cm_out.popleft()
            await RisingEdge(self.dut.aclk)
        return None
