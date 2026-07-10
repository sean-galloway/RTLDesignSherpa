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
        self.dut.ins_valid_i.value = 0
        self.dut.ins_bank_i.value = 0
        self.dut.ins_row_i.value = 0
        self.dut.ins_col_i.value = 0
        self.dut.ins_id_i.value = 0
        self.dut.sched_lu_valid_i.value = 0
        self.dut.sched_lu_bank_i.value = 0
        self.dut.sched_lu_row_i.value = 0
        self.dut.issue_valid_i.value = 0
        self.dut.issue_slot_i.value = 0
        self.dut.dfi_ret_valid_i.value = 0
        self.dut.dfi_ret_data_i.value = 0
        self.dut.dfi_ret_resp_i.value = 0
        self.dut.dfi_ret_last_i.value = 0
        self.dut.drain_ready_i.value = 1

    async def _mon_drain(self):
        cur = []
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.drain_valid_o.value) and int(self.dut.drain_ready_i.value):
                cur.append((int(self.dut.drain_id_o.value),
                            int(self.dut.drain_data_o.value),
                            int(self.dut.drain_resp_o.value)))
                if int(self.dut.drain_last_o.value):
                    self.drain_out.append(cur)
                    cur = []

    async def insert(self, bank, row, col, rid):
        self.dut.ins_bank_i.value = bank
        self.dut.ins_row_i.value = row
        self.dut.ins_col_i.value = col
        self.dut.ins_id_i.value = rid
        self.dut.ins_valid_i.value = 1
        await RisingEdge(self.dut.aclk)
        while int(self.dut.ins_ready_o.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.ins_valid_i.value = 0

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
        while int(self.dut.issue_ready_o.value) == 0:
            await RisingEdge(self.dut.aclk)
        self.dut.issue_slot_i.value = slot
        self.dut.issue_valid_i.value = 1
        await RisingEdge(self.dut.aclk)
        self.dut.issue_valid_i.value = 0

    async def dfi_return(self, data, resp=0):
        n = len(data)
        for i, d in enumerate(data):
            self.dut.dfi_ret_data_i.value = d
            self.dut.dfi_ret_resp_i.value = resp
            self.dut.dfi_ret_last_i.value = 1 if i == n - 1 else 0
            self.dut.dfi_ret_valid_i.value = 1
            await RisingEdge(self.dut.aclk)
            while int(self.dut.dfi_ret_ready_o.value) == 0:
                await RisingEdge(self.dut.aclk)
        self.dut.dfi_ret_valid_i.value = 0
        self.dut.dfi_ret_last_i.value = 0
