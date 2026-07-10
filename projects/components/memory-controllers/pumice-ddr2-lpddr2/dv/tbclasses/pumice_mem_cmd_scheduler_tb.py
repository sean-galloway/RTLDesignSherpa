# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Macro testbench for `pumice_mem_cmd_scheduler`.

Exercises the REAL wiring of arbiter + pumice_bank_timers + global_timers +
refresh_ctrl + init_sequencer + cmd FIFO. The TB plays:
  * DFI init handshake  (drive dfi_init_complete, watch init_done)
  * mock wr/rd CAMs     (answer sched lookups by {bank,open_row}; oldest ports;
                         observe commit/issue)
  * DFI command sink    (drain the cmd FIFO, capture the command stream)

Checks: init MRS stream forwarded; after init, a pending read gets ACT->RD with
real per-bank timer gating (tRCD spacing); refresh emerges as PRE(active)->REF.
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

OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA, OP_PRE, OP_PREA, OP_REF, OP_REFPB, OP_MRS = range(11)
PAGE_OPEN, PAGE_CLOSE = 0, 1
MEMTYPE_DDR2 = 0


class PumiceMemCmdSchedulerTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_BANKS = self.convert_to_int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH = self.convert_to_int(os.environ.get('ROW_WIDTH', '14'))
        self.COL_WIDTH = self.convert_to_int(os.environ.get('COL_WIDTH', '10'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))
        self.NUM_ENTRIES = self.convert_to_int(os.environ.get('NUM_ENTRIES', '8'))
        self.AGE_WIDTH = 16
        self.BKW = max(1, (self.NUM_BANKS - 1).bit_length())
        self.PTRW = max(1, (self.NUM_ENTRIES - 1).bit_length())
        self.N_LU = self.NUM_BANKS
        self.cmds = deque()          # captured command stream (dicts)
        # mock CAM model: single pending entry per side {bank,row,col,id,age,slot}
        self.wr_entry = None
        self.rd_entry = None
        self.wr_committed = []
        self.rd_issued = []

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 6)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 3)
        cocotb.start_soon(self._cam_model())
        cocotb.start_soon(self._cmd_sink())
        cocotb.start_soon(self._track_commit_issue())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.page_policy_i.value = PAGE_OPEN
        self.dut.memtype_i.value = MEMTYPE_DDR2
        # timing (small, legal-ish)
        self.dut.t_rcd_i.value = 3
        self.dut.t_rp_i.value = 3
        self.dut.t_ras_i.value = 5
        self.dut.t_rc_i.value = 8
        self.dut.t_wr_i.value = 4
        self.dut.t_rtp_i.value = 2
        self.dut.t_faw_i.value = 6
        self.dut.t_rrd_i.value = 2
        self.dut.t_wtr_i.value = 2
        self.dut.t_rtw_i.value = 2
        self.dut.t_ccd_i.value = 2
        self.dut.t_refi_i.value = 0x0800
        self.dut.refresh_burst_i.value = 1
        self.dut.t_init_wait_i.value = 0
        self.dut.t_dll_wait_i.value = 0
        self.dut.t_mrd_wait_i.value = 0
        self.dut.t_rp_wait_i.value = 0
        self.dut.t_rfc_wait_i.value = 0
        self.dut.dfi_init_complete_i.value = 0
        # CAM lookup / oldest inputs (driven by _cam_model)
        for pfx in ('wr', 'rd'):
            getattr(self.dut, f'{pfx}_lu_hit_i').value = 0
            getattr(self.dut, f'{pfx}_lu_slot_i').value = 0
            getattr(self.dut, f'{pfx}_lu_col_i').value = 0
            getattr(self.dut, f'{pfx}_lu_id_i').value = 0
            getattr(self.dut, f'{pfx}_lu_age_i').value = 0
            getattr(self.dut, f'{pfx}_oldest_valid_i').value = 0
            getattr(self.dut, f'{pfx}_oldest_bank_i').value = 0
            getattr(self.dut, f'{pfx}_oldest_row_i').value = 0
            getattr(self.dut, f'{pfx}_oldest_slot_i').value = 0
        self.dut.cmd_ready_i.value = 1

    # ---- mock CAMs: answer lookups from wr_entry/rd_entry ------------------
    # Model the real CAMs' scheduled/issued exclusion: the moment the arbiter
    # commits/issues a slot, that entry is removed from sched_lu/oldest (real
    # wr r_sched / rd r_issued). So an entry whose commit/issue is firing this
    # cycle is suppressed here, preventing re-issue with no throttle.
    def _apply_cam(self):
        wr_fire = int(self.dut.wr_commit_valid_o.value)
        wr_fslot = int(self.dut.wr_commit_slot_o.value)
        rd_fire = int(self.dut.rd_issue_valid_o.value)
        rd_fslot = int(self.dut.rd_issue_slot_o.value)
        for pfx, ent in (('wr', self.wr_entry), ('rd', self.rd_entry)):
            hit = slot = col = idv = age = 0
            ov = ob = orow = oslot = 0
            fired = ((pfx == 'wr' and wr_fire and ent is not None and ent['slot'] == wr_fslot)
                     or (pfx == 'rd' and rd_fire and ent is not None and ent['slot'] == rd_fslot))
            if ent is not None and not fired:
                b = ent['bank']
                # lookup port b responds to {bank b, its open row}: the arbiter
                # queries with bank_open_row; the mock hits when the query row
                # equals the entry's row. Query row = arbiter's lu_row_o[b].
                qrow = (int(getattr(self.dut, f'{pfx}_lu_row_o').value)
                        >> (b * self.ROW_WIDTH)) & ((1 << self.ROW_WIDTH) - 1)
                if qrow == ent['row']:
                    hit |= (1 << b)
                    slot |= (ent['slot'] & ((1 << self.PTRW) - 1)) << (b * self.PTRW)
                    col  |= (ent['col'] & ((1 << self.COL_WIDTH) - 1)) << (b * self.COL_WIDTH)
                    idv  |= (ent['id'] & ((1 << self.AXI_ID_WIDTH) - 1)) << (b * self.AXI_ID_WIDTH)
                    age  |= (ent['age'] & 0xFFFF) << (b * self.AGE_WIDTH)
                ov, ob, orow, oslot = 1, ent['bank'], ent['row'], ent['slot']
            getattr(self.dut, f'{pfx}_lu_hit_i').value = hit
            getattr(self.dut, f'{pfx}_lu_slot_i').value = slot
            getattr(self.dut, f'{pfx}_lu_col_i').value = col
            getattr(self.dut, f'{pfx}_lu_id_i').value = idv
            getattr(self.dut, f'{pfx}_lu_age_i').value = age
            getattr(self.dut, f'{pfx}_oldest_valid_i').value = ov
            getattr(self.dut, f'{pfx}_oldest_bank_i').value = ob
            getattr(self.dut, f'{pfx}_oldest_row_i').value = orow
            getattr(self.dut, f'{pfx}_oldest_slot_i').value = oslot

    async def _cam_model(self):
        while True:
            self._apply_cam()
            await RisingEdge(self.dut.aclk)

    async def _track_commit_issue(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.wr_commit_valid_o.value):
                self.wr_committed.append(int(self.dut.wr_commit_slot_o.value))
                self.wr_entry = None       # retire
            if int(self.dut.rd_issue_valid_o.value):
                self.rd_issued.append(int(self.dut.rd_issue_slot_o.value))
                self.rd_entry = None       # retire

    async def _cmd_sink(self):
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.cmd_valid_o.value) and int(self.dut.cmd_ready_i.value):
                self.cmds.append({
                    'op':   int(self.dut.cmd_op_o.value),
                    'bank': int(self.dut.cmd_bank_o.value),
                    'row':  int(self.dut.cmd_row_o.value),
                    'col':  int(self.dut.cmd_col_o.value),
                    'ap':   int(self.dut.cmd_ap_o.value),
                })

    # ---- helpers ------------------------------------------------------------
    async def complete_init(self, max_cycles=200):
        self.dut.dfi_init_complete_i.value = 1
        for _ in range(max_cycles):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.init_done_o.value):
                return True
        return False

    def ops_of(self, op):
        return [c for c in self.cmds if c['op'] == op]
