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

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
from tbclasses.pumice_fub_bfm import fub_consumer      # noqa: E402

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
        self._build_bfms()
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
        self.dut.t_rfc_i.value = 8       # mission-mode REF recovery (arbiter)
        self.dut.refresh_burst_i.value = 1
        self.dut.t_init_wait_i.value = 0
        self.dut.t_dll_wait_i.value = 0
        self.dut.t_mrd_wait_i.value = 0
        self.dut.t_rp_wait_i.value = 0
        self.dut.t_rfc_wait_i.value = 0
        self.dut.dfi_init_complete_i.value = 0
        # CAM per-entry vector inputs (driven by _cam_model)
        for pfx in ('wr', 'rd'):
            getattr(self.dut, f'{pfx}_sch_valid_i').value = 0
            getattr(self.dut, f'{pfx}_sch_bank_i').value = 0
            getattr(self.dut, f'{pfx}_sch_row_i').value = 0
            getattr(self.dut, f'{pfx}_sch_col_i').value = 0
            getattr(self.dut, f'{pfx}_sch_older_i').value = 0
        # cmd / wr_commit / rd_issue readys come from GAXI slave BFMs, not
        # a hardwired 1. `backtoback` is ready_delay 0, i.e. continuously
        # asserted -- identical stimulus, but now protocol-driven.

    def _build_bfms(self, profile="backtoback"):
        """GAXI slaves on the scheduler's three output handshakes."""
        self.cmd_bfm = fub_consumer(
            self.dut, "cmd", self.dut.aclk, profile=profile, log=self.log,
            valid="cmd_valid_o", ready="cmd_ready_i",
            fields={'op':   ("cmd_op_o",   max(1, len(self.dut.cmd_op_o))),
                    'rank': ("cmd_rank_o", max(1, len(self.dut.cmd_rank_o))),
                    'bank': ("cmd_bank_o", max(1, len(self.dut.cmd_bank_o))),
                    'row':  ("cmd_row_o",  max(1, len(self.dut.cmd_row_o))),
                    'col':  ("cmd_col_o",  max(1, len(self.dut.cmd_col_o))),
                    'ap':   ("cmd_ap_o",   1)})
        self.wr_commit_bfm = fub_consumer(
            self.dut, "wr_commit", self.dut.aclk, profile=profile, log=self.log,
            valid="wr_commit_valid_o", ready="wr_commit_ready_i",
            fields={'slot': ("wr_commit_slot_o", max(1, len(self.dut.wr_commit_slot_o)))})
        self.rd_issue_bfm = fub_consumer(
            self.dut, "rd_issue", self.dut.aclk, profile=profile, log=self.log,
            valid="rd_issue_valid_o", ready="rd_issue_ready_i",
            fields={'slot': ("rd_issue_slot_o", max(1, len(self.dut.rd_issue_slot_o)))})

    # ---- mock CAMs: expose wr_entry/rd_entry as per-entry vectors -----------
    # Model the real CAMs' scheduled/issued exclusion: the moment the arbiter
    # commits/issues a slot, that entry drops out of the schedulable set (real
    # wr r_sched / rd r_issued). So an entry whose commit/issue is firing this
    # cycle is suppressed here, preventing re-issue with no throttle. The arbiter
    # now does the {bank,row} match itself, so the mock just places the entry's
    # registered fields at its slot index in the sch_* vectors.
    def _apply_cam(self):
        wr_fire = int(self.dut.wr_commit_valid_o.value)
        wr_fslot = int(self.dut.wr_commit_slot_o.value)
        rd_fire = int(self.dut.rd_issue_valid_o.value)
        rd_fslot = int(self.dut.rd_issue_slot_o.value)
        for pfx, ent, fire, fslot in (('wr', self.wr_entry, wr_fire, wr_fslot),
                                      ('rd', self.rd_entry, rd_fire, rd_fslot)):
            valid = bank = row = col = 0
            fired = (ent is not None and fire and ent['slot'] == fslot)
            if ent is not None and not fired:
                e = ent['slot']
                valid |= (1 << e)
                bank |= (ent['bank'] & ((1 << self.BKW) - 1)) << (e * self.BKW)
                row  |= (ent['row']  & ((1 << self.ROW_WIDTH) - 1)) << (e * self.ROW_WIDTH)
                col  |= (ent['col']  & ((1 << self.COL_WIDTH) - 1)) << (e * self.COL_WIDTH)
            getattr(self.dut, f'{pfx}_sch_valid_i').value = valid
            getattr(self.dut, f'{pfx}_sch_bank_i').value = bank
            getattr(self.dut, f'{pfx}_sch_row_i').value = row
            getattr(self.dut, f'{pfx}_sch_col_i').value = col
            # single pending entry per side -> it is trivially the oldest, so the
            # order matrix is don't-care (arg_oldest needs no OTHER masked entry).
            getattr(self.dut, f'{pfx}_sch_older_i').value = 0

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
