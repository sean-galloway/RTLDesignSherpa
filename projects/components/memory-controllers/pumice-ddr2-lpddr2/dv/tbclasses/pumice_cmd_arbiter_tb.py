# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_cmd_arbiter`.

The arbiter is combinational-pick + accepted-issue side effects. The TB mocks
its neighbors: per-bank/global timer readiness, both CAMs' sched-lookup + oldest
ports, init passthrough, refresh req, and the command sink (cmd_ready). It reads
back the picked command + the evt/commit/issue/grant strobes.

Scenarios: init passthrough; refresh (PRE active bank then REF+grant); read-
priority row-hit; oldest tie-break among RD candidates; write pick when no RD;
ACT fallback toward the oldest pending op; cmd_ready backpressure (no strobes
until accepted).
"""

import os
import sys
import subprocess

import cocotb
from cocotb.triggers import RisingEdge, Timer

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402

# dram_op_e
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA, OP_PRE, OP_PREA, OP_REF = \
    0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8
# page_policy_e
PAGE_OPEN, PAGE_CLOSE, PAGE_HYBRID = 0, 1, 2


class PumiceCmdArbiterTB(TBBase):
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

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 4)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.page_policy_i.value = PAGE_OPEN
        self.dut.init_done_i.value = 1
        self.dut.init_cmd_valid_i.value = 0
        self.dut.init_cmd_op_i.value = OP_NOP
        self.dut.init_cmd_bank_i.value = 0
        self.dut.init_cmd_row_i.value = 0
        self.dut.refresh_req_i.value = 0
        self.dut.refresh_drain_i.value = 0
        self.dut.refresh_kind_i.value = 0
        self.dut.refresh_bank_i.value = 0
        self.dut.t_rfc_i.value = 8       # REF recovery (mission-mode tRFC)
        self.dut.t_rfc_pb_i.value = 0
        self.dut.sched_order_mode_i.value = 0   # FR-FCFS build default
        self.dut.sched_row_sel_i.value = 0      # oldest
        self.dut.sched_col_sel_i.value = 0      # oldest
        self.dut.sched_access_pref_i.value = 0  # column_first
        self.dut.sched_wr_high_wm_i.value = 0   # write batching off
        self.dut.sched_wr_low_wm_i.value = 0
        self.dut.rd_sch_age_exceed_i.value = 0
        self.dut.wr_sch_age_exceed_i.value = 0
        self.dut.rd_sch_head_rel_i.value = 0
        self.dut.wr_sch_head_rel_i.value = 0
        self.dut.bank_act_ready_i.value = 0
        self.dut.bank_rdwr_ready_i.value = 0
        self.dut.bank_pre_ready_i.value = 0
        self.dut.bank_row_active_i.value = 0
        self.dut.bank_open_row_i.value = 0
        self.dut.tfaw_ok_i.value = 1
        self.dut.trrd_ok_i.value = 1
        self.dut.twtr_ok_i.value = 1
        self.dut.trtw_ok_i.value = 1
        self.dut.tccd_ok_i.value = 1
        for pfx in ('wr', 'rd'):
            getattr(self.dut, f'{pfx}_sch_valid_i').value = 0
            getattr(self.dut, f'{pfx}_sch_bank_i').value = 0
            getattr(self.dut, f'{pfx}_sch_row_i').value = 0
            getattr(self.dut, f'{pfx}_sch_col_i').value = 0
            getattr(self.dut, f'{pfx}_sch_older_i').value = 0
        self.dut.cmd_ready_i.value = 1
        self.dut.wr_commit_ready_i.value = 1   # CAM drain FIFO has room
        self.dut.rd_issue_ready_i.value = 1    # CAM issue FIFO has room

    # ---- helpers: pack per-bank vectors -------------------------------------
    def set_bank_bits(self, sig, bank_to_val):
        v = 0
        for b, on in bank_to_val.items():
            if on:
                v |= (1 << b)
        sig.value = v

    def set_open_rows(self, rows):
        """rows: {bank: row}. Packs bank_open_row_i (row_active banks)."""
        v = 0
        for b, r in rows.items():
            v |= (r & ((1 << self.ROW_WIDTH) - 1)) << (b * self.ROW_WIDTH)
        self.dut.bank_open_row_i.value = v

    def set_entries(self, pfx, entries):
        """entries: {slot: (bank, row, col, age)} (col optional). Listed slots
        are schedulable (sch_valid=1); the arbiter picks the OLDEST via the
        age-order matrix, which we synthesize here from the given ages:
        older[i][j] = age[i] > age[j] (higher age == older, matching the old key)."""
        N = self.NUM_ENTRIES
        valid = bank = row = col = older = 0
        ages = {}
        for e, vals in entries.items():
            if len(vals) == 4:
                b, r, c, a = vals
            else:
                b, r, a = vals
                c = 0
            ages[e] = a
            valid |= (1 << e)
            bank |= (b & ((1 << self.BKW) - 1)) << (e * self.BKW)
            row  |= (r & ((1 << self.ROW_WIDTH) - 1)) << (e * self.ROW_WIDTH)
            col  |= (c & ((1 << self.COL_WIDTH) - 1)) << (e * self.COL_WIDTH)
        for i, ai in ages.items():
            for j, aj in ages.items():
                if i != j and ai > aj:
                    older |= (1 << (i * N + j))
        getattr(self.dut, f'{pfx}_sch_valid_i').value = valid
        getattr(self.dut, f'{pfx}_sch_bank_i').value = bank
        getattr(self.dut, f'{pfx}_sch_row_i').value = row
        getattr(self.dut, f'{pfx}_sch_col_i').value = col
        getattr(self.dut, f'{pfx}_sch_older_i').value = older

    async def settle(self):
        # The arbiter is a 2-stage pipeline: it registers the per-bank timer
        # fan-in at its INPUT (1 cycle), then registers the DECISION at its
        # OUTPUT (1 cycle). So a pick reflecting freshly-set bank state / CAM
        # entries appears 2 edges later. Advance both, then settle combinational.
        await RisingEdge(self.dut.aclk)
        await RisingEdge(self.dut.aclk)
        await Timer(1, units='ns')

    # ---- readback -----------------------------------------------------------
    def picked(self):
        return {
            'valid': int(self.dut.cmd_valid_o.value),
            'op':    int(self.dut.cmd_op_o.value),
            'bank':  int(self.dut.cmd_bank_o.value),
            'row':   int(self.dut.cmd_row_o.value),
            'col':   int(self.dut.cmd_col_o.value),
            'ap':    int(self.dut.cmd_ap_o.value),
        }

    def strobes(self):
        return {
            'act': int(self.dut.evt_act_o.value),
            'rd':  int(self.dut.evt_rd_o.value),
            'wr':  int(self.dut.evt_wr_o.value),
            'pre': int(self.dut.evt_pre_o.value),
            'wr_commit': int(self.dut.wr_commit_valid_o.value),
            'wr_commit_slot': int(self.dut.wr_commit_slot_o.value),
            'rd_issue': int(self.dut.rd_issue_valid_o.value),
            'rd_issue_slot': int(self.dut.rd_issue_slot_o.value),
            'grant': int(self.dut.refresh_grant_o.value),
        }
