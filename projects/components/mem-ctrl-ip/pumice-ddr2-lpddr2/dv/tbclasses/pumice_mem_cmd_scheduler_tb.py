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
from cocotb.triggers import RisingEdge, Timer

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
from tbclasses.pumice_dram_configs import (            # noqa: E402
    dram_config, describe as describe_config,
)

OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA, OP_PRE, OP_PREA, OP_REF, OP_REFPB, OP_MRS = range(11)
PAGE_OPEN, PAGE_CLOSE = 0, 1
MEMTYPE_DDR2 = 0


def _resolve_cfg(config=None):
    """(name, model_timings, controller_mc_cycles, meta) for a named point.

    A test may pass a name; otherwise DRAM_CONFIG in the environment decides;
    otherwise the BOARD. A default that is a constant rather than the board is
    how this suite spent months measuring the wrong thing
    (feedback_config_register_not_default).
    """
    model, ctrl, meta = dram_config(config)
    return meta['name'], model, ctrl, meta


class PumiceMemCmdSchedulerTB(TBBase):
    # THE OPERATING POINT, not a pile of constants. This TB used to clock aclk at
    # 100 MHz (`freq=10, units='ns'`) and program t_rcd=3 t_rp=3 t_ras=5 t_rc=8
    # t_faw=6 -- a timing set belonging to no part at no frequency. pumice
    # BUG-003 was root-caused on that config and the writeup claimed the board;
    # the mechanism was structural and held anyway, but the claim was false and
    # had to be corrected. A scheduler-layer TB is single-domain, so a frequency
    # reaches it ONLY through these cycle counts -- which is exactly why the
    # config axis belongs here and is worth sweeping.
    def __init__(self, dut, config=None):
        super().__init__(dut)
        self.config_name, self._model_t, self._ctrl_t, self.meta = _resolve_cfg(config)
        self.BL = self.meta['BL']
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
        self._cam_sigs = None          # handle cache, see _apply_cam
        self._cam_last = {}            # last value written per side
        # arbiter push audit (see _arbiter_audit)
        self.pushes = []
        self.unsafe_pushes = []

    async def setup_clocks_and_reset(self):
        # Period from the operating point, never a literal.
        await self.start_clock('aclk', freq=self.meta['aclk_ns'], units='ns')
        self._build_bfms()
        self._drive_idle()
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 6)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 3)
        cocotb.start_soon(self._cam_model())
        cocotb.start_soon(self._cmd_sink())
        cocotb.start_soon(self._track_commit_issue())
        cocotb.start_soon(self._arbiter_audit())

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.page_policy_i.value = PAGE_OPEN
        self.dut.memtype_i.value = MEMTYPE_DDR2
        # timing (small, legal-ish)
        # DERIVED from the operating point. The keys are the derivation's own
        # (JEDEC) names; the ports are the RTL's. t_rtw is the one term that is
        # not a pure JEDEC delay -- it carries a measured PHY read-pipeline floor
        # (pumice BUG-014 (was PUMICE-037)) -- and it comes from the same derivation so it cannot
        # drift from the rest.
        t = self._ctrl_t
        self.dut.t_rcd_i.value  = t['tRCD']
        self.dut.t_rp_i.value   = t['tRP']
        self.dut.t_ras_i.value  = t['tRAS']
        self.dut.t_rc_i.value   = t['tRC']
        self.dut.t_wr_i.value   = t['tWR']
        self.dut.t_rtp_i.value  = t['tRTP']
        self.dut.t_faw_i.value  = t['tFAW']
        self.dut.t_rrd_i.value  = t['tRRD']
        self.dut.t_wtr_i.value  = t['tWTR']
        self.dut.t_rtw_i.value  = t['tRTW']
        self.dut.t_ccd_i.value  = t['tCCD']
        self.dut.t_refi_i.value = t['tREFI']
        self.dut.t_rfc_i.value  = t['tRFC']
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
        """Drive the mock CAM's request signals.

        CALLED EVERY CYCLE, so it is written to cost nothing when nothing
        changed. It used to resolve `getattr(self.dut, f'{pfx}_sch_valid_i')`
        and its four siblings from a fresh f-string every cycle and then write
        all ten signals unconditionally -- 10 f-strings, 10 getattrs and 10
        simulator writes per clock, whether or not a single bit differed.
        Signal writes were the largest remaining cost in the profile after the
        TBBase fix (167k writes across ~8k cycles, ~21 per cycle).

        Handles are resolved once; values are written only when they change.
        That is safe because these are LEVEL signals the DUT samples, not
        pulses -- a value that did not change does not need re-driving.
        """
        if self._cam_sigs is None:
            self._cam_sigs = {
                pfx: tuple(getattr(self.dut, f'{pfx}_sch_{f}_i')
                           for f in ('valid', 'bank', 'row', 'col', 'older'))
                for pfx in ('wr', 'rd')
            }
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
            # single pending entry per side -> it is trivially the oldest, so the
            # order matrix is don't-care (arg_oldest needs no OTHER masked entry).
            nv = (valid, bank, row, col, 0)
            if self._cam_last.get(pfx) == nv:
                continue
            self._cam_last[pfx] = nv
            for sig, val in zip(self._cam_sigs[pfx], nv):
                sig.value = val

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
        # Stamp the CYCLE each command issues on. Without it a caller reasoning
        # about JEDEC spacing has only the list index, which is the number of
        # commands in between -- not cycles. That distinction silently turned a
        # pumice BUG-014 (was PUMICE-037) "PRE 1 cycle after RD" into a false positive.
        cyc = 0
        while True:
            await RisingEdge(self.dut.aclk)
            cyc += 1
            if int(self.dut.cmd_valid_o.value) and int(self.dut.cmd_ready_i.value):
                op = int(self.dut.cmd_op_o.value)
                # ROW IS ONLY MEANINGFUL ON AN ACT. A DRAM column command carries
                # bank and column, not a row -- the row is implied by whatever
                # ACT opened the bank. pumice's arbiter assigns w_row only on its
                # ACT branches, so cmd_row_o reads 0 beside a RD/WR. Recording
                # that 0 as if it were the target row makes every column op look
                # like it addresses row 0, which is exactly what the stream
                # checker's wrong-row rule then reported. None means "not
                # observable here", and the checker skips the comparison rather
                # than inventing a verdict from a don't-care.
                self.cmds.append({
                    'cycle': cyc,
                    'op':   op,
                    'bank': int(self.dut.cmd_bank_o.value),
                    'row':  int(self.dut.cmd_row_o.value) if op == OP_ACT else None,
                    'col':  int(self.dut.cmd_col_o.value),
                    'ap':   int(self.dut.cmd_ap_o.value),
                })

    # ---- helpers ------------------------------------------------------------
    async def _arbiter_audit(self):
        """Record every cmd-FIFO push, and whether the arbiter's OWN final
        safety gate had approved it.

        `w_out_safe` is the arbiter's last-moment re-check of a registered pick
        against the freshest bank-timer state. A push that happens while it is
        LOW is a command the controller decided not to issue and issued anyway.
        That was pumice BUG-003: `cmd_valid_o` was `r_pick_valid` with no
        `w_out_safe` term, so the reject freed the output register (which the
        code called "dropping") while the FIFO took the command regardless -- and
        because `w_fire_out` DOES carry the term, `evt_*` never strobed and the
        bank timers, the guard chains and the CAM retire all recorded a command
        that the DRAM had executed.

        The invariant is one comparison and it holds for every config, every
        paging mode and every traffic pattern, so it lives here rather than in
        the one test that found it. `unsafe_pushes` must stay empty.

        SAMPLED 1 ps AFTER the edge, never on it: `w_out_safe` and `cmd_valid_o`
        are combinational, and reading them on the edge samples before the deltas
        settle -- which is what once made an arbiter-side count come up exactly
        one short (776 vs 777) and wrongly exonerate the arbiter.
        """
        arb = self.dut.u_arbiter
        cyc = 0
        while True:
            await RisingEdge(self.dut.aclk)
            await Timer(1, 'ps')
            cyc += 1
            try:
                pushing = int(arb.cmd_valid_o.value) and int(arb.cmd_ready_i.value)
            except Exception:
                return              # no arbiter visibility; audit is inert
            if not pushing:
                continue
            rec = dict(cycle=cyc, op=int(arb.r_op.value),
                       bank=int(arb.r_bank.value),
                       safe=int(arb.w_out_safe.value),
                       fire=int(arb.w_fire_out.value))
            self.pushes.append(rec)
            if not rec['safe']:
                self.unsafe_pushes.append(rec)

    async def complete_init(self, max_cycles=200):
        self.dut.dfi_init_complete_i.value = 1
        for _ in range(max_cycles):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.init_done_o.value):
                return True
        return False

    def ops_of(self, op):
        return [c for c in self.cmds if c['op'] == op]
