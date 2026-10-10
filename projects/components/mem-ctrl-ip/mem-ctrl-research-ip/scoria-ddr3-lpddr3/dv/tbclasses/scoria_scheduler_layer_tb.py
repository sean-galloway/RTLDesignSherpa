# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Macro testbench for `scoria_scheduler_layer` -- the first COMPOSED scoria.

Every scoria test before this one was a FUB test, and a FUB test mocks its
module's neighbours. A mocked neighbour cannot disagree with you: it answers
exactly as the test author believed it would. This testbench instantiates the
real wiring instead -- arbiter + bank_timers + global_timers + refresh_ctrl +
page_policy + zq_ctrl + init_sequencer + wrlvl_ifc + mode_register + the
command FIFO -- so the seams are live for the first time.

Those seams are where this session's FUB-level findings actually lived: the
arbiter's own in-flight precharge bookkeeping disagreeing with a stale
`bank_row_active`, readiness flops sampling current state instead of next, a
grant gated on a registered decision rather than an accepted fire. Each was
found by reasoning about a boundary the unit test had to model by hand. Here
nobody models them.

What the TB still plays, because they are outside the scheduler:
  * the DFI init handshake   (drive `dfi_init_complete_i`, watch `init_done_o`)
  * mock wr/rd CAMs          (answer the sched lookups, observe commit/issue,
                              retire an entry the moment its slot fires)
  * the DFI command sink     (drain the FIFO, capture the stream WITH CYCLE
                              STAMPS)

Ported from `pumice_mem_cmd_scheduler_tb`, which the two schedulers' 159-line
divergence makes a starting point rather than a drop-in: scoria adds write
leveling, ZQ calibration, mode-register writes and RESET# as a pin, and every
one of those inputs is driven here rather than left to the simulator's
zero-fill. An undriven input in an integration TB is the trap that makes a
composed design look broken.

The timing set is DERIVED, never typed: see `scoria_dram_configs`, which turns
the HAS design point's nanoseconds into programmed register values through the
N+1 convention. `describe()` is logged by the tests so a result can prove which
config produced it.
"""

import os
import subprocess
import sys
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, Timer

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = os.path.join(_repo_root, "bin")
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

from TBClasses.shared.tbbase import TBBase    # noqa: E402
from TBClasses.fub_bfm import fub_consumer    # noqa: E402

_DV = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _DV not in sys.path:
    sys.path.insert(0, _DV)
from tbclasses.scoria_dram_configs import dram_config, describe  # noqa: E402

# dram_op_e (scoria_pkg)
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x0, 0x1, 0x2, 0x3, 0x4, 0x5
OP_PRE, OP_PREA, OP_REF, OP_REFPB = 0x6, 0x7, 0x8, 0x9
OP_MRS, OP_ZQCS, OP_ZQCL = 0xA, 0xB, 0xC
OP_NAMES = {OP_NOP: 'NOP', OP_ACT: 'ACT', OP_RD: 'RD', OP_RDA: 'RDA',
            OP_WR: 'WR', OP_WRA: 'WRA', OP_PRE: 'PRE', OP_PREA: 'PREA',
            OP_REF: 'REF', OP_REFPB: 'REFPB', OP_MRS: 'MRS',
            OP_ZQCS: 'ZQCS', OP_ZQCL: 'ZQCL'}

PAGE_OPEN, PAGE_CLOSE = 0, 1
MEMTYPE_DDR3, MEMTYPE_LPDDR3 = 0, 1


class ScoriaMemCmdSchedulerTB(TBBase):
    def __init__(self, dut, config=None):
        super().__init__(dut)
        self.spacing, self.prog, self.meta = dram_config(config)
        self.config_name = self.meta['name']
        self.NUM_BANKS = self.convert_to_int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH = self.convert_to_int(os.environ.get('ROW_WIDTH', '15'))
        self.COL_WIDTH = self.convert_to_int(os.environ.get('COL_WIDTH', '10'))
        self.NUM_ENTRIES = self.convert_to_int(os.environ.get('NUM_ENTRIES', '8'))
        self.BKW = max(1, (self.NUM_BANKS - 1).bit_length())
        self.cmds = deque()
        self.wr_entry = None
        self.rd_entry = None
        self.wr_committed = []
        self.rd_issued = []
        self._cam_sigs = None
        self._cam_last = {}
        self.pushes = []
        self.unsafe_pushes = []

    async def setup_clocks_and_reset(self):
        # Period from the operating point, never a literal.
        await self.start_clock('aclk', freq=self.meta['mc_ns'], units='ns')
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
        self.log.info("scoria scheduler TB config:\n" + describe(self.config_name))

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        d, p = self.dut, self.prog
        d.page_policy_i.value = PAGE_OPEN
        d.memtype_i.value = MEMTYPE_DDR3
        # ---- JEDEC windows, as PROGRAMMED values (spacing - 1) --------------
        d.t_rcd_i.value = p['tRCD']
        d.t_rp_i.value  = p['tRP']
        d.t_ras_i.value = p['tRAS']
        d.t_rc_i.value  = p['tRC']
        d.t_wr_i.value  = p['tWR']
        d.t_rtp_i.value = p['tRTP']
        d.t_faw_i.value = p['tFAW']
        d.t_rrd_i.value = p['tRRD']
        d.t_wtr_i.value = p['tWTR']
        d.t_rtw_i.value = p['tWTR']      # no separate tRTW in the HAS table
        d.t_ccd_i.value = p['tCCD']
        d.t_refi_i.value = p['tREFI']
        d.t_rfc_i.value  = p['tRFC']
        d.refi_reload_i.value = 0
        d.refresh_burst_i.value = 1
        d.ref_postpone_i.value = 0
        d.ref_pullin_i.value = 0
        d.ref_mode_i.value = 0           # REFab
        d.ref_trefi_pb_i.value = p['tREFI']
        d.ref_trfc_pb_i.value = p['tRFC']
        # ---- Mode A/B/C CSR fields (TASK-001): baseline defaults -----------
        d.ref_elastic_en_i.value = 0
        d.ref_pullin_idle_streak_i.value = 16
        d.ref_postpone_demand_streak_i.value = 1
        d.ref_tcr_en_i.value = 0
        d.ref_trefi_derate_i.value = 0
        d.zq_placement_i.value = 0
        d.zq_overdue_max_i.value = 0
        # ---- scheduler policy knobs: build defaults ------------------------
        d.sched_order_mode_i.value = 0   # FR-FCFS
        d.sched_row_sel_i.value = 0
        d.sched_col_sel_i.value = 0
        d.sched_access_pref_i.value = 0  # column_first
        d.sched_wr_high_wm_i.value = 0   # write batching off
        d.sched_wr_batch_max_i.value = 0
        d.sched_wr_low_wm_i.value = 0
        d.sched_prio_sub_i.value = 0
        d.sched_qos_en_i.value = 0
        d.page_mode_i.value = 0          # arbiter's legacy flat policy
        d.page_tr_init_i.value = 0
        # ---- init sequence: short waits so a test is not mostly waiting ----
        # These are the only values here NOT from the operating point: tINIT is
        # 500 us, which at 10 ns is 50,000 cycles of nothing. The sequence's
        # ORDER is what the init test checks (dv/tests/fub), so the waits are
        # collapsed and that is stated rather than hidden.
        d.t_init_wait_i.value = 4
        d.t_dll_wait_i.value = 4
        d.t_mrd_wait_i.value = 2
        d.t_rp_wait_i.value = 2
        d.t_rfc_wait_i.value = 2
        d.t_xpr_wait_i.value = 4
        d.t_zqinit_wait_i.value = 4
        d.dfi_init_complete_i.value = 0
        d.init_restart_i.value = 0
        # ---- DDR3 mode registers (scoria additions) ------------------------
        # MR0 CL=6 -> {A6,A5,A4}=010 with A2=0, i.e. bits [6:4]=2; the mode
        # register FUB test pins that encoding (JESD79-3F Figure 9).
        d.mr0_i.value = (2 << 4)
        d.mr1_i.value = 0
        d.mr2_i.value = (1 << 3)         # CWL = 1 + 5 = 6
        d.mr3_i.value = 0
        # ---- ZQ calibration ------------------------------------------------
        d.zq_enable_i.value = 0          # off unless a test asks
        d.zq_interval_i.value = 0
        d.t_zqcs_i.value = 16
        # ---- write leveling ------------------------------------------------
        d.wrlvl_strobe_i.value = 0
        d.wrlvl_cs_sel_i.value = 0
        d.wrlvl_prime_dq_i.value = 0
        d.t_wldqsen_i.value = 4
        d.t_wlmrd_i.value = 4
        d.t_wlmrd_max_i.value = 0        # no timeout
        d.t_wlo_i.value = 4
        d.t_wloe_i.value = 4
        # ACTIVE LOW and NOT acked by default: the PHY is only made to answer
        # by a test that wants leveling to progress. Tying this low here would
        # hand every test a PHY that always agrees.
        d.dfi_phylvl_ack_cs_n_i.value = (1 << max(1, len(d.dfi_phylvl_ack_cs_n_i))) - 1
        # ---- CAM-side vectors (driven by _cam_model) -----------------------
        for pfx in ('wr', 'rd'):
            getattr(d, f'{pfx}_sch_valid_i').value = 0
            getattr(d, f'{pfx}_sch_bank_i').value = 0
            getattr(d, f'{pfx}_sch_row_i').value = 0
            getattr(d, f'{pfx}_sch_col_i').value = 0
            getattr(d, f'{pfx}_sch_older_i').value = 0
            getattr(d, f'{pfx}_sch_age_exceed_i').value = 0
            getattr(d, f'{pfx}_sch_qos_i').value = 0
            getattr(d, f'{pfx}_sch_head_rel_i').value = 0
        # cmd / wr_commit / rd_issue readys belong to the GAXI BFMs.

    def _build_bfms(self, profile="backtoback"):
        d = self.dut
        self.cmd_bfm = fub_consumer(
            d, "cmd", d.aclk, profile=profile, log=self.log,
            valid="cmd_valid_o", ready="cmd_ready_i",
            fields={'op':   ("cmd_op_o",   max(1, len(d.cmd_op_o))),
                    'rank': ("cmd_rank_o", max(1, len(d.cmd_rank_o))),
                    'bank': ("cmd_bank_o", max(1, len(d.cmd_bank_o))),
                    'row':  ("cmd_row_o",  max(1, len(d.cmd_row_o))),
                    'col':  ("cmd_col_o",  max(1, len(d.cmd_col_o))),
                    'ap':   ("cmd_ap_o",   1)})
        self.wr_commit_bfm = fub_consumer(
            d, "wr_commit", d.aclk, profile=profile, log=self.log,
            valid="wr_commit_valid_o", ready="wr_commit_ready_i",
            fields={'slot': ("wr_commit_slot_o",
                             max(1, len(d.wr_commit_slot_o)))})
        self.rd_issue_bfm = fub_consumer(
            d, "rd_issue", d.aclk, profile=profile, log=self.log,
            valid="rd_issue_valid_o", ready="rd_issue_ready_i",
            fields={'slot': ("rd_issue_slot_o",
                             max(1, len(d.rd_issue_slot_o)))})

    # ---- mock CAMs ----------------------------------------------------------
    def _apply_cam(self):
        """Place the single pending entry per side into the sch_* vectors.

        Models the real CAMs' scheduled/issued exclusion: an entry whose
        commit/issue is firing THIS cycle drops out of the schedulable set, as
        the real `r_sched` / `r_issued` bits do. Without that the arbiter
        re-picks the same slot with no throttle.

        Called every cycle, so handles resolve once and values are written only
        when they change -- these are levels the DUT samples, not pulses.
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
                row |= (ent['row'] & ((1 << self.ROW_WIDTH) - 1)) << (e * self.ROW_WIDTH)
                col |= (ent['col'] & ((1 << self.COL_WIDTH) - 1)) << (e * self.COL_WIDTH)
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
                self.wr_entry = None
            if int(self.dut.rd_issue_valid_o.value):
                self.rd_issued.append(int(self.dut.rd_issue_slot_o.value))
                self.rd_entry = None

    async def _cmd_sink(self):
        """Drain the command FIFO, stamping the CYCLE of every command.

        The stamp is the point. A caller reasoning about JEDEC spacing from
        list indices is counting COMMANDS in between, not cycles -- a
        distinction that already turned a real pumice finding into a false
        positive once.

        `row` is recorded only for an ACT. A DRAM column command carries bank
        and column; its row is implied by whatever ACT opened the bank, and the
        arbiter assigns `w_row` only on its ACT branches. Recording the
        don't-care 0 beside a RD makes every column op look like it addresses
        row 0.
        """
        cyc = 0
        while True:
            await RisingEdge(self.dut.aclk)
            cyc += 1
            if int(self.dut.cmd_valid_o.value) and int(self.dut.cmd_ready_i.value):
                op = int(self.dut.cmd_op_o.value)
                self.cmds.append({
                    'cycle': cyc,
                    'op': op,
                    'name': OP_NAMES.get(op, hex(op)),
                    'bank': int(self.dut.cmd_bank_o.value),
                    'row': int(self.dut.cmd_row_o.value) if op == OP_ACT else None,
                    'col': int(self.dut.cmd_col_o.value),
                    'ap': int(self.dut.cmd_ap_o.value),
                })

    async def _arbiter_audit(self):
        """Every cmd-FIFO push, with the arbiter's own final safety verdict.

        `w_out_safe` is the arbiter's last-moment re-check of a registered pick
        against the freshest bank-timer state. A push while it is LOW is a
        command the controller decided not to issue and issued anyway -- pumice
        BUG-003, where the FIFO took a rejected pick while `evt_*` never
        strobed, so the timers, the guard chains and the CAM retire all missed
        a command the DRAM executed. `unsafe_pushes` must stay empty for every
        config and traffic pattern, which is why the invariant lives in the TB
        rather than in the one test that found it.

        Sampled 1 ps AFTER the edge, never on it: these are combinational, and
        reading them on the edge samples before the deltas settle -- which once
        made an arbiter-side count come up exactly one short and wrongly
        exonerate the arbiter.
        """
        arb = self.dut.u_arbiter
        cyc = 0
        while True:
            await RisingEdge(self.dut.aclk)
            await Timer(1, 'ps')
            cyc += 1
            try:
                pushing = (int(arb.cmd_valid_o.value)
                           and int(arb.cmd_ready_i.value))
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

    # ---- helpers ------------------------------------------------------------
    async def complete_init(self, max_cycles=400):
        """Raise dfi_init_complete and wait for the sequencer to finish.

        DDR3 init here is RESET# -> CKE -> tXPR -> MR2/MR3/MR1/MR0 -> ZQCL ->
        tDLLK/tZQinit. Write leveling is NOT part of it -- it is a separate
        engine a CSR strobe starts -- so this does not need the PHY to ack
        anything.
        """
        self.dut.dfi_init_complete_i.value = 1
        for _ in range(max_cycles):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.init_done_o.value):
                return True
        return False

    async def wait_for_ops(self, *ops, since=0, limit=200):
        """Wait until an op from `ops` appears in the CAPTURED stream.

        Wait on the sink, never on `rd_issue_valid_o` / `wr_commit_valid_o`.
        Those fire when the arbiter ISSUES, which is CMD_DELAY plus the FIFO
        ahead of the command reaching the DRAM-facing stream -- so a loop that
        breaks on the issue strobe and then inspects `self.cmds` finds nothing
        and reads as "the composition produced no command". That is exactly how
        this TB's first act-then-read case failed against a design that was
        working: the probe showed ACT@57 RD@62 while the test had already given
        up at the issue strobe.

        Returns the matching commands from index `since`, or [] on timeout.
        """
        want = set(ops)
        for _ in range(limit):
            hit = [c for c in list(self.cmds)[since:] if c['op'] in want]
            if hit:
                return hit
            await RisingEdge(self.dut.aclk)
        return []

    async def drain(self, cycles=None):
        """Let the command pipeline empty: CMD_DELAY plus FIFO, with margin."""
        for _ in range(cycles if cycles is not None else 24):
            await RisingEdge(self.dut.aclk)

    def ops_of(self, *ops):
        want = set(ops)
        return [c for c in self.cmds if c['op'] in want]

    def stream(self):
        """The captured stream as 'NAME@cycle' strings, for a failure message."""
        return " ".join(f"{c['name']}@{c['cycle']}" for c in self.cmds)

    def stat(self, name):
        return int(getattr(self.dut, name).value)
