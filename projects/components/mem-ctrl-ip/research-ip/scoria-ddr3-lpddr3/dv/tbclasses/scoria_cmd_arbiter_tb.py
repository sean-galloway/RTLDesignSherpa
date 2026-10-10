# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Testbench for `scoria_cmd_arbiter`.

Ported from `pumice_cmd_arbiter_tb` -- the two arbiters' port lists differ by
exactly four signals (`zq_req_i`, `zq_grant_o`, `t_zqcs_i`, `stall_zq_o`), the
DDR3 ZQ-calibration arm -- so the neighbour mocks carry over unchanged and the
new surface is the ZQ arm plus whatever the DDR3 ops touch.

What it mocks: per-bank and global timer readiness (live AND the lookahead
twins), both CAMs' sched-lookup ports, the page-policy block's auto-precharge
and background-close requests, init passthrough, refresh request, the ZQ
request, and the command sink. It reads back the picked command plus the
evt/commit/issue/grant strobes and the stall counters.

Two traps inherited from the pumice TB, both of which cost real debugging there
and are preserved here deliberately:

  * the three `bank_*_ready_i` vectors each have an ADVISORY lookahead twin,
    and `r_bank_*_ready` samples the TWIN. Setting only the live vector starves
    the pick pipeline no matter what the live inputs say, which looks exactly
    like a broken arbiter. `set_bank_bits` writes both.
  * the arbiter keeps its OWN record of precharges it has issued, so once it
    has sent a PRE to a bank it proceeds as if that bank is closed -- whatever
    `bank_row_active_i` still says. A testbench that leaves the bit asserted
    after the PRE is not holding the bank open; it is only lying about it. To
    hold a bank genuinely open, refuse its precharge (`bank_pre_ready_i`),
    which is what a bank timer inside tRAS does.
  * demand picks (column / ACT / PRE) take FOUR edges to appear -- registered
    timer fan-in, the arg_sel input snapshot, the per-class pre-pick register,
    then the output decision. INIT, REFRESH and ZQ picks are decoded directly
    and appear at TWO. A test that settles the wrong depth reads the previous
    decision and concludes the arbiter ignored its stimulus.

Every one of the arbiter's three output handshakes is driven by a GAXI BFM
(`TBClasses.fub_bfm`), never by poking ready: a consumer that deasserts ready
is what a full downstream FIFO looks like, and modelling it with a constant 1
hides every backpressure path.
"""

import os
import sys
import subprocess

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

# dram_op_e (scoria_pkg) -- the DDR3 ops past OP_REF are what pumice's copy
# of this table stops short of.
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x0, 0x1, 0x2, 0x3, 0x4, 0x5
OP_PRE, OP_PREA, OP_REF, OP_REFPB = 0x6, 0x7, 0x8, 0x9
OP_MRS, OP_ZQCS, OP_ZQCL = 0xA, 0xB, 0xC
OP_NAMES = {OP_NOP: 'NOP', OP_ACT: 'ACT', OP_RD: 'RD', OP_RDA: 'RDA',
            OP_WR: 'WR', OP_WRA: 'WRA', OP_PRE: 'PRE', OP_PREA: 'PREA',
            OP_REF: 'REF', OP_REFPB: 'REFPB', OP_MRS: 'MRS',
            OP_ZQCS: 'ZQCS', OP_ZQCL: 'ZQCL'}

# page_policy_e
PAGE_OPEN, PAGE_CLOSE = 0, 1

STALLS = ('stall_bp_o', 'stall_refresh_o', 'stall_turnaround_o',
          'stall_tccd_o', 'stall_actlimit_o', 'stall_banktimer_o',
          'stall_noreq_o', 'stall_zq_o')


class ScoriaCmdArbiterTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_BANKS = self.convert_to_int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH = self.convert_to_int(os.environ.get('ROW_WIDTH', '15'))
        self.COL_WIDTH = self.convert_to_int(os.environ.get('COL_WIDTH', '10'))
        self.NUM_ENTRIES = self.convert_to_int(os.environ.get('NUM_ENTRIES', '8'))
        self.BKW = max(1, (self.NUM_BANKS - 1).bit_length())

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._build_bfms()
        self._drive_idle()
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 4)
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 2)
        await Timer(1, units='ns')

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        d = self.dut
        d.page_policy_i.value = PAGE_OPEN
        d.init_done_i.value = 1
        d.init_cmd_valid_i.value = 0
        d.init_cmd_op_i.value = OP_NOP
        d.init_cmd_bank_i.value = 0
        d.init_cmd_row_i.value = 0
        d.refresh_req_i.value = 0
        d.refresh_drain_i.value = 0
        d.refresh_kind_i.value = 0
        d.refresh_bank_i.value = 0
        d.t_rfc_i.value = 8
        d.t_rfc_pb_i.value = 0
        # ---- the scoria additions. Driven explicitly: an undriven input is a
        # trap even where the simulator zero-fills it, because the next
        # simulator does not have to.
        d.zq_req_i.value = 0
        d.t_zqcs_i.value = 16          # ~tZQCS at the board's 1:4 gear
        # ---- the page-policy interface. pumice's TB left these undriven.
        d.ap_mode_en_i.value = 0
        d.ap_close_i.value = 0
        d.timeout_pre_req_i.value = 0
        d.timeout_pre_bank_i.value = 0
        d.sched_order_mode_i.value = 0      # FR-FCFS build default
        d.sched_row_sel_i.value = 0         # oldest
        d.sched_col_sel_i.value = 0         # oldest
        d.sched_access_pref_i.value = 0     # column_first
        d.sched_wr_high_wm_i.value = 0      # write batching off
        d.sched_wr_batch_max_i.value = 0
        d.sched_wr_low_wm_i.value = 0
        d.sched_prio_sub_i.value = 0        # load_over_store
        d.sched_qos_en_i.value = 0
        d.rd_sch_qos_i.value = 0
        d.wr_sch_qos_i.value = 0
        d.rd_sch_age_exceed_i.value = 0
        d.wr_sch_age_exceed_i.value = 0
        d.rd_sch_head_rel_i.value = 0
        d.wr_sch_head_rel_i.value = 0
        d.bank_act_ready_i.value = 0
        d.bank_rdwr_ready_i.value = 0
        d.bank_pre_ready_i.value = 0
        d.bank_act_ready_la_i.value = 0
        d.bank_rdwr_ready_la_i.value = 0
        d.bank_pre_ready_la_i.value = 0
        d.bank_row_active_i.value = 0
        d.bank_open_row_i.value = 0
        d.tfaw_ok_i.value = 1
        d.trrd_ok_i.value = 1
        d.twtr_ok_i.value = 1
        d.trtw_ok_i.value = 1
        d.tccd_ok_i.value = 1
        d.t_ccd_i.value = 1
        for pfx in ('wr', 'rd'):
            getattr(d, f'{pfx}_sch_valid_i').value = 0
            getattr(d, f'{pfx}_sch_bank_i').value = 0
            getattr(d, f'{pfx}_sch_row_i').value = 0
            getattr(d, f'{pfx}_sch_col_i').value = 0
            getattr(d, f'{pfx}_sch_older_i').value = 0
        # cmd / wr_commit / rd_issue readys belong to the BFMs (_build_bfms).

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

    # ---- per-bank vector helpers -------------------------------------------
    def _la_twin(self, sig):
        for live, la in (("bank_act_ready_i",  "bank_act_ready_la_i"),
                         ("bank_rdwr_ready_i", "bank_rdwr_ready_la_i"),
                         ("bank_pre_ready_i",  "bank_pre_ready_la_i")):
            if sig is getattr(self.dut, live):
                return getattr(self.dut, la)
        return None

    def set_bank_bits(self, sig, bank_to_val):
        v = 0
        for b, on in bank_to_val.items():
            if on:
                v |= (1 << b)
        sig.value = v
        twin = self._la_twin(sig)
        if twin is not None:
            twin.value = v

    def all_banks_ready(self, on=True):
        """Every bank permitted every operation (or none)."""
        every = {b: 1 if on else 0 for b in range(self.NUM_BANKS)}
        for s in ('bank_act_ready_i', 'bank_rdwr_ready_i', 'bank_pre_ready_i'):
            self.set_bank_bits(getattr(self.dut, s), every)

    def set_open_rows(self, rows):
        v = 0
        for b, r in rows.items():
            v |= (r & ((1 << self.ROW_WIDTH) - 1)) << (b * self.ROW_WIDTH)
        self.dut.bank_open_row_i.value = v

    def set_entries(self, pfx, entries):
        """entries: {slot: (bank, row, col, age)}; age higher == older."""
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
            row |= (r & ((1 << self.ROW_WIDTH) - 1)) << (e * self.ROW_WIDTH)
            col |= (c & ((1 << self.COL_WIDTH) - 1)) << (e * self.COL_WIDTH)
        for i, ai in ages.items():
            for j, aj in ages.items():
                if i != j and ai > aj:
                    older |= (1 << (i * N + j))
        getattr(self.dut, f'{pfx}_sch_valid_i').value = valid
        getattr(self.dut, f'{pfx}_sch_bank_i').value = bank
        getattr(self.dut, f'{pfx}_sch_row_i').value = row
        getattr(self.dut, f'{pfx}_sch_col_i').value = col
        getattr(self.dut, f'{pfx}_sch_older_i').value = older

    # ---- time ---------------------------------------------------------------
    async def settle(self, depth=4):
        """Advance `depth` edges, then settle combinational.

        depth=4 for demand picks, depth=2 for INIT / REFRESH / ZQ -- see the
        module docstring.
        """
        for _ in range(depth):
            await RisingEdge(self.dut.aclk)
        await Timer(1, units='ns')

    async def step(self):
        """ONE edge + settle. Poll with this, never with settle().

        A multi-edge stride aliases against the pick's period (the pipeline
        throttles columns to every 2-3 cycles), so a poll advancing by settle()
        can phase-lock onto the idle cycle and never see the pick.
        """
        await RisingEdge(self.dut.aclk)
        await Timer(1, units='ns')

    def set_cmd_ready(self, accepting: bool):
        self.cmd_bfm.set_ready_policy('always' if accepting else 'stall')

    # ---- readback -----------------------------------------------------------
    def picked(self):
        d = self.dut
        return {'valid': int(d.cmd_valid_o.value),
                'op':    int(d.cmd_op_o.value),
                'bank':  int(d.cmd_bank_o.value),
                'row':   int(d.cmd_row_o.value),
                'col':   int(d.cmd_col_o.value),
                'ap':    int(d.cmd_ap_o.value)}

    def op_name(self):
        p = self.picked()
        return OP_NAMES.get(p['op'], hex(p['op'])) if p['valid'] else 'idle'

    def strobes(self):
        d = self.dut
        return {'act': int(d.evt_act_o.value),
                'rd':  int(d.evt_rd_o.value),
                'wr':  int(d.evt_wr_o.value),
                'pre': int(d.evt_pre_o.value),
                'ap':  int(d.evt_ap_o.value),
                'wr_commit': int(d.wr_commit_valid_o.value),
                'rd_issue':  int(d.rd_issue_valid_o.value),
                'grant': int(d.refresh_grant_o.value),
                'zq_grant': int(d.zq_grant_o.value)}

    def stalls(self):
        return {k: int(getattr(self.dut, k).value) for k in STALLS}
