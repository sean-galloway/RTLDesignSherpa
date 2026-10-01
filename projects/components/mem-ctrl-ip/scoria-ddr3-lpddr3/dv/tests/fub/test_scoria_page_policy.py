# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_page_policy` -- page-policy engine + page telemetry.

This block has no pumice twin to lean on (pumice's is `page_predictor`, a
different design), and most of its content is counters that a board session
reads and believes. pumice ISSUE-014 and TASK-012 are both in the header: a
derived hit count (`col_ops - ACT`) went NEGATIVE on silicon, and a
free-running refresh counter overstated its window by 2584x because it was
timing the HOST. Telemetry that lies is worse than none, so every counter here
is measured against a stimulus whose correct answer is known by construction.

The one thing the testbench must get right to mean anything is the RELATIONSHIP
between the issued-command stream and `bank_row_active_i`. In the design those
come from two different places: `cmd_valid_i` is the arbiter's issue stream, and
`bank_row_active_i` is the bank timers' REGISTERED row state, which rises the
cycle AFTER the ACT that opens the row and falls the cycle after the PRE that
closes it. `PpTB.issue` reproduces that one-cycle lag. Driving row_active
in the same cycle as the ACT would be a friendlier world than the RTL lives in,
and it hides the arming behaviour that `act_alone_does_not_arm_the_timer`
documents.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

# dram_op_e, scoria_pkg
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x0, 0x1, 0x2, 0x3, 0x4, 0x5
OP_PRE, OP_PREA, OP_REF, OP_REFPB = 0x6, 0x7, 0x8, 0x9

MODE_DEFAULT, MODE_STATIC_OPEN, MODE_STATIC_CLOSE, MODE_FIXED_OPEN = 0, 1, 2, 3
NUM_BANKS = 8
ROW_WIDTH = 15

STATS = ('stat_page_hit_o', 'stat_page_miss_o', 'stat_page_empty_o',
         'stat_act_o', 'stat_pre_o', 'stat_ref_o', 'stat_ref_busy_o')


class PpTB(TBBase):
    """Drives the issued-command stream and models the bank row state.

    `row_active` follows the commands with the bank timers' one-cycle
    registration lag, because that is what the RTL sees.
    """

    async def setup(self, *, mode=MODE_FIXED_OPEN, tr=4, demand=0):
        await self.start_clock('aclk', 10, 'ns')
        d = self.dut
        d.policy_mode_i.value = mode
        d.tr_init_i.value = tr
        d.demand_i.value = demand
        d.cmd_valid_i.value = 0
        d.cmd_op_i.value = OP_NOP
        d.cmd_bank_i.value = 0
        d.cmd_row_i.value = 0
        self.active = 0                       # bank_row_active_i mirror
        self.rows = [0] * NUM_BANKS
        d.bank_row_active_i.value = 0
        d.bank_open_row_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 2)
        await Timer(1, 'ns')

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    def _publish(self):
        d = self.dut
        d.bank_row_active_i.value = self.active
        packed = 0
        for b in range(NUM_BANKS):
            packed |= (self.rows[b] & ((1 << ROW_WIDTH) - 1)) << (b * ROW_WIDTH)
        d.bank_open_row_i.value = packed

    async def tick(self):
        await RisingEdge(self.dut.aclk)
        await Timer(1, 'ns')

    async def issue(self, op, bank=0, row=0):
        """Issue one command for one cycle, then apply its effect on the row
        state at the NEXT cycle boundary -- the bank timers' registration lag.
        """
        d = self.dut
        d.cmd_valid_i.value = 1
        d.cmd_op_i.value = op
        d.cmd_bank_i.value = bank
        d.cmd_row_i.value = row
        await self.tick()
        d.cmd_valid_i.value = 0
        d.cmd_op_i.value = OP_NOP
        if op == OP_ACT:
            self.active |= (1 << bank)
            self.rows[bank] = row
        elif op == OP_PRE:
            self.active &= ~(1 << bank)
        elif op == OP_PREA:
            self.active = 0
        self._publish()
        await Timer(1, 'ns')

    async def idle(self, n=1):
        for _ in range(n):
            await self.tick()

    def stat(self, name):
        return int(getattr(self.dut, name).value)

    def row_hit(self, b):
        return int(self.dut.stat_row_hit_o[b].value)

    def snapshot(self):
        s = {k: self.stat(k) for k in STATS}
        s['row_hit'] = [self.row_hit(b) for b in range(NUM_BANKS)]
        return s

    async def open_and_touch(self, bank, row=0x123):
        """ACT then one column op -- the sequence that actually arms the timer."""
        await self.issue(OP_ACT, bank, row)
        await self.issue(OP_RD, bank)

    async def wait_timeout_req(self, bank=None, limit=400):
        """Index of the first mid-cycle sample where the close request is up.

        `issue()` leaves the clock mid-cycle T+1, where T is the command's own
        cycle, so index 0 is already one cycle past the reload. The timer
        loads tr at edge T, counts down one per edge, and registers expiry on
        the edge where it reads 1 -- so the request appears at index tr, and
        the row has been idle for tr+1 cycles by then.
        """
        for i in range(limit):
            if int(self.dut.timeout_pre_req_o.value):
                if bank is None or int(self.dut.timeout_pre_bank_o.value) == bank:
                    return i
            await self.tick()
        return None


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_scoria_page_policy(dut):
    tt = os.environ.get("TEST_TYPE", "mode_select_drives_ap")
    tb = PpTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "mode_select_drives_ap":
        # The mode field is the only thing standing between the arbiter's
        # legacy flat page policy and this block. A mode that claims the
        # override without driving a decision closes every page or none.
        want = {
            MODE_DEFAULT:      (0, 0),
            MODE_STATIC_OPEN:  (1, 0),
            MODE_STATIC_CLOSE: (1, (1 << NUM_BANKS) - 1),
            MODE_FIXED_OPEN:   (1, 0),
            4: (0, 0), 5: (0, 0), 6: (0, 0), 7: (0, 0),
        }
        for mode, (en, ap) in want.items():
            await tb.setup(mode=mode, tr=4)
            got_en = int(dut.ap_mode_en_o.value)
            got_ap = int(dut.ap_close_o.value)
            chk((got_en, got_ap) == (en, ap),
                f"mode {mode}: ap_mode_en={got_en} ap_close=0x{got_ap:02X}, "
                f"expected en={en} ap=0x{ap:02X}. Modes 4-7 are retired and "
                f"must fall through to the build default -- claiming the "
                f"override with no decision behind it is worse than mode 0.")

    elif tt == "timeout_expiry_is_exact":
        # fixed_open's only close mechanism. Measured, not bounded: a timeout
        # that fires early closes rows the workload is still using, and one
        # that never fires makes the mode inert.
        for tr in (1, 3, 8):
            await tb.setup(mode=MODE_FIXED_OPEN, tr=tr)
            await tb.open_and_touch(0)
            g = await tb.wait_timeout_req(bank=0)
            chk(g == tr,
                f"tr={tr}: timeout_pre_req rose at index {g}, expected {tr} "
                f"(= tr+1 cycles of idle after the last command; see "
                f"wait_timeout_req for the index mapping)")
            chk(int(dut.timeout_pre_bank_o.value) == 0,
                f"tr={tr}: request names bank "
                f"{int(dut.timeout_pre_bank_o.value)}, not the open one")

    elif tt == "timeout_reloads_on_every_command":
        # "Any command to the bank re-warms the row." A timer that does not
        # reload closes a page in the middle of a same-row burst.
        tr = 5
        await tb.setup(mode=MODE_FIXED_OPEN, tr=tr)
        await tb.open_and_touch(0)
        for _ in range(4):
            await tb.idle(tr - 1)
            chk(int(dut.timeout_pre_req_o.value) == 0,
                "timeout fired while the bank was still being touched every "
                f"{tr - 1} cycles -- each command must restart the window")
            await tb.issue(OP_RD, 0)
        g = await tb.wait_timeout_req(bank=0)
        chk(g == tr,
            f"after the last touch the timeout came at index {g}, expected {tr}")

    elif tt == "timeout_disabled_states":
        # Two OFF states, and both need their own stimulus: tr==0 (the CSR's
        # "build default") and any mode other than fixed_open.
        await tb.setup(mode=MODE_FIXED_OPEN, tr=0)
        await tb.open_and_touch(0)
        await tb.idle(80)
        chk(int(dut.timeout_pre_req_o.value) == 0,
            "tr=0 raised a timeout close -- 0 disables the bank's timeout, so "
            "a row would be closed by a mechanism software switched off")
        for mode in (MODE_DEFAULT, MODE_STATIC_OPEN, MODE_STATIC_CLOSE):
            await tb.setup(mode=mode, tr=2)
            await tb.open_and_touch(0)
            await tb.idle(40)
            chk(int(dut.timeout_pre_req_o.value) == 0,
                f"mode {mode} raised a background close; the idle timeout is "
                f"fixed_open's mechanism only, and one close mechanism per "
                f"mode is the design rule")

    elif tt == "timeout_holds_until_the_row_closes":
        # The request is sticky: the arbiter picks it up at lowest priority and
        # may take many cycles. A request that drops itself loses the close.
        await tb.setup(mode=MODE_FIXED_OPEN, tr=2)
        await tb.open_and_touch(3)
        await tb.wait_timeout_req(bank=3)
        for i in range(25):
            chk(int(dut.timeout_pre_req_o.value) == 1,
                f"timeout request dropped {i} cycles after it rose, with the "
                f"row still open -- the arbiter had not acted on it yet")
            await tb.tick()
        await tb.issue(OP_PRE, 3)
        await tb.idle(2)
        chk(int(dut.timeout_pre_req_o.value) == 0,
            "timeout request still high after the PRE closed the row")

    elif tt == "timeout_picks_the_lowest_bank":
        # The header says lowest-numbered expired bank; the loop counts DOWN
        # and relies on the last write winning, which is the kind of thing a
        # refactor reverses silently.
        await tb.setup(mode=MODE_FIXED_OPEN, tr=2)
        for b in (5, 2, 7):
            await tb.open_and_touch(b)
        await tb.wait_timeout_req()
        chk(int(dut.timeout_pre_bank_o.value) == 2,
            f"three banks expired (2, 5, 7) and the request names "
            f"{int(dut.timeout_pre_bank_o.value)}; the contract is the "
            f"lowest-numbered one")
        await tb.issue(OP_PRE, 2)
        await tb.idle(2)
        chk(int(dut.timeout_pre_req_o.value) == 1
            and int(dut.timeout_pre_bank_o.value) == 5,
            f"after closing bank 2 the request should move to bank 5, got "
            f"req={int(dut.timeout_pre_req_o.value)} "
            f"bank={int(dut.timeout_pre_bank_o.value)}")

    elif tt == "act_alone_does_not_arm_the_timer":
        # DOCUMENTS a real asymmetry rather than asserting a wish. The timer's
        # reload branch is gated behind `bank_row_active_i[b]`, and row_active
        # rises the cycle AFTER the ACT, so the ACT's own reload is discarded
        # and a row opened with no column op behind it never times out. In the
        # live design the arbiter only activates when it has a column to issue,
        # so the case is unreachable from traffic -- but any future speculative
        # or pre-activating path inherits a row that stays open forever.
        await tb.setup(mode=MODE_FIXED_OPEN, tr=3)
        await tb.issue(OP_ACT, 1, 0x55)
        g = await tb.wait_timeout_req(bank=1, limit=60)
        chk(g is None,
            f"the ACT alone armed the timer (request at {g}). If the RTL has "
            f"been changed to arm on the ACT, that is an improvement -- update "
            f"this case and the header note, do not delete the check.")
        # And one column op is enough to arm it.
        await tb.issue(OP_RD, 1)
        g = await tb.wait_timeout_req(bank=1)
        chk(g == 3,
            f"a column op to the open bank left the timer unarmed too "
            f"(request at index {g}, expected 3 for tr=3) -- then fixed_open "
            f"has no close mechanism at all")

    elif tt == "row_hit_excludes_the_activations_own_column":
        # pumice BUG-020's counter. The first column after an ACT is the
        # activation's own access and is NOT a hit; every later one is.
        await tb.setup(mode=MODE_STATIC_OPEN, tr=0)
        await tb.issue(OP_ACT, 4, 0x77)
        await tb.issue(OP_RD, 4)
        chk(tb.row_hit(4) == 0,
            f"row_hit[4]={tb.row_hit(4)} after ACT+one column -- that column "
            f"is the activation's own access and inflates the hit rate")
        for i in range(1, 6):
            await tb.issue(OP_WR, 4)
            chk(tb.row_hit(4) == i,
                f"row_hit[4]={tb.row_hit(4)} after {i} further columns on the "
                f"open row, expected {i}")
        chk(all(tb.row_hit(b) == 0 for b in range(NUM_BANKS) if b != 4),
            "a column op to bank 4 credited another bank's hit counter")

    elif tt == "row_hit_survives_reactivation":
        # pumice ISSUE-014, measured on silicon as 49 ACTs for 48 column ops
        # and a NEGATIVE derived hit count. Open, close by timeout before any
        # column op, reopen, then one column: two ACTs, one column, and the
        # honest hit count is zero.
        await tb.setup(mode=MODE_FIXED_OPEN, tr=2)
        await tb.issue(OP_ACT, 6, 0x11)
        await tb.issue(OP_RD, 6)            # the first activation's access
        await tb.wait_timeout_req(bank=6)
        await tb.issue(OP_PRE, 6)
        await tb.issue(OP_ACT, 6, 0x12)     # reopen, different row
        await tb.issue(OP_RD, 6)            # the second activation's access
        chk(tb.row_hit(6) == 0,
            f"row_hit[6]={tb.row_hit(6)} across open/close/reopen with one "
            f"column op per activation -- neither column found a row someone "
            f"else opened")
        chk(tb.stat('stat_act_o') == 2 and tb.stat('stat_page_hit_o') == 2,
            f"act={tb.stat('stat_act_o')} col={tb.stat('stat_page_hit_o')}; "
            f"expected 2 and 2, which is exactly the shape that makes "
            f"`col_ops - ACT` an unusable hit estimate")

    elif tt == "miss_vs_empty_classification":
        # A wrong-row (conflict) PRE marks its bank: the reopen is a MISS. A
        # timeout close does not: the reopen is EMPTY. A virgin ACT is EMPTY.
        await tb.setup(mode=MODE_FIXED_OPEN, tr=3)
        await tb.issue(OP_ACT, 0, 0x10)      # virgin -> empty
        await tb.issue(OP_RD, 0)
        chk((tb.stat('stat_page_empty_o'), tb.stat('stat_page_miss_o')) == (1, 0),
            f"virgin ACT: empty={tb.stat('stat_page_empty_o')} "
            f"miss={tb.stat('stat_page_miss_o')}, expected 1 and 0")
        # Conflict close: PRE while the timer has NOT expired.
        await tb.issue(OP_PRE, 0)
        await tb.issue(OP_ACT, 0, 0x20)
        chk((tb.stat('stat_page_empty_o'), tb.stat('stat_page_miss_o')) == (1, 1),
            f"after a conflict PRE the reopen must be a MISS: "
            f"empty={tb.stat('stat_page_empty_o')} "
            f"miss={tb.stat('stat_page_miss_o')}, expected 1 and 1")
        # Timeout close: let the timer expire first, then PRE.
        await tb.issue(OP_RD, 0)
        await tb.wait_timeout_req(bank=0)
        await tb.issue(OP_PRE, 0)
        await tb.issue(OP_ACT, 0, 0x30)
        chk((tb.stat('stat_page_empty_o'), tb.stat('stat_page_miss_o')) == (2, 1),
            f"after a TIMEOUT close the reopen must be EMPTY, not a miss: "
            f"empty={tb.stat('stat_page_empty_o')} "
            f"miss={tb.stat('stat_page_miss_o')}, expected 2 and 1")

    elif tt == "prea_marks_no_bank":
        # FOUND HERE, then fixed in the RTL. The header says refresh closes do
        # not mark, but the mark was driven by w_is_pre, which includes PREA --
        # the refresh drain's all-bank close, whose bank field is not an
        # address. Measured: 1 miss + 7 empties for the eight reopens after one
        # PREA, so one arbitrary bank's reopen was booked as a conflict miss.
        # All eight belong to the page_empty class: nothing conflicted, a drain
        # closed them. The mark is now gated on a single-bank PRE.
        await tb.setup(mode=MODE_STATIC_OPEN, tr=0)
        for b in range(NUM_BANKS):
            await tb.issue(OP_ACT, b, 0x40 + b)
            await tb.issue(OP_RD, b)
        base_empty = tb.stat('stat_page_empty_o')
        chk(base_empty == NUM_BANKS,
            f"opening 8 virgin banks gave {base_empty} empties")
        await tb.issue(OP_PREA, 0)            # bank field is meaningless here
        for b in range(NUM_BANKS):
            await tb.issue(OP_ACT, b, 0x50 + b)
        miss = tb.stat('stat_page_miss_o')
        empty = tb.stat('stat_page_empty_o') - base_empty
        tb.log.info(f"after PREA + 8 reopens: miss={miss} empty={empty}")
        chk(miss + empty == NUM_BANKS,
            f"8 reopens classified as {miss} miss + {empty} empty -- every "
            f"ACT must land in exactly one class")
        chk(miss == 0 and empty == NUM_BANKS,
            f"after a PREA the eight reopens are {miss} miss + {empty} empty; "
            f"a drain conflicts with nothing, so every one of them is "
            f"page_empty. A miss here means the mark is being driven by PREA, "
            f"whose bank field is not an address -- it books one arbitrary "
            f"bank as a conflict and makes open-page look worse than it is.")
        # A single-bank PRE still marks: the fix must not disarm the real case.
        await tb.issue(OP_RD, 2)
        await tb.issue(OP_PRE, 2)
        await tb.issue(OP_ACT, 2, 0x60)
        chk(tb.stat('stat_page_miss_o') == 1,
            f"a single-bank conflict PRE followed by a reopen gave "
            f"{tb.stat('stat_page_miss_o')} misses, expected 1 -- narrowing "
            f"the mark to OP_PRE must not lose the conflict class itself")

    elif tt == "command_class_counters":
        # act / pre / ref are the denominators every efficiency number on the
        # board divides by. An op landing in two classes or none corrupts the
        # lot, so drive one of everything.
        await tb.setup(mode=MODE_STATIC_OPEN, tr=0)
        plan = [(OP_ACT, 0), (OP_RD, 0), (OP_WR, 0), (OP_RDA, 0), (OP_WRA, 0),
                (OP_PRE, 0), (OP_ACT, 1), (OP_PREA, 0),
                (OP_REF, 0), (OP_REFPB, 1), (OP_NOP, 0)]
        for op, b in plan:
            await tb.issue(op, b)
        chk(tb.stat('stat_act_o') == 2, f"act={tb.stat('stat_act_o')}, exp 2")
        chk(tb.stat('stat_pre_o') == 2,
            f"pre={tb.stat('stat_pre_o')}, exp 2 (PRE and PREA both count)")
        chk(tb.stat('stat_ref_o') == 2,
            f"ref={tb.stat('stat_ref_o')}, exp 2 (REF and REFPB both count)")
        chk(tb.stat('stat_page_hit_o') == 4,
            f"page_hit={tb.stat('stat_page_hit_o')}, exp 4 column ops "
            f"(RD, WR, RDA, WRA)")
        chk(tb.stat('stat_page_miss_o') + tb.stat('stat_page_empty_o')
            == tb.stat('stat_act_o'),
            f"miss+empty={tb.stat('stat_page_miss_o')}"
            f"+{tb.stat('stat_page_empty_o')} != act={tb.stat('stat_act_o')}")
        # A NOP must move nothing.
        before = tb.snapshot()
        await tb.issue(OP_NOP, 0)
        await tb.idle(3)
        chk(tb.snapshot() == before, "a NOP moved a counter")

    elif tt == "ref_busy_counts_only_with_demand":
        # TASK-012: the whole point is that this one is NOT free-running with
        # the host. A refresh while idle costs the workload nothing.
        await tb.setup(mode=MODE_STATIC_OPEN, tr=0, demand=0)
        for _ in range(4):
            await tb.issue(OP_REF, 0)
        chk(tb.stat('stat_ref_o') == 4 and tb.stat('stat_ref_busy_o') == 0,
            f"4 refreshes with demand low: ref={tb.stat('stat_ref_o')} "
            f"busy={tb.stat('stat_ref_busy_o')}, expected 4 and 0 -- counting "
            f"idle refreshes is what made the board number a 2584x "
            f"overstatement")
        dut.demand_i.value = 1
        await Timer(1, 'ns')
        for _ in range(3):
            await tb.issue(OP_REF, 0)
        chk(tb.stat('stat_ref_o') == 7 and tb.stat('stat_ref_busy_o') == 3,
            f"3 more refreshes with demand high: ref={tb.stat('stat_ref_o')} "
            f"busy={tb.stat('stat_ref_busy_o')}, expected 7 and 3")
        # Demand high but no refresh must not count either.
        await tb.idle(10)
        chk(tb.stat('stat_ref_busy_o') == 3,
            f"busy={tb.stat('stat_ref_busy_o')} after 10 idle cycles with "
            f"demand high -- it counts REFRESHES, not cycles")

    elif tt == "random_soak":
        # Invariants that hold for any legal command stream, checked against a
        # Python tally of the stimulus rather than a re-implementation of the
        # RTL's counters.
        rng = random.Random(int(os.environ.get('SEED', '29')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 150, "FUNC": 600, "FULL": 2500}.get(lvl, 600)
        await tb.setup(mode=MODE_FIXED_OPEN, tr=4, demand=0)
        n_act = n_pre = n_ref = n_col = n_refbusy = 0
        for _ in range(n):
            demand = rng.randint(0, 1)
            dut.demand_i.value = demand
            b = rng.randrange(NUM_BANKS)
            open_now = bool(tb.active & (1 << b))
            r = rng.random()
            if not open_now and r < 0.45:
                await tb.issue(OP_ACT, b, rng.randrange(1 << ROW_WIDTH))
                n_act += 1
            elif open_now and r < 0.6:
                await tb.issue(rng.choice((OP_RD, OP_WR)), b)
                n_col += 1
            elif open_now and r < 0.75:
                await tb.issue(OP_PRE, b)
                n_pre += 1
            elif r < 0.82:
                await tb.issue(OP_REF, 0)
                n_ref += 1
                n_refbusy += demand
            else:
                await tb.idle(1)
        await tb.idle(3)
        chk(tb.stat('stat_act_o') == n_act,
            f"act={tb.stat('stat_act_o')}, stimulus issued {n_act}")
        chk(tb.stat('stat_pre_o') == n_pre,
            f"pre={tb.stat('stat_pre_o')}, stimulus issued {n_pre}")
        chk(tb.stat('stat_ref_o') == n_ref,
            f"ref={tb.stat('stat_ref_o')}, stimulus issued {n_ref}")
        chk(tb.stat('stat_page_hit_o') == n_col,
            f"page_hit={tb.stat('stat_page_hit_o')}, stimulus issued {n_col} "
            f"column ops")
        chk(tb.stat('stat_ref_busy_o') == n_refbusy,
            f"ref_busy={tb.stat('stat_ref_busy_o')}, {n_refbusy} refreshes "
            f"were issued with demand high")
        chk(tb.stat('stat_page_miss_o') + tb.stat('stat_page_empty_o') == n_act,
            f"miss+empty={tb.stat('stat_page_miss_o')}"
            f"+{tb.stat('stat_page_empty_o')} != {n_act} activations")
        total_hits = sum(tb.row_hit(b) for b in range(NUM_BANKS))
        chk(total_hits <= n_col,
            f"row hits {total_hits} exceed the {n_col} column ops issued")
        chk(total_hits >= n_col - n_act,
            f"row hits {total_hits} below col-act = {n_col - n_act}; every "
            f"column op beyond one per activation found an open row")
        chk(n_act > n // 20,
            f"only {n_act} activations in {n} cycles -- the soak proved little")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('aclk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["mode_select_drives_ap", "timeout_expiry_is_exact",
         "row_hit_excludes_the_activations_own_column"]
_FUNC = _GATE + ["timeout_reloads_on_every_command", "timeout_disabled_states",
                 "timeout_holds_until_the_row_closes",
                 "timeout_picks_the_lowest_bank",
                 "act_alone_does_not_arm_the_timer",
                 "row_hit_survives_reactivation",
                 "miss_vs_empty_classification", "prea_marks_no_bank",
                 "command_class_counters", "ref_busy_counts_only_with_demand",
                 "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_page_policy(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_page_policy"
    test_name = f"test_scoria_page_policy_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_page_policy.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_page_policy",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
