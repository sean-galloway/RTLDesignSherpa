# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_cmd_arbiter` -- the DDR3 ZQ arm, first simulation.

andesite's arbiter is pumice's plus exactly four signals: `zq_req_i`,
`zq_grant_o`, `t_zqcs_i` and `stall_zq_o`. That arm was written and wired in
this tree and had never been simulated -- including the `STALL_ZQ` CSR, whose
counter was committed with no test behind it at all. Everything else in the
block is covered by pumice's suite, so this file goes deep on the ZQ arm and
takes the inherited paths as smoke.

Why the ZQ arm is worth its own file rather than a line in an integration test:
JESD79-3F 3.10 requires ALL BANKS IDLE before ZQCS and forbids EVERY command
for tZQCS afterwards. Both halves are structural in the arbiter -- a two-step
precharge-then-issue sequence that must NOT fall through to column traffic
while it waits (a fall-through lets columns reopen rows behind it and the
calibration never finds an all-idle moment), and a window during which the
whole arbiter idles including refresh. Get either half wrong and the DRAM's
output drivers are calibrated against a bus that is not quiet, which does not
fail in simulation at all: it shows up as marginal DQ on silicon.

The one inherited case kept here, `column_pick_smoke`, exists to prove the
testbench rather than the arbiter: it is the case that fails if the lookahead
twins are left undriven or the pick-pipeline depth is wrong, and both of those
mistakes make every other case in the file read as a broken arbiter.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_cmd_arbiter_tb import (  # noqa: E402
    AndesiteCmdArbiterTB, OP_ACT, OP_RD, OP_PRE, OP_REF, OP_MRS, OP_ZQCS,
    OP_NAMES,
)

NUM_BANKS = 8
ROW_WIDTH = 15
T_ZQCS = 16


async def wait_for(tb, pred, limit=80):
    """Step one edge at a time until pred() holds; return the cycle or None."""
    for i in range(limit):
        if pred():
            return i
        await tb.step()
    return None


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_andesite_cmd_arbiter(dut):
    tt = os.environ.get("TEST_TYPE", "zq_precharges_then_issues")
    tb = AndesiteCmdArbiterTB(dut)
    await tb.setup_clocks_and_reset()
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    def is_op(op):
        p = tb.picked()
        return p['valid'] == 1 and p['op'] == op

    if tt == "init_passthrough":
        # Inherited smoke, and the precondition for everything else: before
        # init_done the sequencer owns the bus verbatim.
        dut.init_done_i.value = 0
        dut.init_cmd_valid_i.value = 1
        dut.init_cmd_op_i.value = OP_MRS
        dut.init_cmd_bank_i.value = 2
        dut.init_cmd_row_i.value = 0x532
        await tb.settle(2)
        p = tb.picked()
        chk(p['valid'] == 1 and p['op'] == OP_MRS and p['bank'] == 2
            and p['row'] == 0x532,
            f"init passthrough gave {p}; the sequencer's MRS must reach the "
            f"wire unchanged (op 0x{OP_MRS:X}, bank 2, row 0x532)")
        dut.init_cmd_valid_i.value = 0
        dut.init_done_i.value = 1

    elif tt == "zq_precharges_then_issues":
        # JESD79-3F 3.10: all banks idle before ZQCS. With a row open the
        # arbiter must PRE first and only then calibrate.
        tb.all_banks_ready(True)
        tb.set_bank_bits(dut.bank_row_active_i, {3: 1})
        tb.set_open_rows({3: 0x1234})
        dut.zq_req_i.value = 1
        await tb.settle(2)
        i = await wait_for(tb, lambda: is_op(OP_PRE))
        chk(i is not None,
            f"zq_req with bank 3 open never produced a PRE (saw "
            f"{tb.op_name()}); ZQCS cannot issue against an open row")
        if i is not None:
            chk(tb.picked()['bank'] == 3,
                f"the ZQ precharge named bank {tb.picked()['bank']}, not the "
                f"open one (3)")
        # Model the bank timer closing the row, then the calibration must fire.
        tb.set_bank_bits(dut.bank_row_active_i, {})
        j = await wait_for(tb, lambda: is_op(OP_ZQCS))
        chk(j is not None,
            f"with every bank idle and zq_req high, no ZQCS issued (saw "
            f"{tb.op_name()}) -- andesite_zq_ctrl holds the request until it is "
            f"granted, so the calibration would never happen")
        if j is not None:
            chk(tb.strobes()['zq_grant'] == 1,
                "ZQCS issued without zq_grant_o -- andesite_zq_ctrl never learns "
                "its request was taken and re-requests forever")

    elif tt == "zq_window_blocks_all_commands":
        # The second half of 3.10: NO command for tZQCS after the ZQCS, not
        # even a refresh. The window is ~16 MC cycles against a tREFI of ~1950,
        # so refresh_ctrl's postpone credit absorbs at most one refresh --
        # which is why idling here is safe and falling through is not.
        tb.all_banks_ready(True)
        dut.zq_req_i.value = 1
        await tb.settle(2)
        # Wait for the FIRE (zq_grant), not for the command to be PRESENTED.
        # The window counter loads on the accepted fire, so a presented-but-
        # unaccepted ZQCS has not started it yet -- and changing an input in
        # that same cycle can re-steer the pick before it is taken. That is
        # not a hypothetical: driving refresh_req_i on the ZQCS's own cycle
        # replaced it with a REF and read as "a command issued inside the
        # window", which is this case's own failure message.
        j = await wait_for(tb, lambda: tb.strobes()['zq_grant'] == 1)
        chk(j is not None, f"no ZQCS fired with all banks idle "
                           f"(saw {tb.op_name()})")
        await tb.step()                      # the tZQCS window is loaded now
        dut.zq_req_i.value = 0
        # Pile on demand: a refresh AND a read candidate on an open row.
        dut.refresh_req_i.value = 1
        tb.set_entries('rd', {0: (1, 0x55, 4, 10)})
        tb.set_bank_bits(dut.bank_row_active_i, {1: 1})
        tb.set_open_rows({1: 0x55})
        seen = []
        for _ in range(T_ZQCS - 2):
            await tb.step()
            if tb.picked()['valid']:
                seen.append(OP_NAMES.get(tb.picked()['op'], '?'))
        chk(seen == [],
            f"commands issued inside the tZQCS window: {seen}. JESD79-3F 3.10 "
            f"forbids every command while the device calibrates -- the arm "
            f"must IDLE, not fall through to refresh or a column pick.")
        # ...and the window must end.
        k = await wait_for(tb, lambda: tb.picked()['valid'] == 1, limit=60)
        chk(k is not None,
            "the arbiter never resumed after tZQCS -- the window counter does "
            "not drain and the controller is wedged")

    elif tt == "demand_queued_before_zq_stays_out_of_the_window":
        # The SHADOW CYCLE that zq_window_blocks_all_commands cannot see.
        #
        # That case presents its demand one step AFTER the grant, by which time
        # the window counter has loaded and the pick cone's priority-2 block
        # catches everything. But the counter loads on the ACCEPTED FIRE, so
        # during the ZQCS's own fire cycle w_zq_busy is still 0 -- and the
        # arbiter picks that cycle too. A command already waiting when the
        # ZQCS goes is therefore picked in the shadow and fires one cycle
        # later, inside the window, because the final gate (w_out_safe) carries
        # no tZQCS term.
        #
        # This is not a contrived order. The arbiter precharges every bank to
        # issue a ZQCS, so traffic is NORMALLY queued behind one, and zq_req
        # outranks demand -- so "pending read, all banks idle, zq_req high" is
        # what the real controller looks like every time it calibrates.
        # Found by formal (formal/andesite/cmd_arbiter, a_zqcs_quiet), which also
        # covers c_act_in_zqcs and c_col_in_zqcs.
        tb.all_banks_ready(True)
        # Queue the demand FIRST, on a closed bank so it needs an ACT, and
        # leave every bank idle so the ZQCS's own precondition holds.
        tb.set_entries('rd', {0: (4, 0x10, 8, 10)})
        dut.zq_req_i.value = 1
        await tb.settle(2)
        j = await wait_for(tb, lambda: tb.strobes()['zq_grant'] == 1)
        chk(j is not None, f"no ZQCS fired with all banks idle and a queued "
                           f"read (saw {tb.op_name()})")
        # NO step() here -- stepping is what hides the bug. Sample from the
        # cycle after the grant, which is the first cycle of the window.
        seen = []
        for _ in range(T_ZQCS):
            await tb.step()
            if tb.picked()['valid']:
                seen.append((OP_NAMES.get(tb.picked()['op'], '?'),
                             tb.strobes()['zq_grant']))
        issued = [op for op, zq in seen if not zq]
        chk(issued == [],
            f"commands issued inside the tZQCS window: {issued}. JESD79-3F "
            f"3.10 forbids EVERY command while the device calibrates. The "
            f"command was picked in the ZQCS's own fire cycle, when the window "
            f"counter had not loaded yet, and w_out_safe does not re-validate "
            f"tZQCS at the fire -- the same shape as andesite BUG-001, where the "
            f"rank-global tRRD/tFAW windows were checked two stages early.")

    elif tt == "probe_zq_shadow_alignment":
        # Formal says a command CAN fire inside the tZQCS window (see
        # formal/andesite/cmd_arbiter, assertion a_zqcs_quiet, covers
        # c_act_in_zqcs / c_col_in_zqcs). The pick pipeline is 3-4 stages, so
        # reproducing it in simulation needs the demand to be in flight at the
        # moment the ZQCS fires -- one arbitrary alignment misses it. This
        # sweeps the offset at which the demand entry appears, relative to the
        # cycle zq_req is raised, and reports which offsets land a command in
        # the window. A probe, not a gate: it prints and does not fail.
        hits = []
        for off in range(10):
            await tb.assert_reset(); await tb.step(); await tb.deassert_reset()
            await tb.settle(2)
            tb.all_banks_ready(True)
            dut.zq_req_i.value = 1
            await tb.settle(2)
            placed = False
            seen = []
            for c in range(T_ZQCS + 12):
                if c == off:
                    tb.set_entries('rd', {0: (4, 0x10, 8, 10)}); placed = True
                await tb.step()
                zq = tb.strobes()['zq_grant']
                if zq:
                    win = T_ZQCS
                    for _ in range(win):
                        await tb.step()
                        if tb.picked()['valid'] and not tb.strobes()['zq_grant']:
                            seen.append(OP_NAMES.get(tb.picked()['op'], '?'))
                    break
            if seen:
                hits.append((off, seen))
            tb.set_entries('rd', {})
            dut.zq_req_i.value = 0
        tb.log.info(f"tZQCS shadow sweep: {len(hits)} of 10 offsets landed a "
                    f"command inside the window")
        for off, seen in hits:
            tb.log.info(f"  demand at offset {off}: {seen}")
        if not hits:
            tb.log.info("  no offset reproduced it in simulation; the formal "
                        "counterexample stands as the evidence, which is also "
                        "how pumice BUG-021 (same mechanism, same block) could "
                        "only ever be shown")

    elif tt == "refresh_outranks_zq":
        # Priority cone: 1 init, 2 the tZQCS window, 3 refresh, 4 ZQCS. A
        # refresh deferred behind a calibration is a data-retention risk; a
        # calibration deferred behind a refresh costs nothing.
        tb.all_banks_ready(True)
        dut.refresh_req_i.value = 1
        dut.zq_req_i.value = 1
        await tb.settle(2)
        i = await wait_for(tb, lambda: tb.picked()['valid'] == 1)
        chk(i is not None, "neither refresh nor ZQ produced a command")
        if i is not None:
            chk(tb.picked()['op'] == OP_REF,
                f"with both pending, the arbiter picked "
                f"{OP_NAMES.get(tb.picked()['op'], '?')}; refresh must win -- "
                f"retention over calibration")
            chk(tb.strobes()['grant'] == 1 and tb.strobes()['zq_grant'] == 0,
                f"grants {tb.strobes()} -- the refresh grant only")

    elif tt == "zq_waits_without_falling_through":
        # The subtle half. While the ZQ arm waits for banks to close it must
        # NOT let column traffic through: a column reopens a row behind it and
        # the all-idle moment never arrives. The arm is allowed to issue the
        # PREs it needs, and nothing else.
        tb.all_banks_ready(True)
        tb.set_bank_bits(dut.bank_row_active_i, {5: 1})
        tb.set_open_rows({5: 0x77})
        tb.set_entries('rd', {0: (5, 0x77, 8, 10)})      # a row HIT on bank 5
        dut.zq_req_i.value = 1
        await tb.settle(4)
        ops = []
        for _ in range(24):
            await tb.step()
            if tb.picked()['valid']:
                ops.append(OP_NAMES.get(tb.picked()['op'], '?'))
        chk(set(ops) <= {'PRE'},
            f"while the ZQ arm waited for bank 5 to close, the arbiter issued "
            f"{sorted(set(ops))}. Anything but PRE reopens or re-uses a row "
            f"and the calibration never sees an idle bus.")
        chk('PRE' in ops,
            "the ZQ arm issued nothing at all with an open bank and a "
            "precharge permitted -- it is waiting for something to close the "
            "row for it, and nothing will")

    elif tt == "stall_zq_counts_the_wait":
        # STALL_ZQ was committed with no test. Its contract (from the RTL):
        # charge a cycle whenever the tZQCS window is busy OR a request is
        # pending and unresolved. A counter stuck at zero makes the board's
        # attribution of lost cycles wrong in the worst way -- the time goes
        # somewhere and every other bucket looks innocent.
        tb.all_banks_ready(True)
        # QUIET FIRST, deliberately: no ZQ request has ever been made since
        # reset, so no window can exist and the measurement needs no
        # assumption about how long a window has left to run. Doing this
        # phase second instead read +2 and looked like a counter bug; it was
        # the tail of a tZQCS window the arm had legitimately started.
        quiet = tb.stalls()['stall_zq_o']
        for _ in range(12):
            await tb.step()
        chk(tb.stalls()['stall_zq_o'] == quiet,
            f"stall_zq advanced by {tb.stalls()['stall_zq_o'] - quiet} with no "
            f"ZQ request and no window since reset -- it would charge idle "
            f"time to calibration")
        # Now a request the arm CANNOT resolve: bank 2 open and precharge
        # refused for it, so no PRE can close it and the ZQCS can never issue.
        # (Leaving pre_ready set instead lets the arbiter precharge it and then
        # proceed on its OWN in-flight bookkeeping, regardless of what this
        # testbench still claims about bank_row_active -- which is how this
        # case first mis-measured.)
        tb.set_bank_bits(dut.bank_pre_ready_i,
                         {b: 1 for b in range(NUM_BANKS) if b != 2})
        tb.set_bank_bits(dut.bank_row_active_i, {2: 1})
        tb.set_open_rows({2: 0x9})
        dut.zq_req_i.value = 1
        await tb.settle(4)
        base = tb.stalls()['stall_zq_o']
        n = 12
        for _ in range(n):
            await tb.step()
        waited = tb.stalls()['stall_zq_o'] - base
        chk(waited >= n - 2,
            f"stall_zq advanced {waited} over {n} cycles of a pending, "
            f"unresolvable ZQ request -- those cycles must be charged to ZQ "
            f"or they are charged to nothing")
        chk(tb.picked()['valid'] == 0 or tb.picked()['op'] == OP_ZQCS,
            f"the arm issued {tb.op_name()} while it could not close bank 2")

    elif tt == "zq_grant_pulses_once":
        # andesite_zq_ctrl counts grants. A grant held for two cycles counts two
        # calibrations and moves the next interval; one missed leaves the
        # request asserted forever.
        tb.all_banks_ready(True)
        dut.zq_req_i.value = 1
        await tb.settle(2)
        j = await wait_for(tb, lambda: tb.strobes()['zq_grant'] == 1)
        chk(j is not None, "zq_grant never asserted with all banks idle")
        # wait_for returns IN the grant cycle without stepping, so counting
        # from here counts that cycle again -- the first version of this case
        # reported "high for 1 further cycle" against a grant that is exactly
        # one cycle wide. Step past it first.
        await tb.step()
        dut.zq_req_i.value = 0
        hi = 0
        for _ in range(T_ZQCS + 8):
            if tb.strobes()['zq_grant']:
                hi += 1
            await tb.step()
        chk(hi == 0,
            f"zq_grant was still high for {hi} further cycles after the ZQCS "
            f"fired -- andesite_zq_ctrl would count {hi + 1} calibrations for "
            f"one command")

    elif tt == "column_pick_smoke":
        # This case tests the TESTBENCH as much as the arbiter: it is the one
        # that fails when the lookahead twins are left undriven (the pick
        # pipeline samples the TWIN, not the live vector) or when the settle
        # depth is wrong. Both mistakes make every other case here look like a
        # broken arbiter, so it runs at GATE.
        tb.all_banks_ready(True)
        tb.set_bank_bits(dut.bank_row_active_i, {1: 1})
        tb.set_open_rows({1: 0x2A})
        tb.set_entries('rd', {0: (1, 0x2A, 0x10, 10)})
        await tb.settle(4)
        i = await wait_for(tb, lambda: is_op(OP_RD))
        chk(i is not None,
            f"a read candidate on an open, ready row never issued (saw "
            f"{tb.op_name()}). Before suspecting the arbiter: are the "
            f"bank_*_ready_la_i twins driven, and is the settle depth 4?")
        if i is not None:
            p = tb.picked()
            chk(p['bank'] == 1 and p['col'] == 0x10,
                f"the read issued as bank {p['bank']} col 0x{p['col']:X}, "
                f"expected bank 1 col 0x10")
            chk(tb.strobes()['rd_issue'] == 1,
                "the column issued without rd_issue_valid_o -- the read CAM "
                "never learns its entry went out")


    elif tt == "ls_same_group_waits_for_the_long_window":
        # ANDESITE L/S DELTA: with the short window (t_ccd_i=2) expired, a
        # column to the SAME bank group as the last column must still wait
        # for tccd_l_ok_i, while a cross-group column flows through the
        # short gate alone. NUM_BANKS=8, NUM_BG=4 -> group = bank[2:1].
        tb.all_banks_ready(True)
        dut.t_ccd_i.value = 2
        tb.set_bank_bits(dut.bank_row_active_i, {0: 1, 2: 1, 3: 1})
        tb.set_open_rows({2: 0x11, 3: 0x22, 0: 0x33})
        tb.set_entries('rd', {0: (2, 0x11, 0x10, 10), 1: (3, 0x22, 0x20, 8)})
        await tb.settle(4)
        i = await wait_for(tb, lambda: is_op(OP_RD))
        chk(i is not None, "first column (bank 2, group 1) never issued")
        p = tb.picked()
        chk(p['bank'] == 2, f"first column went to bank {p['bank']}, expected 2")
        # The mock CAM does not consume entries; clear the fired one so only
        # the same-group candidate (bank 3) remains.
        tb.set_entries('rd', {1: (3, 0x22, 0x20, 8)})
        await tb.settle(4)
        # First column fired on group 1. Shut the long window: the pending
        # same-group candidate (bank 3, group 1) must not issue even after
        # the short window expires.
        dut.tccd_l_ok_i.value = 0
        saw = 0
        for _ in range(20):
            await tb.step()
            if is_op(OP_RD):
                saw += 1
        chk(saw == 0,
            f"{saw} same-group columns issued while tccd_l_ok_i was low -- "
            f"the L gate leaked across the short window")
        dut.tccd_l_ok_i.value = 1
        i = await wait_for(tb, lambda: is_op(OP_RD), limit=40)
        chk(i is not None, "same-group column never issued after the long window opened")
        p = tb.picked()
        chk(p['bank'] == 3, f"the second column went to bank {p['bank']}, expected 3")
        # Cross-group: a column to bank 0 (group 0) flows on the short gate
        # alone even with the long window shut.
        dut.tccd_l_ok_i.value = 0
        tb.set_entries('rd', {2: (0, 0x33, 0x30, 6)})
        await tb.settle(4)
        i = await wait_for(tb, lambda: is_op(OP_RD), limit=40)
        chk(i is not None,
            "cross-group column blocked with the long window shut -- the L gate must not leak across groups")
        p = tb.picked()
        chk(p['bank'] == 0, f"cross-group column went to bank {p['bank']}, expected 0")

    elif tt == "act_waits_for_the_act_limit":
        # tFAW/tRRD are re-applied LIVE at the issue point (the fix for the
        # class pumice BUG-021 is in: a stale classify-time gate let ACTs out
        # inside the window). With the limit shut, no ACT may issue however
        # ready the bank is.
        tb.all_banks_ready(True)
        tb.set_entries('rd', {0: (4, 0x33, 0x20, 10)})   # needs an ACT first
        dut.trrd_ok_i.value = 0
        await tb.settle(4)
        acts = 0
        for _ in range(24):
            await tb.step()
            if is_op(OP_ACT):
                acts += 1
        chk(acts == 0,
            f"{acts} ACTs issued with trrd_ok_i low -- the live re-validation "
            f"at the issue point is what stops a classify-time gate going "
            f"stale across the pick pipeline (pumice BUG-021's class)")
        dut.trrd_ok_i.value = 1
        i = await wait_for(tb, lambda: is_op(OP_ACT), limit=40)
        chk(i is not None,
            f"no ACT after trrd_ok_i released (saw {tb.op_name()}) -- the gate "
            f"must re-arm, not latch")

    elif tt == "grants_wait_for_the_accepted_fire":
        # Written because a MUTATION escaped: replacing
        # `zq_grant_o = w_fire_out && r_zq_grant` with the bare registered
        # decision passed all ten cases. With the sink always ready those are
        # the same cycle, so a suite that never stalls the sink cannot tell
        # them apart -- and under backpressure they are not the same at all.
        # The ungated version asserts the grant for EVERY stalled cycle, so
        # andesite_zq_ctrl counts calibrations that never reached the DRAM and
        # moves its interval on each one. refresh_grant_o has the identical
        # shape and the identical consequence for the refresh credit.
        tb.all_banks_ready(True)
        tb.set_cmd_ready(False)
        dut.zq_req_i.value = 1
        await tb.settle(2)
        i = await wait_for(tb, lambda: is_op(OP_ZQCS))
        chk(i is not None,
            f"no ZQCS was presented with the sink stalled (saw "
            f"{tb.op_name()}) -- the pick must be held, not dropped")
        held = 0
        for k in range(10):
            if tb.strobes()['zq_grant']:
                held += 1
            await tb.step()
        chk(held == 0,
            f"zq_grant asserted on {held} of 10 cycles while the command sink "
            f"refused the ZQCS. The grant must follow the ACCEPTED fire: "
            f"andesite_zq_ctrl treats each one as a completed calibration.")
        tb.set_cmd_ready(True)
        j = await wait_for(tb, lambda: tb.strobes()['zq_grant'] == 1, limit=20)
        chk(j is not None, "zq_grant never came after the sink resumed")

        # Same claim for the refresh grant, from a clean start.
        await tb.setup_clocks_and_reset()
        tb.all_banks_ready(True)
        tb.set_cmd_ready(False)
        dut.refresh_req_i.value = 1
        await tb.settle(2)
        i = await wait_for(tb, lambda: is_op(OP_REF))
        chk(i is not None,
            f"no REF was presented with the sink stalled (saw {tb.op_name()})")
        held = 0
        for k in range(10):
            if tb.strobes()['grant']:
                held += 1
            await tb.step()
        chk(held == 0,
            f"refresh_grant asserted on {held} of 10 stalled cycles -- "
            f"andesite_refresh_ctrl would retire a refresh the DRAM never got")
        tb.set_cmd_ready(True)
        j = await wait_for(tb, lambda: tb.strobes()['grant'] == 1, limit=20)
        chk(j is not None, "refresh_grant never came after the sink resumed")

    elif tt == "cmd_backpressure_holds_the_pick":
        # A stalled sink must not lose a command: with ready low the pick is
        # presented and held, and no side effects fire until it is accepted.
        tb.all_banks_ready(True)
        tb.set_bank_bits(dut.bank_row_active_i, {1: 1})
        tb.set_open_rows({1: 0x2A})
        tb.set_entries('rd', {0: (1, 0x2A, 0x10, 10)})
        tb.set_cmd_ready(False)
        await tb.settle(4)
        i = await wait_for(tb, lambda: tb.picked()['valid'] == 1)
        chk(i is not None, "nothing was presented with the sink stalled")
        held = tb.picked()
        for k in range(10):
            chk(tb.picked() == held,
                f"the presented command changed at stall cycle {k}: "
                f"{tb.picked()} vs {held} -- a pick must hold until accepted")
            chk(tb.strobes()['rd_issue'] == 0,
                f"rd_issue fired at stall cycle {k} for a command the sink has "
                f"not taken -- the CAM would free an entry whose command never "
                f"went out")
            await tb.step()
        tb.set_cmd_ready(True)
        j = await wait_for(tb, lambda: tb.strobes()['rd_issue'] == 1, limit=20)
        chk(j is not None,
            "rd_issue never fired after the sink resumed")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('aclk', 4)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["column_pick_smoke", "zq_precharges_then_issues",
         "zq_window_blocks_all_commands"]
_FUNC = _GATE + ["init_passthrough", "refresh_outranks_zq",
                 "zq_waits_without_falling_through",
                 "stall_zq_counts_the_wait", "zq_grant_pulses_once",
                 "act_waits_for_the_act_limit", "ls_same_group_waits_for_the_long_window",
                 "grants_wait_for_the_accepted_fire",
                 "cmd_backpressure_holds_the_pick",
                 "demand_queued_before_zq_stays_out_of_the_window",
                 "probe_zq_shadow_alignment"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_cmd_arbiter(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_cmd_arbiter"
    test_name = f"test_andesite_cmd_arbiter_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_cmd_arbiter.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_cmd_arbiter",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "NUM_BANKS": str(NUM_BANKS), "ROW_WIDTH": str(ROW_WIDTH),
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
