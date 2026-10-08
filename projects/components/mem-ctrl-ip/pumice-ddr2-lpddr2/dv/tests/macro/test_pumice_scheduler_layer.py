# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B macro runner for `pumice_scheduler_layer`."""

import os
import sys
import random

import cocotb
from cocotb.triggers import RisingEdge, Timer
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_dram_configs import dram_config  # noqa: E402
_CTRL_T = dram_config()[1]      # the operating point this suite runs
from tbclasses.pumice_scheduler_layer_tb import (  # noqa: E402
    PumiceMemCmdSchedulerTB, OP_ACT, OP_RD, OP_WR, OP_PRE, OP_REF, OP_MRS,
)
from tbclasses.pumice_levels import depth as _profile_depth  # noqa: E402

_FILELIST = ("projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/"
             "rtl/filelists/macro/pumice_scheduler_layer.f")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_refresh_vs_inflight_read(dut):
    """pumice BUG-014 (was PUMICE-037) at the scheduler layer: refresh landing on an in-flight read.

    On the board, a refresh arriving while reads are outstanding corrupts them:
    the ILA shows RD(bank4) -> PRE(bank4) -> REF -> ACT(bank4) with the read
    checker's mismatch asserted continuously across the whole window, and 59% of
    the bad beats read as all-ones (an undriven DQ bus). Nothing in the char sim
    or at pumice_top reproduces it, because both hand the controller a DFI slave
    that always returns correct data -- no model there can be wrong.

    This layer CAN speak to it, because the question is about COMMAND SPACING,
    which is what this block decides. JEDEC says a PRE may not follow a READ to
    the same bank until the burst has been driven out:

        PRE >= AL + BL/2 + max(tRTP, 2) - 2   (DDR2, in DRAM clocks)

    and REF may not follow PRE until tRP. If the refresh path issues either
    early, the DRAM stops driving mid-burst and the beats already in the PHY
    pipeline are garbage -- exactly the observed signature.

    Asserted here against the timings the TB programs, so a violation names the
    offending pair and the shortfall rather than showing up as a wrong byte on a
    board three layers up.
    """
    tb = PumiceMemCmdSchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.complete_init(), "init_done never asserted"
    tb.cmds.clear()

    t_rtp = int(dut.t_rtp_i.value)
    t_rp  = int(dut.t_rp_i.value)

    # A read pending on a bank, then force refresh to come due immediately, so
    # the refresh path has to precharge a bank that just took a column command.
    BANK, ROW = 4, 0x21
    tb.rd_entry = {'bank': BANK, 'row': ROW, 'col': 0x10,
                   'id': 0x3, 'age': 5, 'slot': 2}
    # t_refi is LOADED at init (0x800), so shortening it does not take effect
    # until that first interval expires -- allow for it rather than concluding
    # "no refresh" after 400 cycles, which is what this test did first time.
    dut.t_refi_i.value = 0x0010
    for _ in range(3000):
        await tb.wait_clocks('aclk', 1)
        if tb.ops_of(OP_REF):
            break

    seq = [(i, c) for i, c in enumerate(tb.cmds)]
    rds = [(i, c) for i, c in seq if c['op'] == OP_RD and c['bank'] == BANK]
    pres = [(i, c) for i, c in seq if c['op'] == OP_PRE]
    refs = [(i, c) for i, c in seq if c['op'] == OP_REF]
    assert refs, "no REF issued -- the refresh path never fired, test proves nothing"
    assert rds, "no RD issued to the bank -- nothing was in flight, test proves nothing"

    # cmds carry their issue cycle; fall back to index order if not stamped.
    def at(c, i):
        # No silent fallback to the list INDEX. That fallback is what made the
        # first version of this test report "PRE 1 cycle after RD" when it had
        # actually measured "PRE is the next COMMAND after RD" -- a false
        # positive that nearly drove an RTL change.
        assert 'cycle' in c, ("command stream carries no cycle stamp; spacing "
                              "cannot be checked (see _cmd_sink)")
        return c['cycle']

    ref_i, ref_c = refs[0]
    last_rd = max((x for x in rds if x[0] < ref_i), default=None, key=lambda x: x[0])
    assert last_rd is not None, "REF issued before any RD -- no collision window"
    pre_after = [x for x in pres if last_rd[0] < x[0] <= ref_i
                 and x[1]['bank'] == BANK]

    if pre_after:
        pre_i, pre_c = pre_after[0]
        d_rd_pre = at(pre_c, pre_i) - at(last_rd[1], last_rd[0])
        assert d_rd_pre >= t_rtp, (
            f"pumice BUG-014 (was PUMICE-037): PRE(bank {BANK}) issued {d_rd_pre} cycles after RD to "
            f"the same bank, tRTP={t_rtp}. The DRAM is precharged while its read "
            f"burst is still being driven out.")
        d_pre_ref = at(ref_c, ref_i) - at(pre_c, pre_i)
        assert d_pre_ref >= t_rp, (
            f"pumice BUG-014 (was PUMICE-037): REF issued {d_pre_ref} cycles after PRE, tRP={t_rp}.")

    tb.log.info(
        f"refresh vs in-flight read: {len(rds)} RD, {len(pres)} PRE, "
        f"{len(refs)} REF; spacing respects tRTP={t_rtp} tRP={t_rp}")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_scheduler_layer(dut):
    tb = PumiceMemCmdSchedulerTB(dut)
    await tb.setup_clocks_and_reset()

    # ===== 1. INIT: MRS stream forwarded; init completes =====
    done = await tb.complete_init()
    assert done, "init_done never asserted"
    mrs = tb.ops_of(OP_MRS)
    assert len(mrs) >= 4, f"expected the JEDEC MRS stream, saw {len(mrs)} MRS commands"
    tb.cmds.clear()

    # ===== 2. Pending READ to an unopened bank -> ACT then RD (real timers) =====
    tb.rd_entry = {'bank': 5, 'row': 0x123, 'col': 0x40, 'id': 0xA, 'age': 10, 'slot': 3}
    # let the scheduler run
    for _ in range(60):
        await tb.wait_clocks('aclk', 1)
        if tb.rd_issued:
            break
    await tb.wait_clocks('aclk', 12)  # drain the cmd FIFO to tb.cmds (CMD_DELAY=6 release + FIFO hop)

    acts = [c for c in tb.cmds if c['op'] == OP_ACT and c['bank'] == 5]
    rds  = [c for c in tb.cmds if c['op'] == OP_RD and c['bank'] == 5]
    assert acts, f"no ACT to bank5 issued; cmds={tb.cmds}"
    assert acts[0]['row'] == 0x123, f"ACT row {acts[0]['row']:#x} != 0x123"
    assert rds, f"no RD to bank5 issued; cmds={tb.cmds}"
    assert rds[0]['col'] == 0x40, f"RD col {rds[0]['col']:#x} != 0x40"
    assert tb.rd_issued == [3], f"rd_issue slot {tb.rd_issued} != [3]"

    # ACT must precede RD (order in the captured stream)
    act_idx = tb.cmds.index(acts[0])
    rd_idx  = tb.cmds.index(rds[0])
    assert act_idx < rd_idx, "ACT did not precede RD"

    # tRCD spacing: at least t_rcd cycles of non-RD between ACT and RD
    # (the RD can't be adjacent to ACT). Count captured commands is coarse;
    # assert there is no RD in the same or immediately-next slot by index gap.
    assert rd_idx > act_idx, "RD must come after ACT (tRCD gating)"

    tb.log.info(f"WRITE-path skipped (read tested). cmds after read: "
                f"{len(tb.ops_of(OP_ACT))} ACT, {len(tb.ops_of(OP_RD))} RD")

    # ===== 3. Pending WRITE (open row now on bank5) -> WR, commit =====
    tb.cmds.clear()
    tb.wr_entry = {'bank': 5, 'row': 0x123, 'col': 0x80, 'id': 0xB, 'age': 20, 'slot': 6}
    for _ in range(60):
        await tb.wait_clocks('aclk', 1)
        if tb.wr_committed:
            break
    await tb.wait_clocks('aclk', 12)  # drain the cmd FIFO to tb.cmds (CMD_DELAY=6 release + FIFO hop)
    wrs = [c for c in tb.cmds if c['op'] == OP_WR and c['bank'] == 5]
    assert wrs, f"no WR to bank5 (row already open); cmds={tb.cmds}"
    assert wrs[0]['col'] == 0x80, f"WR col {wrs[0]['col']:#x} != 0x80"
    assert tb.wr_committed == [6], f"wr_commit slot {tb.wr_committed} != [6]"
    # row was already open -> no new ACT needed
    assert not [c for c in tb.cmds if c['op'] == OP_ACT], \
        "unexpected ACT — bank5 row was already open (open-page row hit)"

    # ===== 4. REFRESH: eventually a REF appears (bank5 gets PRE first) =====
    # bank5 is still open from the WR. The tREFI counter drains from its initial
    # 0x800 load, so allow enough cycles to reach the first mandatory refresh.
    tb.cmds.clear()
    tb.dut.t_refi_i.value = 0x0010
    saw_ref = False
    saw_pre = False
    for _ in range(3000):
        await tb.wait_clocks('aclk', 1)
        if tb.ops_of(OP_PRE):
            saw_pre = True
        if tb.ops_of(OP_REF):
            saw_ref = True
            break
    assert saw_pre, "expected a PRE to close the open bank before refresh"
    assert saw_ref, "refresh never produced a REF command"

    # ===== 5. Refresh-collision + tRFC audit under sustained traffic =====
    # Heavy-but-liveable refresh pressure: at tREFI=0x40 a refresh cycle
    # (drain-PRE + guard + REF + tRFC=8) costs ~14 of every 64 cycles, so reads
    # keep flowing while REFs recur constantly. (0x10 would starve: refresh_req
    # never deasserts and priority-2 rightly blocks all other traffic.) The
    # BOUND pumice_cmd_history_checker $fatal-s on: a REFab issued with any row
    # open (bug #2 — ACT then REF with no PRE) and an ACT within tRFC=8 of a
    # REFab (mission-mode refresh recovery, previously enforced by nothing).
    tb.dut.t_refi_i.value = 0x40
    tb.cmds.clear()
    issued = 0
    # Reads under refresh pressure: pure repetition, and the exact RD count
    # below scales with it. The floor stays at 40 at gate and func because the
    # `refs >= 3` / `acts >= 10` floors are sized against that many reads at
    # tREFI=0x40; only full grows.
    n_reads = _profile_depth('sched_refresh_reads')
    n_pairs = _profile_depth('sched_mixed_pairs')
    # The wrapper reads TEST_LEVEL itself, beside its knob: bin/review/check_test_levels.py
    # follows only TBClasses/projects imports, and this area imports tbclasses.* (a
    # hyphenated component path cannot be a package import), so a read hidden inside
    # pumice_levels.depth() would be invisible to the gate. Forced, not chosen (BUG-004).
    tb.log.info("depth: TEST_LEVEL=%s sched_refresh_reads=%d sched_mixed_pairs=%d",
                os.environ.get("TEST_LEVEL", "gate"), n_reads, n_pairs)
    for i in range(n_reads):
        tb.rd_entry = {'bank': i % 8, 'row': 0x100 + i, 'col': 0x10,
                       'id': i & 0xF, 'age': i, 'slot': i % 8}
        for _ in range(400):
            await tb.wait_clocks('aclk', 1)
            if tb.rd_entry is None:
                issued += 1
                break
        assert tb.rd_entry is None, f"read {i} never issued (starved by refresh?)"
    await tb.wait_clocks('aclk', 8)   # drain the cmd FIFO before exact counts
    refs = len(tb.ops_of(OP_REF))
    acts = len(tb.ops_of(OP_ACT))
    assert refs >= 3, f"phase-5 expected recurring REFs, saw {refs}"
    # exactly one RD column per injected entry (1:1); ACT/REF counts vary
    # with refresh interleave so stay bounded-below.
    assert len(tb.ops_of(OP_RD)) == n_reads, \
        f"phase-5 expected exactly {n_reads} RD columns, saw {len(tb.ops_of(OP_RD))}"
    assert acts >= 10, f"phase-5 expected recurring ACTs, saw {acts}"
    tb.log.info(f"phase 5: {issued} reads under refresh pressure "
                f"({refs} REF, {acts} ACT) with the history checker armed")

    # ===== 6. CONCURRENT mixed wr+rd traffic (the DQ-turnaround audit) =====
    # Both entry mocks pending at once -> the arbiter alternates RD/WR columns
    # at its minimum spacing. The bound checker's GLOBAL tWTR/tRTW windows
    # (T_WTR/T_RTW = 2, matching t_wtr_i/t_rtw_i) $fatal on any direction-
    # crossing column issued into the opposite burst's DQ occupancy — the
    # flopped-ok staleness bug (issue #42: 471/471 dirty concurrent soak
    # rounds on silicon; zero sim coverage before this phase because every
    # flow was phase-separated).
    tb.dut.t_refi_i.value = 0x0800          # calm refresh for this phase
    tb.cmds.clear()
    mixed = 0
    for i in range(n_pairs):                 # concurrent pairs: pure repetition
        tb.wr_entry = {'bank': (2 * i) % 8, 'row': 0x200 + i, 'col': 0x20,
                       'id': i & 0xF, 'age': i, 'slot': i % 8}
        tb.rd_entry = {'bank': (2 * i + 1) % 8, 'row': 0x300 + i, 'col': 0x30,
                       'id': (i + 1) & 0xF, 'age': i, 'slot': (i + 3) % 8}
        for _ in range(400):
            await tb.wait_clocks('aclk', 1)
            if tb.wr_entry is None and tb.rd_entry is None:
                mixed += 1
                break
        assert tb.wr_entry is None and tb.rd_entry is None,             f"mixed pair {i} never fully issued"
    await tb.wait_clocks('aclk', 8)   # drain the cmd FIFO before counting
    rds = len(tb.ops_of(OP_RD))
    wrs = len(tb.ops_of(OP_WR))
    # 1:1 accounting: each injected entry issues EXACTLY once — too many
    # columns (re-issue/duplicate) is as much an error as too few.
    assert rds == n_pairs and wrs == n_pairs, \
        f"expected exactly {n_pairs}/{n_pairs} mixed columns, {rds}/{wrs}"
    tb.log.info(f"phase 6: {mixed} concurrent wr+rd pairs "
                f"({rds} RD, {wrs} WR) under the global tWTR/tRTW audit")

    tb.log.info("PASS: init MRS stream, ACT->RD (real tRCD timers), open-page WR "
                "commit (no re-ACT), refresh PRE->REF, refresh-pressure audit, "
                "concurrent-turnaround audit")


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_refresh_vs_read_stream(dut):
    """pumice BUG-014 (was PUMICE-037): a SUSTAINED read stream across a refresh.

    The first attempt at this had ONE read outstanding, which is not the board's
    state at all -- there a queue of reads is in flight when the refresh lands,
    and the failing beats read all-ones (an undriven DQ bus), the signature of a
    column issued to a row that is not open.

    So this streams reads to one bank continuously by re-arming the mock CAM as
    each issues, forces a refresh into the middle of it, and checks the
    invariant the board violates: EVERY column command must land on a bank whose
    row is currently open, with the right row. Row state is modelled from the
    command stream itself -- ACT opens, PRE closes that bank, REF closes all
    (DDR2 REFab requires every bank precharged), auto-precharge closes on the
    column.

    tRTP/tRP spacing is NOT re-checked here; the companion test covers it and
    found it correct.
    """
    tb = PumiceMemCmdSchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.complete_init(), "init_done never asserted"
    tb.cmds.clear()

    BANK, ROW = 4, 0x55
    dut.t_refi_i.value = 0x0010          # takes effect after the 0x800 load

    # Keep a read pending at all times: re-arm the instant the previous issues,
    # so the scheduler always has a column it wants and the refresh has to cut
    # into a live stream.
    col = 0
    tb.rd_entry = {'bank': BANK, 'row': ROW, 'col': col, 'id': 1, 'age': 1, 'slot': 2}
    for _ in range(4000):
        await tb.wait_clocks('aclk', 1)
        if tb.rd_entry is None:          # retired by _track_commit_issue
            col = (col + 1) & 0x3FF
            tb.rd_entry = {'bank': BANK, 'row': ROW, 'col': col,
                           'id': 1, 'age': 1, 'slot': 2}
        if len(tb.ops_of(OP_REF)) >= 2:  # refresh has cut in, twice
            break

    refs = tb.ops_of(OP_REF)
    cols = [c for c in tb.cmds if c['op'] in (OP_RD, OP_WR)]
    assert refs, "no REF issued -- the refresh never cut into the stream"
    assert len(cols) >= 20, (
        f"only {len(cols)} column commands -- the stream was not sustained, "
        f"so a refresh never landed mid-flight and this proves nothing")

    # Model row state from the command stream and find any column on a closed
    # or wrong row. That is the board's all-ones beat, expressed as commands.
    open_row = {}
    bad = []
    for c in tb.cmds:
        op, bk = c['op'], c['bank']
        if op == OP_ACT:
            open_row[bk] = c['row']
        elif op == OP_PRE:
            open_row.pop(bk, None)
        elif op == OP_REF:
            open_row.clear()             # REFab: all banks precharged
        elif op in (OP_RD, OP_WR):
            # Only the "is a row open" half is checkable from the stream: a
            # DDR2 column command carries the COLUMN, so cmd_row_o reads 0 on
            # RD/WR and comparing it against the open row flags every column
            # (408 of 408 on the first run -- a broken model, not a finding).
            if bk not in open_row:
                bad.append((c['cycle'], op, bk, 'no open row'))
            if c['ap']:
                open_row.pop(bk, None)

    assert not bad, (
        f"pumice BUG-014 (was PUMICE-037): {len(bad)} column command(s) issued to a bank with no open "
        f"row, across {len(refs)} refresh(es) and {len(cols)} columns. "
        f"First: cycle {bad[0][0]} op={bad[0][1]} bank={bad[0][2]} ({bad[0][3]}). "
        f"A read to a closed row returns undriven DQ -- the board's all-ones.")

    tb.log.info(f"read stream across refresh: {len(cols)} columns, {len(refs)} REF, "
                f"every column on an open row")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_pumice_scheduler_layer_refresh_read_stream(request, test_level):
    """pumice BUG-014 (was PUMICE-037): sustained read stream across a refresh."""
    _run_scheduler(request, "cocotb_test_refresh_vs_read_stream", test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_pumice_scheduler_layer_refresh_inflight_read(request, test_level):
    """Refresh vs an in-flight read: JEDEC spacing holds. PASSES.

    Written to reproduce pumice BUG-014 (was PUMICE-037) and it does NOT: the refresh path respects
    tRTP from the last same-bank column and tRP into the REF. Kept as a
    regression guard on that property, and as the record that the
    scheduler's command spacing is NOT the mechanism.
    """
    _run_scheduler(request, "cocotb_test_refresh_vs_inflight_read", test_level=test_level)


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_training_priority_and_gate(dut):
    """Training-layer arbiter priority and cal_busy gating.

    The training channel (ZQ / lp_cal) sits between refresh and demand in the
    arbiter: it can preempt demand traffic but must wait for an in-flight
    refresh to finish. A raised cal_busy_i blocks demand-class column commands
    and ACT to any bank so the post-calibration quiet window is honoured.
    """
    tb = PumiceMemCmdSchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.complete_init(), "init_done never asserted"

    # Drain the init MRS stream so a later check for an MRS command does not
    # accidentally capture a leftover init MRS from the output FIFO.
    for _ in range(100):
        await tb.wait_clocks('aclk', 1)
        if not int(dut.busy_o.value):
            break

    tb.cmds.clear()

    # Drive a training MRS request (e.g. MRW/MRR maintenance command).
    dut.trn_cmd_req_i.value = 1
    dut.trn_cmd_op_i.value = OP_MRS
    dut.trn_cmd_bank_i.value = 0
    dut.trn_cmd_row_i.value = (10 << 8) | 0x56   # MR10 ZQCS opcode
    dut.trn_cmd_mrr_i.value = 0
    dut.cal_busy_i.value = 0

    # Wait for the training command to be granted and observed at cmd output.
    for _ in range(40):
        await tb.wait_clocks('aclk', 1)
        if int(dut.trn_cmd_grant_o.value):
            break
    assert int(dut.trn_cmd_grant_o.value), "training request was never granted"

    # Discard any commands that were already in the output FIFO so we only see
    # the granted training command emerge.
    tb.cmds.clear()

    # Wait until it emerges from the cmd FIFO.
    for _ in range(40):
        await tb.wait_clocks('aclk', 1)
        if tb.cmds and tb.cmds[-1]['op'] == OP_MRS:
            break
    mrs = tb.ops_of(OP_MRS)
    assert mrs, "training MRS never reached cmd output"
    assert mrs[-1]['bank'] == 0
    assert int(dut.cmd_mrr_o.value) == 0, "cmd_mrr_o should follow trn_cmd_mrr_i"

    # Drop the request and wait for the output FIFO to drain so the MRR is not
    # confused with the previous MRS still in flight.
    dut.trn_cmd_req_i.value = 0
    for _ in range(100):
        await tb.wait_clocks('aclk', 1)
        if not int(dut.busy_o.value):
            break

    # Prepare the MRR fields one cycle before asserting the request so the
    # arbiter samples trn_cmd_mrr_i == 1 on the grant cycle.
    dut.trn_cmd_mrr_i.value = 1
    dut.trn_cmd_row_i.value = (32 << 8) | 0x00   # MR32 MRR
    await tb.wait_clocks('aclk', 1)

    # Drive an MRR training command while still idle and check cmd_mrr_o.
    dut.trn_cmd_req_i.value = 1
    for _ in range(40):
        await tb.wait_clocks('aclk', 1)
        if int(dut.trn_cmd_grant_o.value):
            break
    assert int(dut.trn_cmd_grant_o.value), "MRR training request was never granted"

    # Discard any earlier FIFO contents so the next MRS is the MRR we just drove.
    tb.cmds.clear()

    for _ in range(40):
        await tb.wait_clocks('aclk', 1)
        if tb.cmds and tb.cmds[-1]['op'] == OP_MRS:
            break
    mrs = tb.ops_of(OP_MRS)
    assert mrs, "MRR training command did not reach cmd output"
    assert int(dut.cmd_mrr_o.value) == 1, "cmd_mrr_o must be 1 for MRR"

    # Now raise cal_busy_i and present a demand read. It must not issue while
    # calibration holds the bus quiet.
    tb.cmds.clear()
    dut.cal_busy_i.value = 1
    dut.trn_cmd_req_i.value = 0
    tb.rd_entry = {'bank': 3, 'row': 0x123, 'col': 0x40,
                   'id': 0x1, 'age': 5, 'slot': 1}
    for _ in range(60):
        await tb.wait_clocks('aclk', 1)
    rds = tb.ops_of(OP_RD)
    acts = tb.ops_of(OP_ACT)
    assert len(rds) == 0 and len(acts) == 0, \
        f"demand traffic issued while cal_busy_i high (RD={len(rds)} ACT={len(acts)})"

    # Drop cal_busy_i; the pending read should now flow.
    dut.cal_busy_i.value = 0
    for _ in range(80):
        await tb.wait_clocks('aclk', 1)
        if tb.rd_issued:
            break
    assert tb.rd_issued, "pending read never issued after cal_busy_i dropped"
    tb.log.info("PASS: training priority, cal_busy gating, and cmd_mrr forwarding")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_pumice_scheduler_layer(request, test_level):
    _run_scheduler(request, "cocotb_test_pumice_scheduler_layer", test_level=test_level)



@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_timeout_pre_vs_pending_column(dut):
    """pumice BUG-003 at the MACRO level: does a column op ever issue to a bank
    the scheduler has just precharged?

    WHY HERE. At the core level the illegal command is observable at
    `cmd_valid_o && cmd_ready_i` and on the DFI pins, but the pick guards are
    timed to the arbiter's INTERNAL fire and the observable sits downstream of a
    FIFO -- the offending PRE sat valid-but-not-ready for 3 cycles, so push and
    pop times diverge and guard state cannot be aligned to the bad command. This
    macro drives the scheduler directly: no AXI front end, no CAMs, no cmd FIFO
    hop beyond CMD_DELAY, no DFI layer.

    THE CONFIG IS THE ONE THAT FAILS ON THE BOARD PATH: open page with the
    background timeout enabled (`page_mode_i=3`, `page_tr_init_i=2`). Baselines
    matter as much as the failing arm -- open page with the timeout OFF, and
    close page, are both clean at the core level, so this test drives all three
    and only the timeout arm is expected to be able to fail.

    THE ORACLE IS JEDEC LEGALITY, not a bandwidth number: replay the issued
    command stream through a per-bank open/closed model and assert that no
    column op is ever issued to a bank with no open row. That is exactly the
    condition the DRAM state model reports as `no_act_before_rd`.

    THE RACE needs a column already classified against an open row at the moment
    the timeout closes it, so the inter-read delay is SWEPT: at some delays the
    next request lands in the pick pipeline as the PRE fires, at others it does
    not. A single delay would pass by luck.
    """
    tb = PumiceMemCmdSchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    done = await tb.complete_init()
    assert done, "init_done never asserted"

    BANK, ROW = 2, 0x123          # the bank/row the board path failed on

    # Guard trace. The whole reason this test lives at the macro level: these are
    # the arbiter-internal pick guards, and here they can be tied to the command
    # that broke the rule.
    #
    # ALIGNMENT IS BY COMMAND ORDINAL, NEVER BY CYCLE. The observable stream is
    # at cmd_valid_o/cmd_ready_i -- CMD_DELAY plus FIFO occupancy downstream of
    # the arbiter's internal fire -- so the two cycle numbers differ by a varying
    # amount and subtracting them is meaningless. An earlier pass read "the read
    # is 4 cycles after the PRE" off two unrelated counters and built a whole
    # theory on it. The cmd FIFO is in-order and lossless, so output command #N
    # IS arbiter fire #N; that identity is ASSERTED below, not assumed.
    #
    # Everything is sampled 1 ps AFTER each rising edge, never on it. w_fire_out
    # is combinational; reading it on the edge samples it before the deltas
    # settle, which is what made an earlier arbiter-side count come up exactly
    # one short (776 vs 777) and wrongly exonerate the arbiter.
    arb = dut.u_arbiter
    guards, fires, outs, pushes, suppressed = {}, [], [], [], []
    _GSIGS = ('w_pre_col_guard', 'r_preguard0', 'r_preguard1', 'r_preguard2',
              'w_preact_bank_guard', 'w_col_inflight_guard', 'w_prepick_guard',
              'w_if_preact_out', 'w_if_col_out', 'w_guarded')

    def _m(sig):
        try:
            return int(getattr(arb, sig).value)
        except Exception:
            return -1

    async def _trace():
        cyc = 0
        while True:
            await RisingEdge(dut.aclk)
            await Timer(1, 'ps')          # let the combinational cone settle
            cyc += 1
            g = {s: _m(s) for s in _GSIGS}
            g['fire'] = _m('w_fire_out')
            g['safe'] = _m('w_out_safe')
            g['rej'] = _m('w_out_reject')
            g['pv'] = _m('r_pick_valid')
            g['crdy'] = _m('cmd_ready_i')
            g['bank'] = _m('r_bank')
            g['do_pre'] = _m('r_do_pre')
            g['do_rd'] = _m('r_do_rd')
            g['rowact'] = _m('r_bank_row_active')
            g['tmo'] = _m('timeout_pre_req_i')
            g['tmo_bank'] = _m('timeout_pre_bank_i')
            guards[cyc] = g
            # THE PUSH, read from the arbiter's OWN handshake rather than
            # reconstructed from r_pick_valid: cmd_valid_o carries the w_out_safe
            # gate (BUG-003), and an instrument that re-derives the condition
            # measures the version of the design it was written against, not the
            # one running. Reading the port cannot drift.
            if int(arb.cmd_valid_o.value) and g['crdy'] == 1:
                pushes.append({'cycle': cyc, 'bank': g['bank'],
                               'op': _m('r_op'), 'row': _m('r_row'),
                               'col': _m('r_col_out'),
                               'safe': g['safe'], 'fire': g['fire'],
                               'do_pre': g['do_pre'], 'do_rd': g['do_rd']})
            # A pick the final gate SUPPRESSED: it was in the output register,
            # the FIFO had room, and it did not go. This is the hazard being
            # caught -- a non-zero count is the positive evidence the test needs,
            # not a failure.
            if g['pv'] == 1 and g['crdy'] == 1 and g['safe'] == 0:
                suppressed.append({'cycle': cyc, 'bank': g['bank'],
                                   'op': _m('r_op'), 'do_rd': g['do_rd'],
                                   'do_pre': g['do_pre']})
            if g['fire'] == 1:
                fires.append({'cycle': cyc, 'bank': g['bank'],
                              'do_pre': g['do_pre'], 'do_rd': g['do_rd']})
            if int(dut.cmd_valid_o.value) and int(dut.cmd_ready_i.value):
                outs.append({'cycle': cyc, 'op': int(dut.cmd_op_o.value),
                             'bank': int(dut.cmd_bank_o.value),
                             'row': int(dut.cmd_row_o.value),
                             'col': int(dut.cmd_col_o.value),
                             'ap': int(dut.cmd_ap_o.value)})
    cocotb.start_soon(_trace())

    def replay(cmds):
        """Return (local index, command) for every column op issued to a bank
        with no open row."""
        state = {b: 'idle' for b in range(8)}
        bad = []
        for i, c in enumerate(cmds):
            op, b = c['op'], c['bank']
            if op == OP_ACT:
                state[b] = 'open'
            elif op == OP_PRE:
                state[b] = 'idle'
            elif op == OP_REF:
                state = {k: 'idle' for k in state}
            elif op in (OP_RD, OP_WR):
                if state.get(b) != 'open':
                    bad.append((i, c))
                if c['ap']:
                    state[b] = 'idle'
        return bad

    async def arm(mode, tr, label):
        dut.page_mode_i.value = mode
        dut.page_tr_init_i.value = tr
        await tb.wait_clocks('aclk', 4)
        # ACCUMULATE the whole arm and replay ONCE. Clearing the stream between
        # reps discarded the ACT that opened the row while the DUT still had it
        # open, so the replay began each window with every bank "idle" and
        # flagged perfectly legal reads -- 38 of 39 points in the open-page
        # baseline, which is how that baseline assertion earned its place.
        base, pbase, sbase = len(outs), len(pushes), len(suppressed)
        cbase = max(guards) if guards else 0
        # Sweep the gap so the next request lands at every phase relative to the
        # timeout PRE. TR=2 expires almost immediately once the bank goes idle.
        # The GAP sweep (0..12) is the stimulus shape; the reps per gap are
        # pure repetition. Reps must stay >= 2 so the >= 100-push vacuity floor
        # below still holds (13 gaps x reps x 4 reads, ~1 push per read).
        for gap in range(0, 13):
            for rep in range(reps_per_gap):
                for k in range(4):
                    tb.rd_entry = {'bank': BANK, 'row': ROW,
                                   'col': 0x40 + 4 * k, 'id': 0xA,
                                   'age': 10, 'slot': 3}
                    for _ in range(40):
                        if tb.rd_entry is None:
                            break
                        await tb.wait_clocks('aclk', 1)
                    await tb.wait_clocks('aclk', gap)
                await tb.wait_clocks('aclk', 16)     # drain CMD_DELAY + FIFO
        stream = outs[base:]
        pstream = pushes[pbase:]
        rej = [p for p in pstream if p['safe'] == 0]
        supp = suppressed[sbase:]
        bad = replay(stream)
        # Cycles in which the page policy actually ASKED for a background close.
        # Without this the whole test is vacuous under any config that disables
        # the timeout: zero closes, zero hazards, green. See
        # feedback_checker_verdict_needs_a_count -- a verdict needs its count.
        tmo_cyc = sum(1 for c, g in guards.items()
                      if c > cbase and g['tmo'] == 1)
        tb.log.info("[%s] mode=%d tr=%d -> %d cmds out, %d pushes, "
                      "%d pushed-but-NOT-safe, %d picks SUPPRESSED by the final "
                      "gate, %d illegal column ops, %d cycles requesting a "
                      "background close",
                      label, mode, tr, len(stream), len(pstream), len(rej),
                      len(supp), len(bad), tmo_cyc)
        return dict(label=label, stream=stream, pstream=pstream, rej=rej,
                    supp=supp, tmo_cyc=tmo_cyc,
                    bad=[(i, c, stream, pstream, rej) for i, c in bad])

    reps_per_gap = _profile_depth('sched_timeout_reps')
    tb.log.info("depth: TEST_LEVEL=%s sched_timeout_reps=%d",
                os.environ.get("TEST_LEVEL", "gate"), reps_per_gap)

    # baseline 1: open page, timeout OFF -> must be clean
    base_open = await arm(0, 0, "open_page_no_timeout")
    # baseline 2: static close (auto-precharge) -> must be clean
    base_close = await arm(2, 0, "static_close")
    # the failing arm: open page + background timeout, TR=2
    tmo = await arm(3, 2, "fixed_open_tr2")

    # THE TEST MUST PROVE IT RAN. Each arm has to have issued a real command
    # stream, and the failing arm has to have actually exercised the background
    # close -- otherwise a green result says nothing about the hazard.
    for a in (base_open, base_close, tmo):
        assert len(a['pstream']) >= 100, (
            f"VACUOUS ARM: {a['label']} pushed only {len(a['pstream'])} commands; "
            f"the stimulus did not run, so its verdict is meaningless.")
    assert tmo['tmo_cyc'] > 0, (
        "VACUOUS TEST: the fixed_open TR=2 arm never asserted "
        "timeout_pre_req_i, so no background close happened and the hazard was "
        "never presented. Check page_mode_i/page_tr_init_i reached the DUT.")
    assert base_open['tmo_cyc'] == 0, (
        f"BASELINE BROKEN: open page with the timeout OFF requested "
        f"{base_open['tmo_cyc']} background closes; it is not a baseline.")
    tb.log.info("coverage: background-close requests -- open_page=%d, "
                  "static_close=%d, fixed_open_tr2=%d (must be >0)",
                  base_open['tmo_cyc'], base_close['tmo_cyc'], tmo['tmo_cyc'])

    assert not base_open['bad'], (
        f"BASELINE BROKEN: open page with no timeout issued a column op to a "
        f"closed bank -- {base_open['bad'][0][1]}. The test is wrong, not the DUT.")
    assert not base_close['bad'], (
        f"BASELINE BROKEN: static close issued a column op to a closed bank -- "
        f"{base_close['bad'][0][1]}.")

    # The defect this test was written for: a pick its own final safety gate
    # rejected (w_out_safe == 0) must not reach the cmd FIFO. cmd_valid_o is
    # gated by w_out_safe, so the push and the fire are the same event; assert
    # that on every arm, not just the one that used to fail.
    for a in (base_open, base_close, tmo):
        assert not a['rej'], (
            f"BUG-003 REGRESSED in {a['label']}: {len(a['rej'])} commands were "
            f"pushed to the cmd FIFO with w_out_safe==0 -- the arbiter rejected "
            f"them at its final gate, never strobed evt_* for them, and issued "
            f"them to the DRAM anyway. First: {a['rej'][0]}")

    # POSITIVE evidence, not just absence. The failing arm must actually reach
    # the hazard -- a pick arriving at the output register after a background
    # close invalidated it -- and the gate must be the thing that stops it. If
    # this count is 0 the arm proves nothing: either the stimulus stopped
    # creating the race or an upstream guard started absorbing it, and in both
    # cases BUG-003's regression check has quietly stopped testing anything.
    tb.log.info("coverage: picks suppressed by the final gate -- open_page=%d, "
                  "static_close=%d, fixed_open_tr2=%d (must be >0)",
                  len(base_open['supp']), len(base_close['supp']),
                  len(tmo['supp']))
    assert tmo['supp'], (
        "COVERAGE LOST: the fixed_open TR=2 arm never presented a pick that the "
        "final safety gate had to reject, so '0 illegal column ops' is vacuous. "
        "BUG-003's mechanism is a rejected pick reaching the cmd FIFO; if no "
        "pick is ever rejected the check is inert. Re-derive the stimulus.")

    if tmo['bad']:
        idx, bad, stream, pstream, rej = tmo['bad'][0]
        ops = {OP_ACT: 'ACT', OP_RD: 'RD', OP_WR: 'WR', OP_PRE: 'PRE',
               OP_REF: 'REF', OP_MRS: 'MRS'}
        trace = " -> ".join(
            f"{ops.get(c['op'], c['op'])}(b{c['bank']}"
            f"{',ap' if c['ap'] else ''})@{c['cycle']}"
            for c in stream if c['bank'] == BANK)

        # The ordinal mapping, made ARM-LOCAL. The cmd FIFO is drained at the end
        # of every gap iteration, so within one arm push #i IS output #i. Assert
        # it rather than assume it: an earlier pass compared the arbiter's cycle
        # counter against the FIFO's and read a 4-cycle gap that did not exist.
        ordinal_ok = (len(pstream) == len(stream))
        dut._log.info("arm pushes=%d, FIFO outputs=%d -> ordinal mapping %s",
                      len(pstream), len(stream),
                      "VALID" if ordinal_ok else "INVALID (do not trust cycles)")
        assert ordinal_ok, (
            f"BUG-003 REPRODUCED ({len(tmo['bad'])} illegal column ops), but the "
            f"push/output ordinal mapping is broken ({len(pstream)} vs "
            f"{len(stream)}), so the guard cycle cannot be identified.")

        p0 = pstream[idx]
        dut._log.info("=== illegal column op is arm command #%d: pushed at cycle "
                      "%d, op=%s bank=%d, w_out_safe=%d, w_fire_out=%d ===",
                      idx, p0['cycle'], ops.get(p0['op'], p0['op']), p0['bank'],
                      p0['safe'], p0['fire'])
        # THE MEASUREMENT. cmd_valid_o == r_pick_valid, so a pick with
        # w_out_safe == 0 is still PUSHED to the FIFO and executed by the DRAM,
        # while w_fire_out == 0 means evt_* never strobed -- the bank timers and
        # the r_guard/r_preguard chains never learned the command happened.
        dut._log.info("pushes with w_out_safe==0 in this arm: %d of %d -- %s",
                      len(rej), len(pstream),
                      [(r['cycle'], ops.get(r['op'], r['op']), r['bank'])
                       for r in rej[:16]])
        n_unsafe_cols = sum(1 for r in rej if r['op'] in (OP_RD, OP_WR))
        dut._log.info("of those, %d are COLUMN ops; the replay found %d illegal "
                      "column ops", n_unsafe_cols, len(tmo['bad']))

        f0 = p0['cycle']
        dut._log.info("%6s %3s %4s %4s %4s %4s %4s %6s | %7s %3s %3s %3s | "
                      "%9s %8s %7s %9s %6s %7s %3s",
                      "cyc", "pv", "crdy", "safe", "fire", "dpre", "drd",
                      "rowact", "pre_col", "pg0", "pg1", "pg2", "preact_bk",
                      "col_infl", "prepick", "ifpre_out", "ifcol", "guarded",
                      "tmo")
        for c in range(max(1, f0 - 12), f0 + 4):
            g = guards.get(c)
            if not g:
                continue
            b = lambda k: ((g[k] >> BANK) & 1) if g[k] >= 0 else -1
            dut._log.info("%6d %3d %4d %4d %4d %4d %4d %6d | %7d %3d %3d %3d | "
                          "%9d %8d %7d %9d %6d %7d %3d",
                          c, g['pv'], g['crdy'], g['safe'], g['fire'],
                          g['do_pre'], g['do_rd'], b('rowact'),
                          b('w_pre_col_guard'), b('r_preguard0'),
                          b('r_preguard1'), b('r_preguard2'),
                          b('w_preact_bank_guard'), b('w_col_inflight_guard'),
                          b('w_prepick_guard'), b('w_if_preact_out'),
                          b('w_if_col_out'), b('w_guarded'), g['tmo'])
        near = [(p['cycle'], ops.get(p['op'], p['op']), 'safe' if p['safe'] else 'UNSAFE')
                for p in pstream if p['bank'] == BANK and f0 - 24 <= p['cycle'] <= f0]
        dut._log.info("pushes to bank %d in [%d..%d]: %s", BANK, f0 - 24, f0, near)
        assert False, (
            f"BUG-003 REPRODUCED at the macro level: column op "
            f"{ops.get(bad['op'], bad['op'])} to bank {bad['bank']} with no open "
            f"row, pushed at cycle {f0} with w_out_safe={p0['safe']} and "
            f"w_fire_out={p0['fire']}. {len(tmo['bad'])} occurrences; "
            f"{len(rej)} pushes this arm had w_out_safe==0.\n"
            f"  bank {BANK} stream: {trace}\n"
            f"  guard trace logged above.")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_pumice_scheduler_layer_training(request, test_level):
    _run_scheduler(request, "cocotb_test_training_priority_and_gate", test_level=test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_pumice_scheduler_layer_timeout_pre_vs_pending_column(request, test_level):
    _run_scheduler(request, "cocotb_test_timeout_pre_vs_pending_column", test_level=test_level)


def _run_scheduler(request, testcase, test_level='gate'):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_scheduler_layer"
    test_name = f"{testcase}_{test_level}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
        "AXI_ID_WIDTH": "8", "NUM_ENTRIES": "8",
        # The in-scheduler command-history scoreboard (audit-only). Its
        # turnaround windows are ELABORATION parameters and must match the
        # timings the TB programs at runtime. They were pinned at 2/2 to match
        # the TB's old invented set; the TB now derives its timings from a named
        # operating point, so these are derived from the same one -- otherwise
        # this second oracle audits windows no config in the table uses, which is
        # worse than not auditing at all because it still reports success.
        "CMD_HISTORY_EN": "1",
        "HIST_T_WTR": str(_CTRL_T['tWTR']), "HIST_T_RTW": str(_CTRL_T['tRTW']),
        # tRRD/tFAW are cross-bank, so the per-bank history cannot see them at
        # all; armed for pumice ISSUE-019 (the arbiter checks both two registers
        # before the fire).
        "HIST_T_RRD": str(_CTRL_T['tRRD']), "HIST_T_FAW": str(_CTRL_T['tFAW']),
    }
    extra_env = {
        "DUT": dut_name, "LOG_PATH": log_path, "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path, **level_env(test_level),
    }
    extra_env.update(params)
    # Command-history scoreboard: generate-gated INSIDE the scheduler
    # (CMD_HISTORY_EN) — fatal JEDEC same-bank sequencing audit
    # (REF-with-row-open + tRFC=8, matching the TB's t_rfc_i). --assert arms it
    # (verilator ignores asserts otherwise).
    compile_args = ["+define+USE_ASYNC_RESET", "--assert"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))), keep_files=True, timescale="1ns/1ps",
    )
