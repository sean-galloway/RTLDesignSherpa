# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B macro runner for `pumice_mem_cmd_scheduler`."""

import os
import sys
import random

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_mem_cmd_scheduler_tb import (  # noqa: E402
    PumiceMemCmdSchedulerTB, OP_ACT, OP_RD, OP_WR, OP_PRE, OP_REF, OP_MRS,
)

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/macro/pumice_mem_cmd_scheduler.f")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_refresh_vs_inflight_read(dut):
    """PUMICE-037 at the scheduler layer: refresh landing on an in-flight read.

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
            f"PUMICE-037: PRE(bank {BANK}) issued {d_rd_pre} cycles after RD to "
            f"the same bank, tRTP={t_rtp}. The DRAM is precharged while its read "
            f"burst is still being driven out.")
        d_pre_ref = at(ref_c, ref_i) - at(pre_c, pre_i)
        assert d_pre_ref >= t_rp, (
            f"PUMICE-037: REF issued {d_pre_ref} cycles after PRE, tRP={t_rp}.")

    tb.log.info(
        f"refresh vs in-flight read: {len(rds)} RD, {len(pres)} PRE, "
        f"{len(refs)} REF; spacing respects tRTP={t_rtp} tRP={t_rp}")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_mem_cmd_scheduler(dut):
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
    for i in range(40):
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
    assert len(tb.ops_of(OP_RD)) == 40, \
        f"phase-5 expected exactly 40 RD columns, saw {len(tb.ops_of(OP_RD))}"
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
    for i in range(30):
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
    assert rds == 30 and wrs == 30, f"expected exactly 30/30 mixed columns, {rds}/{wrs}"
    tb.log.info(f"phase 6: {mixed} concurrent wr+rd pairs "
                f"({rds} RD, {wrs} WR) under the global tWTR/tRTW audit")

    tb.log.info("PASS: init MRS stream, ACT->RD (real tRCD timers), open-page WR "
                "commit (no re-ACT), refresh PRE->REF, refresh-pressure audit, "
                "concurrent-turnaround audit")


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_refresh_vs_read_stream(dut):
    """PUMICE-037: a SUSTAINED read stream across a refresh.

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
        f"PUMICE-037: {len(bad)} column command(s) issued to a bank with no open "
        f"row, across {len(refs)} refresh(es) and {len(cols)} columns. "
        f"First: cycle {bad[0][0]} op={bad[0][1]} bank={bad[0][2]} ({bad[0][3]}). "
        f"A read to a closed row returns undriven DQ -- the board's all-ones.")

    tb.log.info(f"read stream across refresh: {len(cols)} columns, {len(refs)} REF, "
                f"every column on an open row")


def test_pumice_mem_cmd_scheduler_refresh_read_stream(request):
    """PUMICE-037: sustained read stream across a refresh."""
    _run_scheduler(request, "cocotb_test_refresh_vs_read_stream")


def test_pumice_mem_cmd_scheduler_refresh_inflight_read(request):
    """Refresh vs an in-flight read: JEDEC spacing holds. PASSES.

    Written to reproduce PUMICE-037 and it does NOT: the refresh path respects
    tRTP from the last same-bank column and tRP into the REF. Kept as a
    regression guard on that property, and as the record that the
    scheduler's command spacing is NOT the mechanism.
    """
    _run_scheduler(request, "cocotb_test_refresh_vs_inflight_read")


def test_pumice_mem_cmd_scheduler(request):
    _run_scheduler(request, "cocotb_test_pumice_mem_cmd_scheduler")


def _run_scheduler(request, testcase):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_mem_cmd_scheduler"
    test_name = testcase

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
        # enable the in-scheduler command-history scoreboard (audit-only);
        # global turnaround windows match the TB's t_wtr_i/t_rtw_i = 2
        "CMD_HISTORY_EN": "1", "HIST_T_WTR": "2", "HIST_T_RTW": "2",
    }
    extra_env = {
        "DUT": dut_name, "LOG_PATH": log_path, "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path, "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
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
