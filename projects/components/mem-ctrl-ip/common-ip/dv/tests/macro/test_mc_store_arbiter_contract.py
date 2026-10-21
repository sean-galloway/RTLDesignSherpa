# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Macro contract test: mc_xddr2_entry_store + the REAL mc_cmd_arbiter.

This is the regression net for the 2026-10-13/14 granite hang class: the
store's commit/issue ready must be STRUCTURAL ("sink has room"), because the
arbiter's column mask gates the entire pick pool on that one scalar term. A
slot-qualified ready closes a combinational circle that wedges the scheduler
permanently once a committed slot drains while the arbiter's slot pointer
still references it.

Escape analysis (why every other test missed it):
  - At NUM_ENTRIES=1 the next push re-validates slot 0 and the loop
    self-heals, so ALL N=1 sims pass regardless of the bug.
  - The deadlock needs MORE THAN N chunks in one direction (a slot must be
    recycled twice with no push healing the pointer in between).
  - In isolation the store's slot-qualified ready is locally well-behaved;
    the violation only exists in the closed loop with the arbiter, and it
    proved sensitive to the real command/drain pacing: this directed test
    (paced 1-in-4) does NOT reproduce the 2026-10-13 hang by itself.

Coverage split (what pins what):
  - THIS test pins the contract SURFACE at N=8 with 2xN chunks: every chunk
    must commit, drain, and return exactly one B per host burst, and every
    read must issue. A gross contract break (ready tied off, B
    mis-aggregation, drain loss) fails here in ~13 s.
  - The specific stale-pointer deadlock is pinned by the real-system cell
    test_granite_top_geared[gate n=8 m=12] (NUM_ENTRIES=8, GRANITE_MANY=12
    outstanding bursts -- the exact on-board hang reproduces there; it is
    what went red on 2026-10-13 and green with the structural-ready fix).
  - common-ip/dv carries NO RTL assertions by repo rule; checkers live in
    the testbenches.
"""

import os

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, with_timeout

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_store_arbiter_macro.f")

NUM_ENTRIES = 8
N_WR_CHUNKS = 16          # > NUM_ENTRIES: forces two recycles of slot 0
N_RD_DESCS  = 16
N_HOST_BURSTS = 4
CHUNKS_PER_BURST = N_WR_CHUNKS // N_HOST_BURSTS
PHASE_TIMEOUT_NS = 200_000   # 200 us is ~15000 cycles at 75 MHz -- generous

# dram_op_e values from mc_common_pkg.sv
OP_ACT = 1
OP_RD  = 2
OP_RDA = 3
OP_WR  = 4
OP_WRA = 5
OP_PRE = 6
OP_REF = 8
OP_REFPB = 9


async def _push_aw(dut, bank, row, col, txn_id, agg, last):
    dut.aw_push_valid.value = 1
    dut.aw_push_bank.value = bank
    dut.aw_push_row.value = row
    dut.aw_push_col.value = col
    dut.aw_push_id.value = txn_id
    dut.aw_push_qos.value = 0
    dut.aw_push_agg.value = agg
    dut.aw_push_last.value = last
    while True:
        await RisingEdge(dut.aclk)
        if dut.aw_push_ready.value == 1:
            break
    dut.aw_push_valid.value = 0


async def _push_wd(dut, data, last):
    dut.wd_valid.value = 1
    dut.wd_data.value = data
    dut.wd_strb.value = 0xFF   # SW = 64/8
    dut.wd_last.value = last
    while True:
        await RisingEdge(dut.aclk)
        if dut.wd_ready.value == 1:
            break
    dut.wd_valid.value = 0


async def _push_ar(dut, bank, row, col, txn_id):
    dut.ar_push_valid.value = 1
    dut.ar_push_bank.value = bank
    dut.ar_push_row.value = row
    dut.ar_push_col.value = col
    dut.ar_push_id.value = txn_id
    dut.ar_push_qos.value = 0
    while True:
        await RisingEdge(dut.aclk)
        if dut.ar_push_ready.value == 1:
            break
    dut.ar_push_valid.value = 0


async def _run_writes(dut):
    """4 host bursts x 4 one-beat chunks; burst b uses id b, last on chunk 3."""
    for b in range(N_HOST_BURSTS):
        for c in range(CHUNKS_PER_BURST):
            await _push_aw(dut, bank=0, row=0, col=b * CHUNKS_PER_BURST + c,
                           txn_id=b, agg=1, last=(c == CHUNKS_PER_BURST - 1))
            await _push_wd(dut, data=0xA500_0000 + (b << 8) + c, last=1)


async def _run_reads(dut):
    for i in range(N_RD_DESCS):
        await _push_ar(dut, bank=0, row=0, col=i, txn_id=i % N_HOST_BURSTS)


async def _wait_for(dut, signal, target):
    while int(signal.value) < target:
        await RisingEdge(dut.aclk)


async def _reset(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, unit="ns").start())
    dut.aresetn.value = 0
    dut.aw_push_valid.value = 0
    dut.wd_valid.value = 0
    dut.ar_push_valid.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)


async def _open_arbiter_gates(dut):
    """Make every JEDEC readiness input permissive so the pick pool is live."""
    dut.u_arb.bank_act_ready_i.value = 0xFF
    dut.u_arb.bank_rdwr_ready_i.value = 0xFF
    dut.u_arb.bank_pre_ready_i.value = 0xFF
    dut.u_arb.bank_act_ready_la_i.value = 0xFF
    dut.u_arb.bank_rdwr_ready_la_i.value = 0xFF
    dut.u_arb.bank_pre_ready_la_i.value = 0xFF
    dut.u_arb.bank_row_active_i.value = 0xFF
    dut.u_arb.bank_open_row_i.value = 0
    dut.u_arb.tfaw_ok_i.value = 1
    dut.u_arb.trrd_ok_i.value = 1
    dut.u_arb.twtr_ok_i.value = 1
    dut.u_arb.trtw_ok_i.value = 1
    dut.u_arb.tccd_ok_i.value = 1
    dut.u_arb.tccd_l_ok_i.value = 1
    dut.u_arb.trrd_l_ok_i.value = 1
    dut.u_arb.refresh_req_i.value = 0
    dut.u_arb.refresh_drain_i.value = 0
    dut.u_arb.maint_req_i.value = 0
    dut.u_arb.init_done_i.value = 1
    dut.u_arb.init_cmd_valid_i.value = 0


async def _cmd_ready_every_cycle(dut):
    """Override the TB's 1-in-4 cm_ready gate so cmd_ready_i is high every cycle.

    r_cm_gate is a 2-bit free-running counter; cm_ready = (r_cm_gate == 0).
    Depositing 0 every cycle keeps r_cm_gate at 0, so cm_ready/cmd_ready_i
    stay asserted.
    """
    dut.r_cm_gate.value = 0


async def _push_wr_chunk(dut, bank, row, col, txn_id=0):
    await _push_aw(dut, bank, row, col, txn_id, agg=1, last=1)
    await _push_wd(dut, data=0xA500_0000 + (bank << 16) + (row << 8) + col, last=1)


@cocotb.test()
async def cocotb_test_store_arbiter_contract(dut):
    await _reset(dut)

    # ---- phase 1: writes ---------------------------------------------------
    wr_task = cocotb.start_soon(_run_writes(dut))
    done_ids = []
    async def _collect_done():
        while len(done_ids) < N_HOST_BURSTS:
            await RisingEdge(dut.aclk)
            if int(dut.wr_done_valid.value) == 1:
                done_ids.append(int(dut.wr_done_id.value))
    await with_timeout(_collect_done(), PHASE_TIMEOUT_NS, "ns")

    # every host burst must report exactly one B, in order
    assert sorted(done_ids) == list(range(N_HOST_BURSTS)), \
        f"wr_done id set wrong: {done_ids} (expect one per host burst)"

    async def _wr_counters():
        await _wait_for(dut, dut.commit_count, N_WR_CHUNKS)
        await _wait_for(dut, dut.drain_count, N_WR_CHUNKS)
    await with_timeout(_wr_counters(), PHASE_TIMEOUT_NS, "ns")
    await wr_task

    # ---- phase 2: reads ----------------------------------------------------
    rd_task = cocotb.start_soon(_run_reads(dut))
    await with_timeout(_wait_for(dut, dut.rd_issue_count, N_RD_DESCS),
                       PHASE_TIMEOUT_NS, "ns")
    await rd_task

    # ---- contract summary --------------------------------------------------
    commits = int(dut.commit_count.value)
    drains = int(dut.drain_count.value)
    issues = int(dut.rd_issue_count.value)
    dut._log.info("contract: commits=%d drains=%d rd_issues=%d b_count=%d",
                  commits, drains, issues, len(done_ids))
    assert commits == N_WR_CHUNKS, f"commits {commits} != {N_WR_CHUNKS}"
    assert drains == N_WR_CHUNKS, f"drains {drains} != {N_WR_CHUNKS}"
    assert issues == N_RD_DESCS, f"rd issues {issues} != {N_RD_DESCS}"


@cocotb.test()
async def cocotb_test_hold_on_gate_block(dut):
    """A blocked live JEDEC gate must HOLD the chosen winner, not drop/re-pick it.

    Old RTL: w_out_reject makes w_out_ready true, so the output register is
    overwritten by a fresh pick next cycle. With a second candidate in bank 1
    still ready, the bank/row/col of the output command changes while the gate
    is closed -- the winner is not held.
    """
    await _reset(dut)
    await _open_arbiter_gates(dut)
    await _cmd_ready_every_cycle(dut)

    # Preload two candidates in different banks. Bank 0 is the older winner.
    await _push_wr_chunk(dut, bank=0, row=0, col=10)
    await _push_wr_chunk(dut, bank=1, row=0, col=20)

    # Wait until the first pick has reached the output register and is bank 0.
    while True:
        await _cmd_ready_every_cycle(dut)
        await RisingEdge(dut.aclk)
        if int(dut.u_arb.r_pick_valid.value) and int(dut.u_arb.cmd_bank_o.value) == 0:
            break

    chosen_op = int(dut.u_arb.cmd_op_o.value)
    chosen_bank = int(dut.u_arb.cmd_bank_o.value)
    chosen_row = int(dut.u_arb.cmd_row_o.value)
    chosen_col = int(dut.u_arb.cmd_col_o.value)

    # Block bank 0's read/write ready path (live JEDEC gate), keep bank 1 open.
    dut.u_arb.bank_rdwr_ready_i.value = 0xFE   # bit 0 low
    dut.u_arb.bank_rdwr_ready_la_i.value = 0xFE

    held_cycles = 0
    for _ in range(8):
        await _cmd_ready_every_cycle(dut)
        await RisingEdge(dut.aclk)
        if not int(dut.u_arb.cmd_valid_o.value):
            assert False, "cmd_valid_o dropped while gate blocked"
        if (int(dut.u_arb.cmd_op_o.value) != chosen_op or
            int(dut.u_arb.cmd_bank_o.value) != chosen_bank or
            int(dut.u_arb.cmd_row_o.value) != chosen_row or
            int(dut.u_arb.cmd_col_o.value) != chosen_col):
            assert False, ("command changed while gate blocked: "
                           f"op {int(dut.u_arb.cmd_op_o.value)} bank "
                           f"{int(dut.u_arb.cmd_bank_o.value)} row "
                           f"{int(dut.u_arb.cmd_row_o.value)} col "
                           f"{int(dut.u_arb.cmd_col_o.value)}")
        held_cycles += 1

    # Open the gate. The held winner should fire exactly once.
    before = int(dut.drain_count.value)
    dut.u_arb.bank_rdwr_ready_i.value = 0xFF
    dut.u_arb.bank_rdwr_ready_la_i.value = 0xFF

    for _ in range(4):
        await _cmd_ready_every_cycle(dut)
        await RisingEdge(dut.aclk)
        if int(dut.drain_count.value) == before + 1:
            break
    after = int(dut.drain_count.value)
    assert after == before + 1, f"held winner fired {after - before} times, expected 1"


@cocotb.test()
async def cocotb_test_zero_bubble_stream(dut):
    """With all gates open, a same-bank row-hit stream must fire every cycle.

    Old RTL drops a pick on any transient reject and must refill its 3-stage
    pipeline, producing at least one idle cycle. We create that reject by
    briefly closing bank_rdwr_ready_i for one cycle mid-stream while a
    replenishment task keeps the pool filled.
    """
    await _reset(dut)
    await _open_arbiter_gates(dut)

    # Seed the pipeline with same-bank row-hit writes.
    for col in range(8):
        await _push_wr_chunk(dut, bank=0, row=0, col=col)

    # Keep the pool filled: start a new push for every command that drains.
    # Each push takes ~2 cycles; overlapping tasks let the store stay full
    # even when the arbiter drains one entry per cycle.
    next_col = 8
    async def _replenish():
        nonlocal next_col
        prev = int(dut.drain_count.value)
        while True:
            await RisingEdge(dut.aclk)
            cur = int(dut.drain_count.value)
            if cur > prev:
                for _ in range(cur - prev):
                    cocotb.start_soon(_push_wr_chunk(dut, bank=0, row=0, col=next_col))
                    next_col += 1
            prev = cur
    repl_task = cocotb.start_soon(_replenish())

    # Prime slowly (use the TB's natural 1-in-4 cm_ready) so replenishment can
    # fully backfill the store before we measure the every-cycle steady state.
    for _ in range(24):
        await RisingEdge(dut.aclk)

    # Run a measured steady-state window. With all gates open and a filled
    # pool, the new core must produce a valid column command every cycle.
    steady_fires = 0
    steady_idle = 0
    for _ in range(16):
        await _cmd_ready_every_cycle(dut)
        await RisingEdge(dut.aclk)
        if int(dut.u_arb.cmd_valid_o.value) and int(dut.u_arb.cmd_ready_i.value):
            steady_fires += 1
        else:
            steady_idle += 1

    # Inject a one-cycle gate block; new core holds, old core drops -> bubble.
    dut.u_arb.bank_rdwr_ready_i.value = 0xFE
    dut.u_arb.bank_rdwr_ready_la_i.value = 0xFE
    await _cmd_ready_every_cycle(dut)
    await RisingEdge(dut.aclk)
    dut.u_arb.bank_rdwr_ready_i.value = 0xFF
    dut.u_arb.bank_rdwr_ready_la_i.value = 0xFF

    # Measure recovery: with hold-on-not-fired, the blocked winner is still
    # valid the cycle the gate reopens, so the very next cycle must fire it
    # with no refill bubble.
    post_fires = 0
    post_idle = 0
    for _ in range(8):
        await _cmd_ready_every_cycle(dut)
        await RisingEdge(dut.aclk)
        if int(dut.u_arb.cmd_valid_o.value) and int(dut.u_arb.cmd_ready_i.value):
            post_fires += 1
        else:
            post_idle += 1

    repl_task.cancel()

    assert steady_idle == 0, f"steady-state bubbles: {steady_idle} idle cycles"
    assert post_idle == 0, f"post-gate bubbles: {post_idle} idle cycles"


@cocotb.test()
async def cocotb_test_post_pop_winner(dut):
    """The cycle after a pop must show the speculative next-winner, not a bubble.

    We preload entry A, let it reach the output register, then preload B and
    fire A in the next cycle. B is in the live pool but has not yet reached the
    STAGE-1a snapshot. The new core speculatively computes the pool-minus-A
    winner (B) and emits it on the next cycle; the old core either re-picks A
    or produces a bubble.
    """
    await _reset(dut)
    await _open_arbiter_gates(dut)

    # Preload A, let it reach the output register, then preload B.
    await _push_wr_chunk(dut, bank=0, row=0, col=10)   # A
    while True:
        await _cmd_ready_every_cycle(dut)
        await RisingEdge(dut.aclk)
        if (int(dut.u_arb.r_pick_valid.value) and
            int(dut.u_arb.cmd_valid_o.value) and
            int(dut.u_arb.cmd_op_o.value) in (OP_WR, OP_WRA)):
            break

    a_slot = int(dut.u_arb.r_commit_slot.value)

    # Preload B while A sits in the output register. B is now in the live pool
    # but has not yet propagated into the STAGE-1a snapshot.
    await _push_wr_chunk(dut, bank=0, row=0, col=20)   # B

    # Fire A.
    await _cmd_ready_every_cycle(dut)
    await RisingEdge(dut.aclk)

    # Next cycle: must be a valid WR to a different slot (B).
    await _cmd_ready_every_cycle(dut)
    await RisingEdge(dut.aclk)

    assert int(dut.u_arb.cmd_valid_o.value), "post-pop cycle was a bubble"
    assert int(dut.u_arb.cmd_op_o.value) in (OP_WR, OP_WRA), \
        f"post-pop op {int(dut.u_arb.cmd_op_o.value)} is not a column write"
    b_slot = int(dut.u_arb.r_commit_slot.value)
    assert b_slot != a_slot, f"post-pop re-picked the same slot {a_slot}"


@cocotb.test()
async def cocotb_test_override_preempts_speculation(dut):
    """An init-passthrough override must preempt a held speculative column pick.

    We load one write, hold cmd_ready_i low until the WR reaches the output
    register, then raise init_cmd_valid_i while init_done_i is low. The override
    must be emitted instead of the WR; the WR must not be committed as a stale
    winner. After the override drains, the live pool still contains the WR and
    it is picked cleanly.
    """
    await _reset(dut)
    await _open_arbiter_gates(dut)

    # Preload a write and let it reach the output register, but keep cmd_ready_i
    # low so it cannot fire yet.
    await _push_wr_chunk(dut, bank=0, row=0, col=10)
    while True:
        dut.r_cm_gate.value = 1          # cm_ready = 0
        await RisingEdge(dut.aclk)
        if (int(dut.u_arb.r_pick_valid.value) and
            int(dut.u_arb.cmd_op_o.value) in (OP_WR, OP_WRA)):
            break

    # Raise init-passthrough override.
    dut.u_arb.init_done_i.value = 0
    dut.u_arb.init_cmd_valid_i.value = 1
    dut.u_arb.init_cmd_op_i.value = OP_ACT
    dut.u_arb.init_cmd_bank_i.value = 0
    dut.u_arb.init_cmd_row_i.value = 0

    # Release cmd_ready_i; the very next valid command must be the override.
    saw_override = False
    speculative_fired = False
    for i in range(8):
        dut.r_cm_gate.value = 0          # cm_ready = 1
        await RisingEdge(dut.aclk)
        op = int(dut.u_arb.cmd_op_o.value)
        valid = int(dut.u_arb.cmd_valid_o.value)
        if valid:
            if op in (OP_WR, OP_WRA):
                speculative_fired = True
            if op == OP_ACT:
                saw_override = True
            if saw_override or speculative_fired:
                break

    assert saw_override, "init override did not preempt the speculative column"
    assert not speculative_fired, "speculative WR fired before/instead of override"

    # Drain the override and drop init passthrough.
    dut.u_arb.init_cmd_valid_i.value = 0
    dut.u_arb.init_done_i.value = 1

    # Normal picking must resume from the live pool (the original WR).
    saw_wr = False
    for _ in range(8):
        dut.r_cm_gate.value = 0
        await RisingEdge(dut.aclk)
        if (int(dut.u_arb.cmd_valid_o.value) and
            int(dut.u_arb.cmd_op_o.value) in (OP_WR, OP_WRA)):
            saw_wr = True
            break
    assert saw_wr, "normal picking did not resume from the live pool"


CONTRACT_TESTS = [
    "cocotb_test_store_arbiter_contract",
    "cocotb_test_hold_on_gate_block",
    "cocotb_test_zero_bubble_stream",
    "cocotb_test_post_pop_winner",
    "cocotb_test_override_preempts_speculation",
]


@pytest.mark.parametrize("testcase", CONTRACT_TESTS)
def test_mc_store_arbiter_contract(request, testcase):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_store_arbiter_macro_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"NUM_ENTRIES": str(NUM_ENTRIES),
              "AXI_ID_WIDTH": "8", "AXI_DATA_WIDTH": "64",
              "NUM_RANKS": "1", "NUM_BANKS": "8",
              "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "AXI_BEATS_PER_BURST": "1", "RD_RET_DEPTH": "32"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{testcase}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      FIELD_COMBO_VLT, "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
