# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Macro contract test: mc_xddr2_entry_store + a REAL pick core.

Parametrized over the two scheduler cores (tb_top SCHED_CORE):
  bank_pick -- mc_bank_head_records + mc_bank_pick (the family core; all five
               cells must pass -- the four pipeline-acceptance cells are the
               Phase 2 gate of docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md)
  frfcfs    -- mc_cmd_arbiter (research core). The baseline contract cell and
               the zero-bubble stream pass; hold-on-gate-block, post-pop
               winner and override-preempts fail by design on it and are kept
               as STRICT xfails: they document the behaviour the per-bank
               core replaces, and a research-core change that starts passing
               one is news.
The test reads the core only through the tb_top's generic observability
ports (pick_valid, cmd_*), never through core internals.

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
from cocotb.triggers import RisingEdge, ReadOnly, Timer, with_timeout

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
    # TB-level live-gate / override ports (real inputs, not folded constants).
    dut.bank_act_ready.value = 0xFF
    dut.bank_rdwr_ready.value = 0xFF
    dut.bank_pre_ready.value = 0xFF
    dut.init_done.value = 1
    dut.init_cmd_valid.value = 0
    dut.init_cmd_op.value = 0
    dut.init_cmd_bank.value = 0
    dut.init_cmd_row.value = 0
    dut.cmd_ready_mode.value = 0
    dut.la_open.value = 0
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)


async def _open_arbiter_gates(dut):
    """Make every JEDEC readiness input permissive so the pick pool is live.

    Only the TB-level ports are driven. The global windows (tFAW/tRRD/tWTR/
    tRTW/tCCD), refresh and maintenance requests are constant-permissive in
    the tb_top; a cocotb deposit on a constant-tied arbiter port is folded
    away by Verilator and does nothing (that is how the hold cell went
    unverifiable, 2026-10-21).
    """
    dut.bank_act_ready.value = 0xFF
    dut.bank_rdwr_ready.value = 0xFF
    dut.bank_pre_ready.value = 0xFF
    dut.init_done.value = 1
    dut.init_cmd_valid.value = 0


def _cmd_ready_every_cycle(dut):
    """Command bus ready every cycle (tb_top cmd_ready_mode = 1)."""
    dut.cmd_ready_mode.value = 1


def _cmd_ready_never(dut):
    """Hold the command bus: never ready (tb_top cmd_ready_mode = 2)."""
    dut.cmd_ready_mode.value = 2


async def _sample(dut):
    """Settle this cycle's combinational state, snapshot what the core will do
    at the coming edge, then step past it.

    Sampled in ReadOnly BEFORE the edge: `fire` is exact (cmd_valid && cmd_ready
    is the fire condition for this edge); sampling after the edge would read
    the next cycle's state."""
    await ReadOnly()
    snap = {
        "pick": int(dut.pick_valid.value),
        "fire": int(dut.cmd_valid.value) and int(dut.cmd_ready.value),
        "op": int(dut.cmd_op.value),
        "bank": int(dut.cmd_bank.value),
        "row": int(dut.cmd_row.value),
        "col": int(dut.cmd_col.value),
        "slot": int(dut.cmd_slot.value),
        # store-side context for a bubble post-mortem (not asserted on)
        "sch": bin(int(dut.u_store.wr_sch_valid_o.value)).count("1"),
        "pend": bin(int(dut.u_store.wr_sch_pend_o.value)).count("1"),
        "crdy": int(dut.u_store.wr_commit_ready_o.value),
    }
    await RisingEdge(dut.aclk)
    await Timer(1, "ns")
    return snap


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

    # Preload two candidates in different banks with the command bus held
    # (never ready), so both are in the pool before anything fires and the
    # round-robin pick lands on bank 0 first.
    _cmd_ready_never(dut)
    await _push_wr_chunk(dut, bank=0, row=0, col=10)
    await _push_wr_chunk(dut, bank=1, row=0, col=20)
    for _ in range(6):
        await RisingEdge(dut.aclk)
    await Timer(1, "ns")
    held = await _sample(dut)
    assert held["pick"] and held["bank"] == 0, f"expected bank 0 held in the output stage, got {held}"
    chosen = (held["op"], held["bank"], held["row"], held["col"])

    # Block bank 0's read/write ready path (live JEDEC gate), keep bank 1 open,
    # and release the command bus. The held winner must stay bank 0 with its
    # fields unchanged, and nothing may fire.
    dut.bank_rdwr_ready.value = 0xFE   # bit 0 low
    _cmd_ready_every_cycle(dut)
    for _ in range(8):
        sn = await _sample(dut)
        assert sn["pick"], f"winner dropped while gate blocked: {sn}"
        assert (sn["op"], sn["bank"], sn["row"], sn["col"]) == chosen, \
            f"command changed while gate blocked: {sn} vs {chosen}"
        assert not sn["fire"], f"fired while bank 0's gate was blocked: {sn}"

    # Open the gate. The held winner fires exactly once, immediately, then
    # bank 1 follows.
    dut.bank_rdwr_ready.value = 0xFF
    first = await _sample(dut)
    assert first["fire"], f"held winner did not fire the cycle the gate opened: {first}"
    assert (first["op"], first["bank"], first["row"], first["col"]) == chosen, \
        f"the fired command is not the held winner: {first} vs {chosen}"
    second = await _sample(dut)
    assert not (second["fire"] and second["bank"] == 0), \
        f"the held winner fired twice: {second}"


@cocotb.test()
async def cocotb_test_zero_bubble_stream(dut):
    """With all gates open, a same-bank row-hit stream must fire every cycle.

    Old RTL drops a pick on any transient reject and must refill its 3-stage
    pipeline, producing at least one idle cycle. We create that reject by
    briefly closing bank_rdwr_ready_i for one cycle mid-stream while the pool
    is kept full.

    The pool is fed by two free-running streams (one AW per cycle, one W beat
    per cycle, each handshake sampled exactly in ReadOnly before the edge), so
    the store refills at the fire rate and the measurement is of the core, not
    of the stimulus: the storage -> scheduler record lags the store by one
    cycle, so a pool that runs down to one or two entries bubbles for that
    reason alone. The steady-state log carries the store depth for the
    post-mortem.
    """
    await _reset(dut)
    await _open_arbiter_gates(dut)
    # The one-cycle block below is a LIVE-gate dip only: the lookahead keeps
    # reading ready, as it would for a late reload (a timer never re-arms by
    # itself, so a dip on both would be unphysical and would starve the
    # decode for a cycle on its own).
    dut.la_open.value = 1

    # Free-running AW / W streams: same bank, same row, ascending columns.
    state = {"aw": 0, "wd": 0, "run": True}

    async def _aw_stream():
        dut.aw_push_bank.value = 0
        dut.aw_push_row.value = 0
        dut.aw_push_id.value = 0
        dut.aw_push_qos.value = 0
        dut.aw_push_agg.value = 1
        dut.aw_push_last.value = 1
        while state["run"]:
            dut.aw_push_valid.value = 1
            dut.aw_push_col.value = state["aw"] & 0x3FF
            await ReadOnly()
            took = int(dut.aw_push_ready.value) == 1
            await RisingEdge(dut.aclk)
            await Timer(1, "ns")
            if took:
                state["aw"] += 1
        dut.aw_push_valid.value = 0

    async def _wd_stream():
        dut.wd_strb.value = 0xFF
        dut.wd_last.value = 1
        while state["run"]:
            dut.wd_valid.value = 1
            dut.wd_data.value = 0xA500_0000 + (state["wd"] & 0xFFFF)
            await ReadOnly()
            took = int(dut.wd_ready.value) == 1
            await RisingEdge(dut.aclk)
            await Timer(1, "ns")
            if took:
                state["wd"] += 1
        dut.wd_valid.value = 0

    await Timer(1, "ns")
    aw_task = cocotb.start_soon(_aw_stream())
    wd_task = cocotb.start_soon(_wd_stream())

    # Prime at the TB's natural 1-in-4 pace until the store is full.
    for _ in range(32):
        await RisingEdge(dut.aclk)
    await Timer(1, "ns")

    # Run a measured steady-state window at full command-bus speed. With all
    # gates open and a fed pool, the core must fire a column every cycle.
    _cmd_ready_every_cycle(dut)
    steady_fires = 0
    steady_idle = 0
    trace = []
    for _ in range(16):
        sn = await _sample(dut)
        trace.append((sn["fire"], sn["pick"], sn["sch"], sn["pend"], sn["crdy"]))
        if sn["fire"]:
            steady_fires += 1
        else:
            steady_idle += 1
    dut._log.info("steady trace (fire, pick, schedulable, pending, commit_ready): %s", trace)

    # Inject a one-cycle gate block; new core holds, old core drops -> bubble.
    dut.bank_rdwr_ready.value = 0xFE
    blocked = await _sample(dut)
    assert not blocked["fire"], "fired through a closed rdwr gate"
    dut.bank_rdwr_ready.value = 0xFF

    # Measure recovery: with hold-on-not-fired, the blocked winner is still
    # valid the cycle the gate reopens, so the very next cycle must fire it
    # with no refill bubble.
    post_fires = 0
    post_idle = 0
    for _ in range(8):
        sn = await _sample(dut)
        if sn["fire"]:
            post_fires += 1
        else:
            post_idle += 1

    state["run"] = False
    await RisingEdge(dut.aclk)
    aw_task.cancel()
    wd_task.cancel()

    dut._log.info("zero-bubble: steady %d/%d fired, post-block %d/%d fired (aw pushed %d, wd pushed %d)",
                  steady_fires, steady_fires + steady_idle, post_fires, post_fires + post_idle,
                  state["aw"], state["wd"])
    assert steady_idle == 0, f"steady-state bubbles: {steady_idle} idle cycles; trace {trace}"
    assert post_idle == 0, f"post-gate bubbles: {post_idle} idle cycles"


@cocotb.test()
async def cocotb_test_post_pop_winner(dut):
    """The cycle after a pop must fire the next entry, not a bubble.

    A and B (same bank, same row) are loaded while the command bus is held, so
    A sits in the output stage with B behind it. When the bus is released, A
    fires; the VERY NEXT cycle must fire B (a column to a different slot). A
    core that re-reads its storage view after the pop sees A still there for
    a cycle (the storage -> scheduler record lags by one) and either re-picks
    A or produces a bubble; the new core serves the pair from its second
    record in that cycle.
    """
    await _reset(dut)
    await _open_arbiter_gates(dut)

    _cmd_ready_never(dut)
    await _push_wr_chunk(dut, bank=0, row=0, col=10)   # A
    await _push_wr_chunk(dut, bank=0, row=0, col=20)   # B
    for _ in range(6):
        await RisingEdge(dut.aclk)
    await Timer(1, "ns")
    held = await _sample(dut)
    assert held["pick"] and held["op"] in (OP_WR, OP_WRA), f"expected a held WR, got {held}"

    # Release the bus: cycle 1 fires A, cycle 2 must fire B.
    _cmd_ready_every_cycle(dut)
    fired = []
    for _ in range(2):
        sn = await _sample(dut)
        fired.append((sn["op"], sn["slot"], sn["col"]) if sn["fire"] else None)
    dut._log.info("post-pop (op, slot, col) per cycle: %s", fired)
    assert fired[0] is not None and fired[0][0] in (OP_WR, OP_WRA), f"A did not fire first: {fired}"
    assert fired[1] is not None, f"post-pop cycle was a bubble: {fired}"
    assert fired[1][0] in (OP_WR, OP_WRA), f"post-pop op {fired[1][0]} is not a column write"
    assert fired[1][1] != fired[0][1], f"post-pop re-fired the same slot {fired[0][1]}"
    assert {fired[0][2], fired[1][2]} == {10, 20}, f"post-pop columns wrong: {fired}"


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
    _cmd_ready_never(dut)
    await _push_wr_chunk(dut, bank=0, row=0, col=10)
    await Timer(1, "ns")
    held = False
    for _ in range(40):
        sn = await _sample(dut)
        held = sn["pick"] and sn["op"] in (OP_WR, OP_WRA)
        if held:
            break
    assert held, "the WR never reached the output stage"

    # Raise init-passthrough override.
    dut.init_done.value = 0
    dut.init_cmd_valid.value = 1
    dut.init_cmd_op.value = OP_ACT
    dut.init_cmd_bank.value = 0
    dut.init_cmd_row.value = 0

    # Release cmd_ready_i; the very next valid command must be the override.
    # 16 cycles covers a registered-winner core (override visible in 1-2) and
    # the old 4-stage pipe (its init passthrough takes ~5); the trace lets a
    # failure be read as "fired the WR first" vs "emitted nothing".
    saw_override = False
    speculative_fired = False
    trace = []
    _cmd_ready_every_cycle(dut)
    for i in range(16):
        sn = await _sample(dut)
        op, valid = sn["op"], sn["fire"]
        trace.append((i, valid, op))
        if valid:
            if op in (OP_WR, OP_WRA):
                speculative_fired = True
            if op == OP_ACT:
                saw_override = True
            if saw_override or speculative_fired:
                break

    dut._log.info("override window (cycle, valid, op): %s", trace)
    # Check the WR first: the old core's actual failure is the held WRA firing
    # in the cycle cmd_ready returns (trace [(0, 1, OP_WRA)]); testing
    # saw_override first mislabelled it as "nothing emitted".
    assert not speculative_fired, "speculative WR fired before/instead of override"
    assert saw_override, "init override did not preempt the speculative column"

    # Drain the override and drop init passthrough.
    dut.init_cmd_valid.value = 0
    dut.init_done.value = 1

    # Normal picking must resume from the live pool (the original WR).
    saw_wr = False
    for _ in range(8):
        sn = await _sample(dut)
        if sn["fire"] and sn["op"] in (OP_WR, OP_WRA):
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
ACCEPTANCE_TESTS = CONTRACT_TESTS[1:]
# Cells the FRFCFS research core fails by design (strict xfail). The
# zero-bubble stream is NOT among them: once the stimulus kept the pool fed
# (free-running AW/W streams) the research core also streamed bubble-free, so
# its Phase 0 "4 idle in 16" was the old stimulus running dry, not the core.
FRFCFS_XFAIL = {
    "cocotb_test_hold_on_gate_block": "drop-on-reject: the output register is re-picked while the gate is closed",
    "cocotb_test_post_pop_winner": "no speculative post-pop winner: the cycle after a pop is a bubble",
    "cocotb_test_override_preempts_speculation": "a held column fires before the init override",
}
CORES = {"bank_pick": "1", "frfcfs": "0"}     # mc_common_pkg MC_SCHED_*


def _cells():
    out = []
    for core in CORES:
        for tc in CONTRACT_TESTS:
            marks = []
            if core == "frfcfs" and tc in FRFCFS_XFAIL:
                marks.append(pytest.mark.xfail(
                    strict=True,
                    reason=f"FRFCFS research core, by design: {FRFCFS_XFAIL[tc]} "
                           "(Phase 0 report section 3); the per-bank core replaces it"))
            out.append(pytest.param(core, tc, id=f"{core}-{tc.removeprefix('cocotb_test_')}",
                                    marks=marks))
    return out


@pytest.mark.parametrize("core,testcase", _cells())
def test_mc_store_arbiter_contract(request, core, testcase):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_store_arbiter_macro_tb_top"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    tag = f"{core}_{testcase}"
    sim_build = sim_build_path(tests_dir, tag)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"NUM_ENTRIES": str(NUM_ENTRIES),
              "AXI_ID_WIDTH": "8", "AXI_DATA_WIDTH": "64",
              "NUM_RANKS": "1", "NUM_BANKS": "8",
              "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "AXI_BEATS_PER_BURST": "1", "RD_RET_DEPTH": "32",
              "SCHED_CORE": CORES[core]}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{tag}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{tag}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase=testcase,
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      FIELD_COMBO_VLT, "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
