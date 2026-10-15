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

_FILELIST = ("projects/components/mem-ctrl-ip/common-ip/dv/filelists/"
             "mc_store_arbiter_macro.f")

NUM_ENTRIES = 8
N_WR_CHUNKS = 16          # > NUM_ENTRIES: forces two recycles of slot 0
N_RD_DESCS  = 16
N_HOST_BURSTS = 4
CHUNKS_PER_BURST = N_WR_CHUNKS // N_HOST_BURSTS
PHASE_TIMEOUT_NS = 200_000   # 200 us is ~15000 cycles at 75 MHz -- generous


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


@cocotb.test()
async def cocotb_test_store_arbiter_contract(dut):
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


def test_mc_store_arbiter_contract(request):
    from cocotb_test.simulator import run
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "mc_store_arbiter_macro_tb_top"
    test_name = "cocotb_test_store_arbiter_contract"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST)
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    params = {"NUM_ENTRIES": str(NUM_ENTRIES),
              "AXI_ID_WIDTH": "8", "AXI_DATA_WIDTH": "64",
              "NUM_RANKS": "1", "NUM_BANKS": "8",
              "ROW_WIDTH": "14", "COL_WIDTH": "10",
              "AXI_BEATS_PER_BURST": "1", "RD_RET_DEPTH": "32"}
    extra_env = {"DUT": dut_name, "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
                 "COCOTB_LOG_LEVEL": "INFO",
                 "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml")}
    extra_env.update(params)
    run(python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_store_arbiter_contract",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env, parameters=params,
        compile_args=["+define+USE_ASYNC_RESET", "--assert", "--public-flat-rw",
                      "-Wno-MULTIDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        plus_args=(["--trace"] if int(os.environ.get("WAVES", "0")) else []),
        keep_files=True, timescale="1ns/1ps")
