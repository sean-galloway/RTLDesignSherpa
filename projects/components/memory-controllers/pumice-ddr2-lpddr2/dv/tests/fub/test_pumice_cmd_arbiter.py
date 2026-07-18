# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B runner for `pumice_cmd_arbiter`."""

import os
import sys
import random

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from pumice_coverage import get_coverage_compile_args, get_coverage_env  # noqa: E402
from tbclasses.pumice_cmd_arbiter_tb import (  # noqa: E402
    PumiceCmdArbiterTB, OP_ACT, OP_RD, OP_WR, OP_PRE, OP_REF,
    PAGE_OPEN, PAGE_CLOSE,
)
OP_MRS = 0xA

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_cmd_arbiter.f")


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_pumice_cmd_arbiter(dut):
    tb = PumiceCmdArbiterTB(dut)
    await tb.setup_clocks_and_reset()

    # ===== 1. INIT passthrough (init_done=0) =====
    dut.init_done_i.value = 0
    dut.init_cmd_valid_i.value = 1
    dut.init_cmd_op_i.value = OP_MRS
    dut.init_cmd_bank_i.value = 2
    dut.init_cmd_row_i.value = 0x532
    await tb.settle()
    p = tb.picked()
    assert p['valid'] == 1 and p['op'] == OP_MRS and p['bank'] == 2 and p['row'] == 0x532, \
        f"init passthrough wrong: {p}"
    dut.init_cmd_valid_i.value = 0
    dut.init_done_i.value = 1

    # ===== 2. REFRESH: active bank -> PRE first, then REF+grant =====
    tb.set_bank_bits(dut.bank_row_active_i, {3: 1})
    tb.set_bank_bits(dut.bank_pre_ready_i, {3: 1})
    dut.refresh_req_i.value = 1
    await tb.settle()
    p = tb.picked(); s = tb.strobes()
    assert p['op'] == OP_PRE and p['bank'] == 3, f"refresh should PRE active bank first: {p}"
    assert s['pre'] == 1 and s['grant'] == 0, f"expected PRE strobe, no grant yet: {s}"
    # now no active banks -> REF + grant
    tb.set_bank_bits(dut.bank_row_active_i, {})
    await tb.settle()
    p = tb.picked(); s = tb.strobes()
    assert p['op'] == OP_REF and s['grant'] == 1, f"refresh should REF+grant when idle: {p} {s}"
    dut.refresh_req_i.value = 0

    # ===== 3. READ-PRIORITY row-hit: RD wins over WR when both hit =====
    # bank 5 open @ row 0x100; both a RD and WR entry hit it; RD must be picked.
    tb.set_bank_bits(dut.bank_row_active_i, {5: 1})
    tb.set_bank_bits(dut.bank_rdwr_ready_i, {5: 1})
    tb.set_open_rows({5: 0x100})
    tb.set_entries('rd', {4: (5, 0x100, 0x40, 10)})
    tb.set_entries('wr', {2: (5, 0x100, 0x40, 99)})   # older WR, but RD has priority
    await tb.settle()
    p = tb.picked(); s = tb.strobes()
    assert p['op'] == OP_RD and p['bank'] == 5 and p['col'] == 0x40, f"read-priority pick: {p}"
    assert s['rd'] == 1 and s['rd_issue'] == 1 and s['rd_issue_slot'] == 4, f"rd issue: {s}"
    assert s['wr'] == 0 and s['wr_commit'] == 0, "WR must not fire under read-priority"

    # ===== 4. OLDEST tie-break among RD candidates =====
    # banks 1 and 6 both RD-hit; slot 7 (bank 6) older (higher rel age) -> wins.
    tb._drive_idle(); dut.init_done_i.value = 1
    tb.set_bank_bits(dut.bank_row_active_i, {1: 1, 6: 1})
    tb.set_bank_bits(dut.bank_rdwr_ready_i, {1: 1, 6: 1})
    tb.set_open_rows({1: 0x11, 6: 0x66})
    tb.set_entries('rd', {3: (1, 0x11, 0x08, 20), 7: (6, 0x66, 0x09, 55)})
    await tb.settle()
    p = tb.picked(); s = tb.strobes()
    assert p['op'] == OP_RD and p['bank'] == 6 and s['rd_issue_slot'] == 7, \
        f"oldest tie-break should pick bank6 slot7 (age55): {p} {s}"

    # ===== 5. WRITE pick when no RD candidate =====
    tb._drive_idle(); dut.init_done_i.value = 1
    tb.set_bank_bits(dut.bank_row_active_i, {4: 1})
    tb.set_bank_bits(dut.bank_rdwr_ready_i, {4: 1})
    tb.set_open_rows({4: 0x222})
    tb.set_entries('wr', {5: (4, 0x222, 0x1C, 30)})
    await tb.settle()
    p = tb.picked(); s = tb.strobes()
    assert p['op'] == OP_WR and p['bank'] == 4 and p['col'] == 0x1C, f"write pick: {p}"
    assert s['wr'] == 1 and s['wr_commit'] == 1 and s['wr_commit_slot'] == 5, f"wr commit: {s}"

    # ===== 6. CLOSE policy -> auto-precharge (WRA/ap) =====
    dut.page_policy_i.value = PAGE_CLOSE
    await tb.settle()
    p = tb.picked()
    assert p['ap'] == 1 and p['op'] == 0x5, f"CLOSE policy should emit WRA (ap=1): {p}"
    dut.page_policy_i.value = PAGE_OPEN

    # ===== 7. ACTIVATE the pending op's idle bank (no row open yet) =====
    tb._drive_idle(); dut.init_done_i.value = 1
    tb.set_bank_bits(dut.bank_act_ready_i, {2: 1})
    # a pending read in an idle (not row_active) bank -> arbiter ACTs it.
    tb.set_entries('rd', {0: (2, 0x333, 0x00, 40)})
    await tb.settle()
    p = tb.picked(); s = tb.strobes()
    assert p['op'] == OP_ACT and p['bank'] == 2 and p['row'] == 0x333, f"ACT idle bank: {p}"
    assert s['act'] == 1, f"act strobe: {s}"

    # ===== 8. cmd_ready backpressure: pick shown, but NO side-effect strobes =====
    dut.cmd_ready_i.value = 0
    await tb.settle()
    p = tb.picked(); s = tb.strobes()
    assert p['valid'] == 1 and p['op'] == OP_ACT, "pick still presented under backpressure"
    assert s['act'] == 0, "evt_act must NOT fire while cmd_ready low"
    dut.cmd_ready_i.value = 1

    # ===== 9. 1-CMD/CLOCK: columns issue on CONSECUTIVE cycles (no throttle) =====
    # Two RD hits on different banks; retire each as it issues (mocking the CAM's
    # exclude-on-issue). The 2-stage output pipeline throttles columns to
    # every-other cycle (the in-flight forward-mask — free, since tCCD already
    # spaces columns >= 2 apart), so both must issue OLDEST-FIRST across cycles,
    # not necessarily back-to-back.
    tb._drive_idle(); dut.init_done_i.value = 1
    tb.set_bank_bits(dut.bank_row_active_i, {1: 1, 6: 1})
    tb.set_bank_bits(dut.bank_rdwr_ready_i, {1: 1, 6: 1})
    tb.set_open_rows({1: 0x11, 6: 0x66})
    dut.cmd_ready_i.value = 1
    fired = []
    live = {3: (1, 0x11, 0x08, 20), 7: (6, 0x66, 0x09, 55)}  # slot -> entry tuple
    for _ in range(8):
        tb.set_entries('rd', dict(live))
        await tb.settle()
        s = tb.strobes()
        if s['rd'] and s['rd_issue_slot'] in live:
            fired.append(tb.picked()['bank'])
            live.pop(s['rd_issue_slot'], None)   # retire the issued slot
        await RisingEdge(dut.aclk)
    assert fired == [6, 1], \
        f"columns must issue oldest-first (bank6 then bank1): got {fired}"

    # ===== 10. BANK-PARALLEL activate: ACT DIFFERENT idle banks (oldest first) =====
    # The bubble fix: two pending ops in different idle banks must both get ACTed
    # (their tRCDs overlap) instead of the arbiter stalling on one bank. Mock the
    # timers: an ACTed bank becomes row_active on the next cycle.
    tb._drive_idle(); dut.init_done_i.value = 1
    tb.set_bank_bits(dut.bank_act_ready_i, {2: 1, 3: 1})
    tb.set_entries('rd', {0: (2, 0x333, 0x00, 20), 1: (3, 0x444, 0x00, 55)})
    dut.cmd_ready_i.value = 1
    acts = []
    for _cyc in range(8):
        # Registered bank state: banks ACTed in prior cycles are row_active now.
        # Apply at cycle start so it is stable through the settle window (like the
        # real bank_timers) — never mutate a registered-state mock mid-cycle.
        tb.set_bank_bits(dut.bank_row_active_i, {b: 1 for b in acts})
        await tb.settle()
        p = tb.picked(); s = tb.strobes()
        if s['act'] and p['bank'] not in acts:
            acts.append(p['bank'])
        await RisingEdge(dut.aclk)
    assert acts == [3, 2], \
        f"bank-parallel: ACT both idle banks, oldest(3) first: got {acts}"

    tb.log.info("PASS: init, refresh(PRE->REF+grant), read-priority, oldest "
                "tie-break, write pick, CLOSE auto-PRE, ACT idle bank, backpressure, "
                "columns oldest-first (pipelined), bank-parallel activate")


def test_pumice_cmd_arbiter(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_cmd_arbiter"
    test_name = "cocotb_test_pumice_cmd_arbiter"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14", "COL_WIDTH": "10",
        "AXI_ID_WIDTH": "8", "NUM_ENTRIES": "8",
    }
    extra_env = {
        "DUT": dut_name, "LOG_PATH": log_path, "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path, "SEED": str(random.randint(0, 100000)),
    }
    extra_env.update(params)
    compile_args = ["+define+USE_ASYNC_RESET"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_cmd_arbiter",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))), keep_files=True, timescale="1ns/1ps",
    )
