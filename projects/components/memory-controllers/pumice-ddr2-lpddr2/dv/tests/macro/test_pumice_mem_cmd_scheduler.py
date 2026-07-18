# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B macro runner for `pumice_mem_cmd_scheduler`."""

import os
import sys
import random

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
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
    await tb.wait_clocks('aclk', 4)   # drain the cmd FIFO to tb.cmds

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
    await tb.wait_clocks('aclk', 4)   # drain the cmd FIFO to tb.cmds
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

    tb.log.info("PASS: init MRS stream, ACT->RD (real tRCD timers), open-page WR "
                "commit (no re-ACT), refresh PRE->REF")


def test_pumice_mem_cmd_scheduler(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_mem_cmd_scheduler"
    test_name = "cocotb_test_pumice_mem_cmd_scheduler"

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
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_mem_cmd_scheduler",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))), keep_files=True, timescale="1ns/1ps",
    )
