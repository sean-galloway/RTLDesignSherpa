# SPDX-License-Identifier: MIT
"""Isolated arbiter column ISSUE-RATE probe (PUMICE-PERF Phase 1).
8 ready row-hit reads across 8 banks, cmd_ready high, tCCD ok -> count
cmd_valid_o fires/cycle. Blanket mask caps at ~1/4; per-entry -> ~1/cycle."""
import os, sys
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
_DV = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV not in sys.path: sys.path.insert(0, _DV)
from tbclasses.pumice_cmd_arbiter_tb import PumiceCmdArbiterTB  # noqa: E402
_FL = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
       "rtl/filelists/fub/pumice_cmd_arbiter.f")

@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_arbiter_issue_rate(dut):
    tb = PumiceCmdArbiterTB(dut)
    await tb.setup_clocks_and_reset()
    dut.init_done_i.value = 1
    tb.set_bank_bits(dut.bank_row_active_i,  {b: 1 for b in range(8)})
    tb.set_bank_bits(dut.bank_rdwr_ready_i,  {b: 1 for b in range(8)})
    tb.set_bank_bits(dut.bank_act_ready_i,   {b: 1 for b in range(8)})
    tb.set_open_rows({b: 0x100 + b for b in range(8)})
    tb.set_entries('rd', {e: (e, 0x100 + e, e * 4, 8 - e) for e in range(8)})  # 8 banks, row-hit
    tb.set_cmd_ready(True)
    for _ in range(8):        # settle the pipeline
        await RisingEdge(dut.aclk)
    K, fires = 200, 0
    for _ in range(K):
        await RisingEdge(dut.aclk)
        if int(dut.cmd_valid_o.value) and int(dut.cmd_ready_i.value):
            fires += 1
    rate = fires / K
    dut._log.info("ISSUE RATE: %d fires / %d cyc = %.3f fires/cycle", fires, K, rate)
    with open("issue_rate.out", "w") as f:
        f.write(f"fires {fires}\ncycles {K}\nrate {rate:.4f}\n")
    # 1.0 = one column per cycle with the pick pipeline full (design/waves/07).
    # ~0.5 = the per-bank occupancy mask (w_col_inflight_bank) applied to
    # OPEN-policy columns, which it does not guard. Mutation check: make the
    # mask unconditional again -> 0.5 -> RED here.
    assert rate >= 0.95, f"issue rate {rate:.3f} < 0.95 -- same-bank columns not pipelining at tCCD"

def test_pumice_arbiter_issue_rate(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_cmd_arbiter"
    tn = "cocotb_test_arbiter_issue_rate"
    vs, inc = get_sources_from_filelist(repo_root=repo_root, filelist_path=_FL)
    sb = sim_build_path(tests_dir, tn); os.makedirs(sb, exist_ok=True)
    params = {"NUM_RANKS":"1","NUM_BANKS":"8","ROW_WIDTH":"14","COL_WIDTH":"10","AXI_ID_WIDTH":"8","NUM_ENTRIES":"8"}
    env = {"DUT":dut_name,"NUM_BANKS":"8","NUM_ENTRIES":"8","COCOTB_LOG_LEVEL":"INFO"}
    env.update(params)
    run(python_search=[tests_dir], verilog_sources=vs, includes=inc, toplevel=dut_name,
        module="test_pumice_arbiter_issue_rate", testcase=tn, sim_build=sb, simulator="verilator",
        extra_env=env, parameters=params, compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
