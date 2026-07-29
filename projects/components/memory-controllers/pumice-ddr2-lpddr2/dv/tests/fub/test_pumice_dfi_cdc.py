# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B dual-clock runner for `pumice_dfi_cdc`."""

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
from tbclasses.pumice_dfi_cdc_tb import PumiceDfiCdcTB  # noqa: E402

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_dfi_cdc.f")


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_pumice_dfi_cdc(dut):
    tb = PumiceDfiCdcTB(dut)
    await tb.start(ctl_ns=10, dfi_ns=4)   # asynchronous, different rates
    rng = random.Random(int(os.environ.get("SEED", "1")))

    n = 24
    cmds = [rng.randrange(1 << tb.CMD_DW) for _ in range(n)]
    wds  = [rng.randrange(1 << tb.WD_DW) for _ in range(n)]
    rds  = [rng.randrange(1 << tb.RD_DW) for _ in range(n)]

    # ctl -> phy: cmd + wrdata concurrently
    c = cocotb.start_soon(tb.push_cmd(cmds))
    w = cocotb.start_soon(tb.push_wd(wds))
    # phy -> ctl: rddata
    r = cocotb.start_soon(tb.push_rd(rds))
    await c
    await w
    await r

    # drain
    for _ in range(2000):
        if (len(tb.cmd_seen) >= n and len(tb.wd_seen) >= n and len(tb.rd_seen) >= n):
            break
        await RisingEdge(dut.ctl_clk)

    assert list(tb.cmd_seen) == cmds, \
        f"cmd CDC mismatch: got {len(tb.cmd_seen)} items, first diff vs golden"
    assert list(tb.wd_seen) == wds, "wrdata CDC mismatch (lossy/reordered)"
    assert list(tb.rd_seen) == rds, "rddata CDC mismatch (lossy/reordered)"

    # ---- init tokens: level -> token -> sticky latch, across the boundary ----
    assert int(dut.pinit_start_o.value) == 0, "pinit_start high before start"
    dut.init_start_i.value = 1
    for _ in range(20):
        await RisingEdge(dut.dfi_clk)
        if int(dut.pinit_start_o.value):
            break
    assert int(dut.pinit_start_o.value) == 1, "init_start token did not cross ctl->phy"

    assert int(dut.init_complete_o.value) == 0, "init_complete high before complete"
    dut.pinit_complete_i.value = 1
    for _ in range(20):
        await RisingEdge(dut.ctl_clk)
        if int(dut.init_complete_o.value):
            break
    assert int(dut.init_complete_o.value) == 1, "init_complete token did not cross phy->ctl"

    tb.log.info(f"PASS: {n} cmd + {n} wrdata (ctl->phy) + {n} rddata (phy->ctl) "
                "lossless in-order across async clocks; init_start/complete tokens latched")


def test_pumice_dfi_cdc(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_dfi_cdc"
    test_name = "cocotb_test_pumice_dfi_cdc"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {
        "CMD_DW": "32", "WD_DW": "72", "RD_DW": "66",
        "CMD_DEPTH": "8", "WD_DEPTH": "16", "RD_DEPTH": "16", "TOK_DEPTH": "4",
        "N_FLOP_CROSS": "2",
    }
    extra_env = {
        "DUT": dut_name, "LOG_PATH": log_path, "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path, "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    extra_env.update(params)
    compile_args = ["+define+USE_ASYNC_RESET"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir], verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module, testcase="cocotb_test_pumice_dfi_cdc",
        sim_build=sim_build, simulator="verilator", extra_env=extra_env,
        parameters=params, compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))), keep_files=True, timescale="1ns/1ps",
    )
