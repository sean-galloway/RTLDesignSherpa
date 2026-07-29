# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Pattern-B runner for `pumice_bank_timers` (open-page per-bank safe timers)."""

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
from tbclasses.pumice_bank_timers_tb import (  # noqa: E402
    PumiceBankTimersTB, BANK_ACTIVE, BANK_IDLE, BANK_PRECHARGING,
)

_FILELIST = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
             "rtl/filelists/fub/pumice_bank_timers.f")


@cocotb.test(timeout_time=3, timeout_unit="ms")
async def cocotb_test_pumice_bank_timers(dut):
    tb = PumiceBankTimersTB(dut)
    await tb.setup_clocks_and_reset()

    # --- 1. ACT -> tRCD -> rdwr_ready; open_row captured ---
    assert tb.act_ready(2) == 1, "bank should be ACT-ready at idle"
    await tb.act(2, 0x123)
    await tb.wait_clocks('aclk', 2)
    assert tb.rdwr_ready(2) == 0, "rdwr_ready high before tRCD"
    assert tb.act_ready(2) == 0, "act_ready high while activating"
    await tb.wait_clocks('aclk', tb.T_RCD + 2)
    assert tb.state(2) == BANK_ACTIVE, f"bank2 state {tb.state(2)} != ACTIVE"
    assert tb.rdwr_ready(2) == 1, "rdwr_ready not set after tRCD"
    assert tb.open_row(2) == 0x123, f"open_row {tb.open_row(2):#x} != 0x123"

    # --- 2. OPEN-PAGE: column commands keep rdwr_ready HIGH ---
    for k in range(4):
        await tb.rd(2, ap=0)
        await tb.wait_clocks('aclk', 3)
        assert tb.rdwr_ready(2) == 1, \
            f"rdwr_ready dropped after RD #{k} (open-page streaming broken)"
        assert tb.state(2) == BANK_ACTIVE, f"bank left ACTIVE after RD #{k}"
    await tb.wr(2, ap=0)
    await tb.wait_clocks('aclk', 3)
    assert tb.rdwr_ready(2) == 1, "rdwr_ready dropped after WR (open-page)"

    # --- 3. pre_ready gated by tWR (preblk) then allowed ---
    await tb.wr(2, ap=0)
    await tb.wait_clocks('aclk', 2)
    assert tb.pre_ready(2) == 0, "pre_ready high during tWR window"
    await tb.wait_clocks('aclk', tb.T_WR + 3)
    assert tb.pre_ready(2) == 1, "pre_ready not set after tWR (+tRAS long elapsed)"

    # --- 4. explicit PRE -> tRP -> IDLE + act_ready (tRC long elapsed) ---
    await tb.pre(2)
    await tb.wait_clocks('aclk', 2)
    assert tb.state(2) == BANK_PRECHARGING, "bank not PRECHARGING after PRE"
    await tb.wait_clocks('aclk', tb.T_RP + 3)
    assert tb.state(2) == BANK_IDLE, f"bank2 state {tb.state(2)} != IDLE after tRP"
    assert tb.act_ready(2) == 1, "act_ready not set after tRP/tRC"

    # --- 5. auto-precharge (RDA): no explicit PRE, bank returns to IDLE ---
    await tb.act(5, 0x55)
    await tb.wait_clocks('aclk', tb.T_RCD + 2)
    assert tb.rdwr_ready(5) == 1
    await tb.rd(5, ap=1)                 # RDA
    await tb.wait_clocks('aclk', 2)
    assert tb.rdwr_ready(5) == 0, "rdwr_ready high during auto-precharge pending"
    # wait for internal auto-PRE (tRTP/tRAS) + tRP
    await tb.wait_clocks('aclk', tb.T_RAS + tb.T_RP + 6)
    assert tb.state(5) == BANK_IDLE, f"bank5 state {tb.state(5)} != IDLE after RDA auto-PRE"
    assert tb.act_ready(5) == 1, "bank5 not ACT-ready after auto-precharge"

    tb.log.info("PASS: tRCD gate, open-page column streaming, pre gating, "
                "explicit PRE tRP/tRC, auto-precharge return-to-idle")


def test_pumice_bank_timers(request):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_bank_timers"
    test_name = "cocotb_test_pumice_bank_timers"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=_FILELIST
    )
    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    params = {"NUM_RANKS": "1", "NUM_BANKS": "8", "ROW_WIDTH": "14"}
    extra_env = {
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
    }
    extra_env.update(params)

    compile_args = ["+define+USE_ASYNC_RESET"] + get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_pumice_bank_timers",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=params,
        compile_args=compile_args,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        timescale="1ns/1ps",
    )
