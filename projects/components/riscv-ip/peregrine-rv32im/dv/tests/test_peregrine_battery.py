# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_battery
# Purpose: riscv-tests batteries on peregrine_core: rv32ui (42 images) and
#          rv32mi (machine-mode traps and CSRs).  Gate runs a smoke subset
#          per suite; func and full run every image with spike lockstep.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""peregrine riscv-tests batteries (TASK-001 stage 1: traps, cacheless)."""

import os
import sys
from pathlib import Path

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = str(Path(__file__).resolve().parents[1])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.peregrine.battery import LINK_BASE, Battery      # noqa: E402
from tbclasses.peregrine.peregrine_tb import PeregrineTB        # noqa: E402

# Suite -> spike ISA string.
SUITES = {
    "rv32ui": "rv32i_zicsr_zifencei",
    "rv32mi": "rv32i_zicsr_zifencei",
}


async def _battery(dut, suite):
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    work_dir = os.path.join(os.path.dirname(os.environ.get("LOG_PATH", ".")),
                            f"{suite}_battery")
    tb = PeregrineTB(dut, reset_addr=LINK_BASE)
    await tb.ensure_clock()
    await Battery(tb, repo_root, suite, SUITES[suite], level, work_dir).run()


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_peregrine_rv32ui(dut):
    """rv32ui-p-*: tohost == 1 on every image, spike lockstep at func."""
    await _battery(dut, "rv32ui")


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_peregrine_rv32mi(dut):
    """rv32mi-p-*: machine-mode traps and CSRs, spike lockstep at func."""
    await _battery(dut, "rv32mi")


CASES = ["cocotb_test_peregrine_rv32ui", "cocotb_test_peregrine_rv32mi"]


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_battery {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", CASES)
def test_peregrine_battery(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/dv/filelists/peregrine_tb.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_tb_top",
        module=module,
        testcase=cocotb_testcase,
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_tb_top",
            "LOG_PATH": log_path,
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"RESET_ADDR": str(LINK_BASE)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
