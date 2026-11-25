# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_battery
# Purpose: riscv-tests batteries on peregrine_core: rv32ui (42 images),
#          rv32mi (machine-mode traps and CSRs) and rv32um (the M unit, on
#          both MUL_DSP builds).  Gate runs a smoke subset per suite; func
#          and full run every image with spike lockstep.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""peregrine riscv-tests batteries (TASK-001 stages 1-2: traps, M unit, cacheless)."""

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

# Suite -> spike ISA string.  peregrine is RV32IM, and its misa says so, so
# spike runs every suite as rv32im: an rv32mi test that reads misa must see
# the same M bit on both sides of the lockstep.
SUITES = {
    "rv32ui": "rv32im_zicsr_zifencei",
    "rv32mi": "rv32im_zicsr_zifencei",
    "rv32um": "rv32im_zicsr_zifencei",
}


async def _battery(dut, suite):
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    dsp = "_dsp" if os.environ.get("MUL_DSP", "0") == "1" else ""
    # Per level: the gate/func/full cells of one suite run in parallel and
    # would otherwise overwrite each other's spike logs (measured: a FULL
    # run's rv32um div failed lockstep on a log the func cell rewrote).
    work_dir = os.path.join(os.path.dirname(os.environ.get("LOG_PATH", ".")),
                            f"{suite}{dsp}_battery_{level}")
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


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_peregrine_rv32um(dut):
    """rv32um-p-*: the eight M operations, spike lockstep at func."""
    await _battery(dut, "rv32um")


# (cocotb test, MUL_DSP).  rv32um runs on both multiply builds; the other
# suites do not exercise the M unit and run on the default.
CASES = [("cocotb_test_peregrine_rv32ui", 0),
         ("cocotb_test_peregrine_rv32mi", 0),
         ("cocotb_test_peregrine_rv32um", 0),
         ("cocotb_test_peregrine_rv32um", 1)]


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_battery {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase, mul_dsp", CASES)
def test_peregrine_battery(request, cocotb_testcase, mul_dsp, test_level, description):
    """Pytest wrapper: one Verilator build per (case, MUL_DSP, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"{cocotb_testcase}{'_dsp' if mul_dsp else ''}_{test_level}"
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
            "MUL_DSP": str(mul_dsp),
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"RESET_ADDR": str(LINK_BASE), "MUL_DSP": str(mul_dsp)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
