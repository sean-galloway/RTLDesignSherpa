# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_clint
# Purpose: peregrine_clint unit test (PRD P7, TASK-001 stage 4).
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_clint against a cycle model.

Directed (every level): reset values, mtime counting, msip set/clear,
mtimecmp crossing in both directions, byte strobes, an unmapped offset.
Random (func: 4000 cycles, full: 40000), at MTIME_DIV 1 and 3 (two
builds): random reads and writes; every cycle compares the response and
both interrupt outputs with the model.
"""

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

from tbclasses.peregrine.clint_tb import (CMP_HI, CMP_LO, MSIP, TIME_HI,  # noqa: E402
                                          TIME_LO, ClintTB)

CYCLES = {"gate": 0, "func": 4000, "full": 40000}


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_peregrine_clint(dut):
    level = os.environ.get("TEST_LEVEL", "gate")
    seed = int(os.environ.get("RDS_SEED_BASE", "1"))
    div = int(os.environ.get("MTIME_DIV", "1"))
    tb = ClintTB(dut, div=div, seed=seed)
    await tb.setup_clocks_and_reset()

    m = tb.model
    for _ in range(3):
        await tb.step()
    await tb.step((TIME_LO, 0, 0xF, 0))
    await tb.step((CMP_LO, 0, 0xF, 0))
    await tb.step((CMP_HI, 0, 0xF, 0))
    assert m.cmp == (1 << 64) - 1 and m.msip == 0
    await tb.step((MSIP, 1, 0x1, 1))
    await tb.step()
    assert int(dut.irq_software.value) == 1
    await tb.step((MSIP, 1, 0x1, 0))
    await tb.step()
    # mtimecmp = mtime + 10, hi first: the timer fires, then disarm
    await tb.step((CMP_HI, 1, 0xF, 0))
    await tb.step((CMP_LO, 1, 0xF, (m.time + 10) & 0xFFFF_FFFF))
    fired = False
    for _ in range(40 * div):
        await tb.step()
        fired = fired or bool(int(dut.irq_timer.value))
    assert fired, "the timer never fired"
    await tb.step((CMP_HI, 1, 0xF, 0xFFFF_FFFF))
    await tb.step()
    await tb.step()
    assert int(dut.irq_timer.value) == 0, "the timer did not clear"
    # byte strobes on mtime high, an unmapped offset
    await tb.step((TIME_HI, 1, 0x4, 0x00AB_0000))
    await tb.step((TIME_HI, 0, 0xF, 0))
    await tb.step((0x0010, 1, 0xF, 0xDEAD_BEEF))
    await tb.step((0x0010, 0, 0xF, 0))

    for _ in range(CYCLES[level]):
        await tb.step(tb.random_req())
    dut._log.info(f"MTIME_DIV {div}, seed {seed}: {tb.checks} cycles compared with the model")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_clint {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("mtime_div", [1, 3])
def test_peregrine_clint(request, mtime_div, test_level, description):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_clint_div{mtime_div}_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/fub/peregrine_clint.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_clint",
        module=module,
        testcase="cocotb_test_peregrine_clint",
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_clint",
            "LOG_PATH": log_path,
            "MTIME_DIV": str(mtime_div),
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"MTIME_DIV": str(mtime_div)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
