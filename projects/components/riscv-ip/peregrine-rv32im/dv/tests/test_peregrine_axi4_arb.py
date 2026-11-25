# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_axi4_arb
# Purpose: peregrine_axi4_arb unit test (PRD P7, TASK-001 stage 4).
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_axi4_arb: three concurrent masters onto one fabric port.

  gate -- 40 random bursts per master, zero-delay fabric
  func -- 300 per master, a slow fabric with random ready/valid delays and
          out-of-order, beat-interleaved R across ids
  full -- 1500 per master, same
Every read burst is checked against the issuing master's model; the
monitor checks R/B routing by id and that W follows the AW grant order.
"""

import os
import sys
from pathlib import Path

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = str(Path(__file__).resolve().parents[1])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.peregrine.axi4_arb_tb import NM, Axi4ArbTB    # noqa: E402

OPS = {"gate": 40, "func": 300, "full": 1500}


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_peregrine_axi4_arb(dut):
    level = os.environ.get("TEST_LEVEL", "gate")
    seed = int(os.environ.get("RDS_SEED_BASE", "1"))
    tb = Axi4ArbTB(dut, seed=seed)
    if level != "gate":
        tb.set_slow()
        tb.srd["interface"].enable_ooo = True
        tb.srd["interface"].interleave_r = True
    await tb.setup_clocks_and_reset()
    jobs = [cocotb.start_soon(tb.master_traffic(m, OPS[level])) for m in range(NM)]
    checked = 0
    for j in jobs:
        checked += await j
    for _ in range(20):
        await RisingEdge(dut.clk)
    dut._log.info(f"seed {seed}: {checked} read beats checked; per master "
                  f"AR {tb.counts['ar']} R {tb.counts['r']} AW {tb.counts['aw']} "
                  f"B {tb.counts['b']}")
    assert tb.counts["ar"] == tb.counts["r"], "a read burst never completed"
    assert tb.counts["aw"] == tb.counts["b"], "a write never got its B"
    assert not tb.w_owner, f"W owed at the end: {tb.w_owner}"
    assert all(c > 0 for c in tb.counts["ar"] + tb.counts["aw"]), "a master never got through"
    assert checked > 0


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_axi4_arb {lvl}") for lvl in reg_level_grid()])
def test_peregrine_axi4_arb(request, test_level, description):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_axi4_arb_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/dv/filelists/peregrine_axi4_arb_th.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_axi4_arb_th",
        module=module,
        testcase="cocotb_test_peregrine_axi4_arb",
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_axi4_arb_th",
            "LOG_PATH": log_path,
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"AXI_DW": "64", "AXI_IW": "4"},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
