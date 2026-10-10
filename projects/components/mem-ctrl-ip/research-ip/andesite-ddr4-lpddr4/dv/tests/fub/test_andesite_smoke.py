# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Infra smoke test -- proves the andesite cocotb + verilator pipeline.

The assertion set is tiny on purpose: if reset holds the output at 0 and five
clocks after release it is 1, then filelists, dispatchers, the pytest runner,
and the verilator build all work. Every later test in this tree rides on this.
"""

import os
import random
import sys

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.andesite_smoke_tb import AndesiteSmokeTB  # noqa: E402


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_andesite_smoke(dut):
    tb = AndesiteSmokeTB(dut)
    await tb.setup_clock()

    # Reset holds the output at 0.
    dut.rst_n.value = 0
    for _ in range(3):
        await tb.tick()
    assert dut.op_o.value == 0, "reset must clear op_o"

    # Five clocks after release the registered constant has arrived.
    await tb.reset()
    await tb.tick(5)
    assert dut.op_o.value == 1, "op_o must be OP_ACT (5'h01) five clocks after reset release"


@pytest.mark.parametrize("seed", [None])
def test_andesite_smoke(seed):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_smoke"
    test_name = "test_andesite_smoke"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_smoke.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_smoke",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
