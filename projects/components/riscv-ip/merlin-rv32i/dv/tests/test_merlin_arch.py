# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_merlin_arch
# Purpose: riscv-arch-test 3.10.0 rv32i_m/I on merlin_core: each test's
#          signature region, read from the TB memory after the ecall halt,
#          against the RISCOF reference signature (spike and Sail agree).
#
# Documentation: vault/handbook/dv/riscv-arch-test.md
# Subsystem: riscv-ip/merlin-rv32i
#
# Author: sean galloway
# Created: 2026-11-22

"""merlin-rv32i riscv-arch-test signature compare.

The build, the spike and Sail references and the compare are the shared
``common-rv32i/dv/arch_test/rv32_arch_test.py``; this file is the merlin
harness: MerlinTB on merlin_tb_top with a 2 MiB memory (jal-01 is a
1.7 MiB image).  Gate runs add-01, lw-align-01 and sw-align-01; func and
full run all 39 rv32i_m/I tests.
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
_ARCH_DIR = str(Path(__file__).resolve().parents[3] / "common-rv32i" / "dv" / "arch_test")
if _ARCH_DIR not in sys.path:
    sys.path.insert(0, _ARCH_DIR)

from rv32_arch_test import LINK_BASE, run_flat                    # noqa: E402
from tbclasses.merlin.merlin_tb import MerlinTB                # noqa: E402

MEM_WORDS = 1 << 19          # 2 MiB
# The longest test retires under 7,000 instructions; merlin CPI is about 1.2.
MAX_CYCLES = 80_000


@cocotb.test(timeout_time=3000, timeout_unit="sec")
async def cocotb_test_merlin_arch(dut):
    """All rv32i_m/I arch tests: ecall halt + signature == the reference's (spike == Sail)."""
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    work_dir = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"arch_test_{level}"
    tb = MerlinTB(dut, reset_addr=LINK_BASE)
    await run_flat(dut, tb, "merlin", repo_root, level, work_dir,
                   MEM_WORDS, MAX_CYCLES)


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"merlin_arch {lvl}") for lvl in reg_level_grid()])
def test_merlin_arch(request, test_level, description):
    """Pytest wrapper: one Verilator build per level."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    test_name_plus_params = f"cocotb_test_merlin_arch_{test_level}"
    log_path = os.path.join(log_dir, f"{test_name_plus_params}.log")
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name_plus_params}.xml")

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/merlin-rv32i/dv/filelists/merlin_tb.f",
    )

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="merlin_tb_top",
        module=module,
        testcase="cocotb_test_merlin_arch",
        sim_build=sim_build,
        extra_env={
            "DUT": "merlin_tb_top",
            "LOG_PATH": log_path,
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": results_path,
            **level_env(test_level),
        },
        parameters={"RESET_ADDR": str(LINK_BASE), "MEM_WORDS": str(MEM_WORDS)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
