# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_merlin_rv32ui
# Purpose: Full riscv-tests rv32ui-p-* battery for merlin_core: gate runs the
#          simple/add/addi smoke subset, func runs all 42 with the golden
#          interpreter full-field diff and spike (pc, insn) lockstep.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/merlin-rv32i
#
# Author: sean galloway
# Created: 2026-11-01

"""merlin-rv32i rv32ui battery tests.

The battery discovers every ``vendor/riscv-tests/isa/rv32ui-p-*.hex`` image
and loads it through the TB top's backdoor port.  Kestrel's normalize_hex.py
is reused (on sys.path from kestrel-rv32i/dv/tests/programs) to parse the
vendor byte-addressed hex dumps.
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

# Reuse kestrel's normalize_hex.py for the vendor byte-addressed images.
_KESTREL_PROGRAMS_DIR = (
    Path(__file__).resolve().parents[4] / "kestrel-rv32i" / "dv" / "tests" / "programs"
)
if str(_KESTREL_PROGRAMS_DIR) not in sys.path:
    sys.path.insert(0, str(_KESTREL_PROGRAMS_DIR))

from tbclasses.merlin.merlin_tb import MerlinTB                      # noqa: E402
from tbclasses.merlin.merlin_tb import RV32IInterpreter              # noqa: E402
from tbclasses.merlin.rv32ui_battery import (                        # noqa: E402
    LINK_BASE,
    RV32UIBattery,
)


async def _battery(dut):
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    work_dir = os.path.join(log_dir, "rv32ui_battery")
    battery = RV32UIBattery(dut, repo_root=repo_root, level=level,
                            work_dir=work_dir)
    await battery.run()


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_merlin_rv32ui_battery(dut):
    """All 42 rv32ui-p-* images: tohost pass/fail + spike lockstep."""
    await _battery(dut)


# ---------------------------------------------------------------------------
# pytest wrapper
# ---------------------------------------------------------------------------

CASES = {
    "cocotb_test_merlin_rv32ui_battery": LINK_BASE,
}


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"merlin_rv32ui {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_merlin_rv32ui(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    reset_addr = CASES[cocotb_testcase]

    test_name_plus_params = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{test_name_plus_params}.log")
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name_plus_params}.xml")

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/merlin-rv32i/dv/filelists/merlin_tb.f",
    )

    extra_env = {
        "DUT": "merlin_tb_top",
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        **level_env(test_level),
    }

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="merlin_tb_top",
        module=module,
        testcase=cocotb_testcase,
        sim_build=sim_build,
        extra_env=extra_env,
        parameters={"RESET_ADDR": str(reset_addr)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
