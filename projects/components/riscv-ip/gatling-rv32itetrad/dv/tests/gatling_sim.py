# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gatling_sim
# Purpose: Shared plumbing for the gatling test files: the import paths both
#          the pytest process and the cocotb sim process need, and the one
#          cocotb_test.run() call every wrapper makes.
#
# Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32itetrad
#
# Created: 2026-10-21

"""Paths and the simulator call for gatling's cocotb cells.

Import paths: gatling's TB classes are imported as ``gatling.*`` (this
area's ``dv/tbclasses`` is the path entry), kestrel's as ``tbclasses.
kestrel.*`` (kestrel's ``dv`` is the path entry) -- gatling's golden
interpreter, rv32ui battery helpers and fuzz generator are kestrel's.  Both
packages are named for their directory, so neither shadows the other.
``setup_paths()`` runs on import, so the cocotb process (which imports the
test module, not conftest) gets the same view.
"""

import os
import sys
from pathlib import Path

_TESTS = Path(__file__).resolve().parent
_GATLING_DV = _TESTS.parent
_REPO = Path(os.environ.get("REPO_ROOT", str(_TESTS.parents[5])))
_KESTREL_DV = _REPO / "projects/components/riscv-ip/kestrel-rv32i/dv"

PATHS = (
    _GATLING_DV / "tbclasses",
    _KESTREL_DV,
    _KESTREL_DV / "tests" / "programs",     # normalize_hex, kestrel's directed images
    _TESTS,
)
KESTREL_PROGRAMS = _KESTREL_DV / "tests" / "programs"


def setup_paths():
    for p in PATHS:
        if str(p) not in sys.path:
            sys.path.insert(0, str(p))


setup_paths()

TB_FILELIST = "projects/components/riscv-ip/gatling-rv32itetrad/dv/filelists/gatling_tb.f"

COMPILE_ARGS = [
    "--trace", "--trace-structs", "--trace-depth", "99",
    "--timescale", "1ns/1ps",
    "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
]


def run_cell(module, testcase, toplevel, filelist, cell, test_level,
             parameters=None, extra_env=None):
    """One Verilator build + run for (testcase, level); ``cell`` names the
    build directory and the log."""
    from cocotb_test.simulator import run
    from TBClasses.shared.filelist_utils import get_sources_from_filelist
    from TBClasses.shared.test_levels import level_env
    from TBClasses.shared.utilities import get_paths, sim_build_path

    _, repo_root, tests_dir, log_dir, _ = get_paths({})
    log_path = os.path.join(log_dir, f"{cell}.log")
    sim_build = sim_build_path(tests_dir, cell)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist)
    env = {
        "DUT": toplevel,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{cell}.xml"),
        "REPO_ROOT": str(repo_root),
        **level_env(test_level),
        **(extra_env or {}),
    }
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=toplevel,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        extra_env=env,
        parameters=parameters or {},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=COMPILE_ARGS,
    )
