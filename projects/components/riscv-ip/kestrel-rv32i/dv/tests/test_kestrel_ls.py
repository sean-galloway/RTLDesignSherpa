# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_ls
# Purpose: Golden-trace lockstep tests for kestrel_core loads and stores.
#          Covers aligned size/sign loads after word/halfword/byte stores,
#          in-word rotated-strobe misaligned vectors, and a store-then-load
#          dependent chain that pins the single-cycle memory semantics.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""kestrel_core load/store golden-trace tests."""

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

from tbclasses.kestrel.kestrel_tb import KestrelTB                  # noqa: E402
from tbclasses.kestrel.rv32i_interpreter import (                   # noqa: E402
    RV32IInterpreter,
    load_verilog_hex,
)

PROGRAMS_DIR = Path(__file__).resolve().parent / "programs"

CASES = {
    "cocotb_test_kestrel_ls_basic":
        ("ls_basic.hex", 0x0000_0000),
    "cocotb_test_kestrel_ls_misaligned":
        ("ls_misaligned.hex", 0x0000_0000),
    "cocotb_test_kestrel_ls_chain":
        ("ls_chain.hex", 0x0000_0000),
}


async def _run_case(dut, hex_name, reset_addr):
    imem_words = load_verilog_hex(PROGRAMS_DIR / hex_name)
    golden = RV32IInterpreter(imem_words, reset_addr=reset_addr)
    golden.run()

    tb = KestrelTB(dut, reset_addr=reset_addr)
    await tb.run()

    tb.check_halt(expected_cause=1, expected_halt_pc=golden.halt_pc)
    tb.check_first_pc()
    tb.check_order_sequence()
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)
    dut._log.info(
        f"{hex_name}: {len(tb.trace)} beats retired, "
        "trace matches golden model")
    return tb


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_kestrel_ls_basic(dut):
    """Aligned loads of every size/sign after word/halfword/byte stores."""
    await _run_case(dut, "ls_basic.hex", 0x0000_0000)


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_kestrel_ls_misaligned(dut):
    """Review Focus 6: in-word rotated-strobe misaligned accesses."""
    await _run_case(dut, "ls_misaligned.hex", 0x0000_0000)


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_kestrel_ls_chain(dut):
    """Store-then-load dependent chain (single-cycle memory visibility)."""
    await _run_case(dut, "ls_chain.hex", 0x0000_0000)


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"kestrel_ls {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_kestrel_ls(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    hex_name, reset_addr = CASES[cocotb_testcase]
    hex_path = os.path.join(PROGRAMS_DIR, hex_name)

    test_name_plus_params = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{test_name_plus_params}.log")
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name_plus_params}.xml")

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/kestrel-rv32i/dv/filelists/kestrel_tb.f",
    )

    extra_env = {
        "DUT": "kestrel_tb_top",
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
        toplevel="kestrel_tb_top",
        module=module,
        testcase=cocotb_testcase,
        sim_build=sim_build,
        extra_env=extra_env,
        parameters={"RESET_ADDR": str(reset_addr)},
        plus_args=[f"+imem={hex_path}"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
