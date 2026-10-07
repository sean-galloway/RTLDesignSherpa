# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_branch
# Purpose: Golden-trace lockstep tests for kestrel_core branches and jumps.
#          Covers every branch condition in both directions, JAL forward/backward,
#          JALR via register target, JALR LSB-clear behavior, and a taken-loop
#          timing path (1..10 sum). The golden interpreter is extended for
#          BEQ/BNE/BLT/BGE/BLTU/BGEU, JAL, and JALR.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""kestrel_core branch/jump golden-trace tests."""

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
    "cocotb_test_kestrel_branch_all": ("branch_all.hex", 0x0000_0000),
    "cocotb_test_kestrel_branch_jal_jalr": ("jal_jalr.hex", 0x0000_0000),
    "cocotb_test_kestrel_branch_loop_sum": ("loop_sum.hex", 0x0000_0000),
}


def _check_pc_sequence(tb, golden_trace):
    """Dedicated assertion: every retired pc_rdata/pc_wdata pair follows the
    golden taken path, including branches and jumps."""
    for i, (got, want) in enumerate(zip(tb.trace, golden_trace)):
        assert got["pc"] == want["pc"], (
            f"beat {i} pc_rdata: core=0x{got['pc']:x} "
            f"golden=0x{want['pc']:x}")
        assert got["pc_wdata"] == want["pc_wdata"], (
            f"beat {i} pc_wdata: core=0x{got['pc_wdata']:x} "
            f"golden=0x{want['pc_wdata']:x} "
            f"(pc=0x{want['pc']:x})")


def _check_link_values(tb, golden_trace):
    """Dedicated assertion: JAL/JALR link values are pc+4."""
    for i, (got, want) in enumerate(zip(tb.trace, golden_trace)):
        if want["rd_addr"] != 0 and want["rd_wdata"] == (want["pc"] + 4) & 0xFFFFFFFF:
            assert got["rd_wdata"] == want["rd_wdata"], (
                f"beat {i} link value: core=0x{got['rd_wdata']:x} "
                f"golden=0x{want['rd_wdata']:x} "
                f"(pc=0x{want['pc']:x})")


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
    _check_pc_sequence(tb, golden.trace)
    _check_link_values(tb, golden.trace)
    tb.check_trace(golden.trace)
    dut._log.info(
        f"{hex_name}: {len(tb.trace)} beats retired, "
        "trace matches golden model")
    return tb


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_kestrel_branch_all(dut):
    """All six branch conditions, taken and not-taken; signed/unsigned split."""
    await _run_case(dut, "branch_all.hex", 0x0000_0000)


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_kestrel_branch_jal_jalr(dut):
    """JAL forward/backward, JALR register target, JALR LSB clear."""
    await _run_case(dut, "jal_jalr.hex", 0x0000_0000)


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_kestrel_branch_loop_sum(dut):
    """Taken-loop timing: sum 1..10 and verify final value via trace diff."""
    await _run_case(dut, "loop_sum.hex", 0x0000_0000)


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"kestrel_branch {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_kestrel_branch(request, cocotb_testcase, test_level, description):
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
