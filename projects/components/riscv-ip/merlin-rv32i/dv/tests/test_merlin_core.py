# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_merlin_core
# Purpose: Golden-trace lockstep test for the merlin_core vertical slice.
#          Each case loads a hand-assembled program through the TB top's
#          +imem plusarg, runs the pipelined core to halt, and diffs the
#          recorded RVFI trace against the Python golden model.
#
# Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
# Subsystem: riscv-ip/merlin-rv32i
#
# Author: sean galloway
# Created: 2026-11-01

"""merlin_core golden-trace tests: focus pins, OP/OP-IMM sweep, mem_wait pulse."""

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

from tbclasses.merlin.merlin_tb import (                         # noqa: E402
    MerlinTB,
    RV32IInterpreter,
    load_verilog_hex,
)

PROGRAMS_DIR = Path(__file__).resolve().parent / "programs"

CASES = {
    "cocotb_test_merlin_core_focus":
        ("focus.hex", 0x0000_0000),
    "cocotb_test_merlin_core_ops":
        ("rv32ui_ops.hex", 0x0000_0000),
}


async def _run_case(dut, hex_name, reset_addr):
    imem_words = load_verilog_hex(PROGRAMS_DIR / hex_name)
    golden = RV32IInterpreter(imem_words, reset_addr=reset_addr)
    golden.run()

    tb = MerlinTB(dut, reset_addr=reset_addr)
    await tb.run()

    tb.check_halt(expected_cause=golden.halt_cause,
                  expected_halt_pc=golden.halt_pc)
    tb.check_first_pc()
    tb.check_order_sequence()
    tb.check_pc_sequential()
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)
    dut._log.info(
        f"{hex_name}: {len(tb.trace)} beats retired, "
        "trace matches golden model")
    return tb


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_core_focus(dut):
    """Review Focus 1+2: x0 discard and back-to-back dependent ALU ops."""
    await _run_case(dut, "focus.hex", 0x0000_0000)


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_core_ops(dut):
    """One vector per OP/OP-IMM op plus LUI/AUIPC, diffed against golden."""
    tb = await _run_case(dut, "rv32ui_ops.hex", 0x0000_0000)
    x0_beats = [b for b in tb.trace
                if b["insn"] in (0x00500013, 0x00208033)]
    assert len(x0_beats) == 2, "x0-discard vectors missing from the trace"


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_core_mem_wait_pulse(dut):
    """Hold mem_wait mid-load: no double dmem_req, no double retire.

    Uses ls_basic.hex, which contains naturally aligned loads.  The pulse
    callback asserts mem_wait for two cycles as soon as the first load is
    observed on the data-memory request port (dmem_req && !dmem_we).  The
    load must retire exactly once after the wait ends, and the trace must
    still match the golden model.
    """
    hex_name = "ls_basic.hex"
    reset_addr = 0x0000_0000
    imem_words = load_verilog_hex(PROGRAMS_DIR / hex_name)
    golden = RV32IInterpreter(imem_words, reset_addr=reset_addr)
    golden.run()

    tb = MerlinTB(dut, reset_addr=reset_addr)

    # Track dmem_req edges and the cycle on which the first load appears.
    first_load_cycle = [None]
    req_seen = [False]

    def pulse_mem_wait(dut, cycle):
        is_load = int(dut.dmem_req.value) and (int(dut.dmem_wstrb.value) == 0)
        if is_load and first_load_cycle[0] is None:
            first_load_cycle[0] = cycle
        if first_load_cycle[0] is not None:
            rel = cycle - first_load_cycle[0]
            # Assert mem_wait for cycles 1 and 2 after the load request.
            return 1 <= rel <= 2
        return False

    await tb.run(pulse_mem_wait=pulse_mem_wait)

    assert first_load_cycle[0] is not None, "no load request observed"
    tb.check_halt(expected_cause=golden.halt_cause,
                  expected_halt_pc=golden.halt_pc)
    tb.check_first_pc()
    tb.check_order_sequence()
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)
    dut._log.info(
        f"{hex_name}: mem_wait pulsed at load cycle {first_load_cycle[0]}, "
        f"{len(tb.trace)} beats retired, trace matches golden model")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"merlin_core {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES) +
                         ["cocotb_test_merlin_core_mem_wait_pulse"])
def test_merlin_core(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})

    if cocotb_testcase == "cocotb_test_merlin_core_mem_wait_pulse":
        hex_name = "ls_basic.hex"
        reset_addr = 0x0000_0000
    else:
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
        plus_args=[f"+imem={hex_path}"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
