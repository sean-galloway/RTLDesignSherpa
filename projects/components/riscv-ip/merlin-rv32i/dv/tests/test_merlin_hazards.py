# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_merlin_hazards
# Purpose: Directed hazard suite for the merlin 5-stage pipeline.
#          Each case is a hand-assembled hex program whose RVFI trace is
#          golden-diffed, plus targeted assertions on rd_wdata, cycle counts,
#          and single-retirement.
#
# Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
# Subsystem: riscv-ip/merlin-rv32i

"""merlin_core directed hazard suite."""

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
    "cocotb_test_merlin_hazard_forward_matrix":
        ("hazard_forward_matrix.hex", 0x0000_0000),
    "cocotb_test_merlin_hazard_loaduse_matrix":
        ("load_use_distances.hex", 0x0000_0000),
    "cocotb_test_merlin_hazard_branch_after_alu":
        ("hazard_branch_after_alu.hex", 0x0000_0000),
    "cocotb_test_merlin_hazard_store_data_forward":
        ("hazard_store_data_forward.hex", 0x0000_0000),
    "cocotb_test_merlin_hazard_flush_during_loaduse":
        ("hazard_flush_during_loaduse.hex", 0x0000_0000),
    "cocotb_test_merlin_hazard_jalr_forward":
        ("hazard_jalr_forward.hex", 0x0000_0000),
    "cocotb_test_merlin_hazard_branch_flush_backtoback":
        ("hazard_branch_flush_backtoback.hex", 0x0000_0000),
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
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)
    return tb, golden


def _by_pc(trace):
    return {b["pc"]: b for b in trace}


def _assert_single_retirement(trace, pc_list):
    for pc in pc_list:
        count = sum(1 for b in trace if b["pc"] == pc)
        assert count == 1, f"pc=0x{pc:x} retired {count} times, expected 1"


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_hazard_forward_matrix(dut):
    """Every producer stage (EX/MEM, MEM/WB) x both ALU operands."""
    tb, _ = await _run_case(dut, "hazard_forward_matrix.hex", 0x0000_0000)

    by_pc = _by_pc(tb.trace)
    assert by_pc[0x08]["rd_wdata"] == 0x1E, "add x3,x1,x2"
    assert by_pc[0x0C]["rd_wdata"] == 0x28, "add x4,x3,x1"
    assert by_pc[0x10]["rd_wdata"] == 0x32, "add x5,x2,x3"
    assert by_pc[0x14]["rd_wdata"] == 0x5A, "add x6,x4,x5"
    _assert_single_retirement(tb.trace, [0x00, 0x04, 0x08, 0x0C, 0x10, 0x14])
    dut._log.info("forward_matrix: all forwarding combinations passed")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_hazard_loaduse_matrix(dut):
    """Load-use consumers at distances 1/2/3 retire once with correct bubbles."""
    tb, _ = await _run_case(dut, "load_use_distances.hex", 0x0000_0000)

    by_pc = _by_pc(tb.trace)
    load = by_pc[0x10]
    d1 = by_pc[0x14]
    d2 = by_pc[0x1C]
    d3 = by_pc[0x28]

    assert d1["rd_wdata"] == 0x12345678
    assert d2["rd_wdata"] == 0x12345689
    assert d3["rd_wdata"] == 0x123456AB
    assert d1["cycle"] == load["cycle"] + 2, (
        f"distance-1 bubble wrong: load cycle={load['cycle']} "
        f"consumer cycle={d1['cycle']}")
    _assert_single_retirement(tb.trace, [0x14, 0x1C, 0x28])
    dut._log.info(
        f"loaduse_matrix: d1 cycle={d1['cycle']}, d2 cycle={d2['cycle']}, "
        f"d3 cycle={d3['cycle']}, all retired once")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_hazard_branch_after_alu(dut):
    """Branches with operands from immediately-preceding ALU results, taken and not-taken."""
    tb, _ = await _run_case(dut, "hazard_branch_after_alu.hex", 0x0000_0000)

    by_pc = _by_pc(tb.trace)

    # Taken branches redirect; skipped fall-through slots must not retire.
    assert 0x0C not in by_pc, "fall-through after first taken beq executed"
    assert 0x1C not in by_pc, "fall-through after second taken bne executed"

    # Not-taken branches fall through.
    assert by_pc[0x2C]["rd_wdata"] == 1, "addi x9 after not-taken beq"
    assert by_pc[0x3C]["rd_wdata"] == 1, "addi x12 after not-taken bne"

    # Branch targets are correct.
    assert by_pc[0x08]["pc_wdata"] == 0x10
    assert by_pc[0x18]["pc_wdata"] == 0x20
    assert by_pc[0x28]["pc_wdata"] == 0x2C
    assert by_pc[0x38]["pc_wdata"] == 0x3C

    _assert_single_retirement(tb.trace, [0x00, 0x04, 0x08, 0x10, 0x14,
                                          0x18, 0x20, 0x24, 0x28, 0x2C,
                                          0x30, 0x34, 0x38, 0x3C])
    dut._log.info("branch_after_alu: taken/not-taken directions passed")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_hazard_store_data_forward(dut):
    """ALU result forwarded into a store's rs2 data, verified by a later load."""
    tb, _ = await _run_case(dut, "hazard_store_data_forward.hex", 0x0000_0000)

    by_pc = _by_pc(tb.trace)
    assert by_pc[0x10]["rd_wdata"] == 0x12345678, "load read back stored word"
    _assert_single_retirement(tb.trace, [0x00, 0x04, 0x08, 0x0C, 0x10])
    dut._log.info("store_data_forward: store data forwarded and verified")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_hazard_flush_during_loaduse(dut):
    """Taken branch after a load-use stall flushes the consumer's successor."""
    tb, _ = await _run_case(dut, "hazard_flush_during_loaduse.hex", 0x0000_0000)

    by_pc = _by_pc(tb.trace)

    # The load's consumer retires normally.
    assert by_pc[0x10]["rd_wdata"] == 0x1, "load consumer rd_wdata"

    # The instruction immediately after the taken branch is flushed.
    assert 0x18 not in by_pc, "branch delay slot / successor executed after flush"

    # The branch target instruction retires.
    assert by_pc[0x1C]["rd_wdata"] == 0xFFFF_FBCD, "branch target rd_wdata"

    _assert_single_retirement(tb.trace, [0x00, 0x04, 0x08, 0x0C, 0x10, 0x14, 0x1C])
    dut._log.info("flush_during_loaduse: branch flush after load-use stall passed")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_hazard_jalr_forward(dut):
    """jalr rs1 forwarded from a preceding ALU op and from a load result."""
    tb, _ = await _run_case(dut, "hazard_jalr_forward.hex", 0x0000_0000)

    by_pc = _by_pc(tb.trace)

    # ALU-forwarded jalr.
    assert by_pc[0x04]["rd_wdata"] == 0x08, "jalr link from first jump"
    assert 0x08 not in by_pc and 0x0C not in by_pc, "first jump fall-through executed"

    # Load-forwarded jalr.
    assert by_pc[0x20]["rd_wdata"] == 0x24, "jalr link from second jump"
    assert 0x24 not in by_pc and 0x28 not in by_pc, "second jump fall-through executed"

    assert by_pc[0x2C]["rd_wdata"] == 2, "second jump target"

    _assert_single_retirement(tb.trace, [0x00, 0x04, 0x10, 0x14, 0x18, 0x1C,
                                          0x20, 0x2C])
    dut._log.info("jalr_forward: ALU- and load-forwarded jalr targets passed")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_hazard_branch_flush_backtoback(dut):
    """Two taken branches back-to-back, each flushing its fall-through slot."""
    tb, _ = await _run_case(dut, "hazard_branch_flush_backtoback.hex", 0x0000_0000)

    by_pc = _by_pc(tb.trace)

    assert 0x04 not in by_pc, "first branch fall-through executed"
    assert 0x0C not in by_pc, "second branch fall-through executed"
    assert by_pc[0x10]["rd_wdata"] == 1, "target after back-to-back branches"
    assert len(tb.trace) == 4, f"expected 4 retire beats, got {len(tb.trace)}"

    _assert_single_retirement(tb.trace, [0x00, 0x08, 0x10])
    dut._log.info("branch_flush_backtoback: both taken branches redirected cleanly")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"merlin_hazards {lvl}")
                          for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_merlin_hazards(request, cocotb_testcase, test_level, description):
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
