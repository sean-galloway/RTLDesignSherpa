# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_merlin_pipe_regs
# Purpose: Functional unit test for the four merlin pipeline registers.
#          Exercises capture, stall-hold, flush-bubble, and flush-wins-over-
#          stall for each stage boundary through the flat-port TB wrapper.
#
# Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
# Subsystem: riscv-ip/merlin-rv32i
#
# Created: 2026-10-31

"""Pipeline-register unit tests for merlin-rv32i."""

import os

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402


# Field maps for each stage boundary.  Keys are cocotb handle names in the
# wrapper; values are the bit width of the scalar port.
STAGE_FIELDS = {
    "if_id": {
        "pc": 32,
        "insn": 32,
        "valid": 1,
    },
    "id_ex": {
        "pc": 32,
        "rs1_data": 32,
        "rs2_data": 32,
        "imm": 32,
        "rs1_addr": 5,
        "rs2_addr": 5,
        "rd_addr": 5,
        "funct3": 3,
        "alu_op": 4,
        "alu_src_a_pc": 1,
        "alu_src_b_imm": 1,
        "rd_wen": 1,
        "wb_sel": 2,
        "dmem_req": 1,
        "dmem_we": 1,
        "branch": 1,
        "jump": 1,
        "jalr": 1,
        "halt_cause": 4,
        "csr_stub": 1,
        "valid": 1,
    },
    "ex_mem": {
        "pc": 32,
        "next_pc": 32,
        "alu_y": 32,
        "store_data": 32,
        "rd_addr": 5,
        "rd_wen": 1,
        "wb_sel": 2,
        "funct3": 3,
        "dmem_req": 1,
        "dmem_we": 1,
        "ls_misalign": 1,
        "halt_cause": 4,
        "csr_stub": 1,
        "valid": 1,
    },
    "mem_wb": {
        "pc": 32,
        "next_pc": 32,
        "alu_y": 32,
        "load_data": 32,
        "rd_addr": 5,
        "rd_wen": 1,
        "wb_sel": 2,
        "csr_stub": 1,
        "halt_cause": 4,
        "valid": 1,
    },
}

# Bubble field checks per stage.  Every field named here must be zero after
# a flush.  Datapath fields not listed are also expected zero because the
# RTL flushes the whole struct to '0.
BUBBLE_CHECKS = {
    "if_id": ["valid"],
    "id_ex": [
        "valid", "rd_wen", "dmem_req", "dmem_we",
        "branch", "jump", "jalr", "csr_stub", "halt_cause",
    ],
    "ex_mem": [
        "valid", "rd_wen", "dmem_req", "dmem_we",
        "ls_misalign", "csr_stub", "halt_cause",
    ],
    "mem_wb": ["valid", "rd_wen", "csr_stub", "halt_cause"],
}


def _stage_input_handles(dut, stage):
    """Return a dict of cocotb input handles for one stage."""
    return {f: getattr(dut, f"{stage}_{f}_i") for f in STAGE_FIELDS[stage]}


def _stage_output_handles(dut, stage):
    """Return a dict of cocotb output handles for one stage."""
    return {f: getattr(dut, f"{stage}_{f}_o") for f in STAGE_FIELDS[stage]}


def _read_stage(outputs):
    """Sample the wrapper's output ports for one stage into a dict."""
    return {f: int(h.value) for f, h in outputs.items()}


def _write_stage(inputs, values):
    """Drive the wrapper's input ports for one stage from a dict."""
    for f, h in inputs.items():
        h.value = values.get(f, 0)


def _pattern_for_stage(stage, tag):
    """Return a deterministic non-zero pattern for one stage.

    tag is an arbitrary integer seed used to vary the pattern across phases.
    """
    fields = STAGE_FIELDS[stage]
    pattern = {}
    for i, (f, width) in enumerate(fields.items()):
        if width == 1:
            # Toggle some single-bit controls on to verify they flush off.
            pattern[f] = 1 if ((tag + i) & 1) else 0
        else:
            # Distinct nonzero values per field; avoid all-ones to keep
            # assertions easy to read in failure messages.
            pattern[f] = ((tag + i + 1) * 0x1111_1111) & ((1 << width) - 1)
    return pattern


async def _test_one_stage(dut, stage):
    """Verify capture, stall-hold, flush-bubble, and flush-wins-stall."""
    in_handles = _stage_input_handles(dut, stage)
    out_handles = _stage_output_handles(dut, stage)
    stall_handle = getattr(dut, f"{stage}_stall")
    flush_handle = getattr(dut, f"{stage}_flush")

    # Default controls: not stalled, not flushed.
    stall_handle.value = 0
    flush_handle.value = 0

    async def drive_and_wait(values, stall=0, flush=0):
        _write_stage(in_handles, values)
        stall_handle.value = stall
        flush_handle.value = flush
        await RisingEdge(dut.clk)
        await Timer(1, units="ns")
        return _read_stage(out_handles)

    pattern_a = _pattern_for_stage(stage, tag=1)
    pattern_b = _pattern_for_stage(stage, tag=2)
    pattern_c = _pattern_for_stage(stage, tag=3)

    # 1) Capture: after reset, a new input appears on the output.
    q = await drive_and_wait(pattern_a)
    assert q == pattern_a, f"{stage}: capture failed: {q} != {pattern_a}"

    # 2) Stall-hold: output keeps pattern_a while input changes to pattern_b.
    q = await drive_and_wait(pattern_b, stall=1)
    assert q == pattern_a, f"{stage}: stall-hold failed: {q} != {pattern_a}"

    # 3) Flush wins over stall: while still stalled, assert flush -> bubble.
    q = await drive_and_wait(pattern_b, stall=1, flush=1)
    for f in BUBBLE_CHECKS[stage]:
        assert q[f] == 0, f"{stage}: flush did not clear {f}: {q[f]}"
    # Every datapath field also flushes to zero.
    for f, width in STAGE_FIELDS[stage].items():
        if width > 1:
            assert q[f] == 0, f"{stage}: flush did not clear datapath {f}: {q[f]:#x}"

    # 4) Resume capture after flush is released.
    q = await drive_and_wait(pattern_c)
    assert q == pattern_c, f"{stage}: post-flush capture failed: {q} != {pattern_c}"


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_merlin_pipe_regs(dut):
    """Verify all four pipeline registers for capture, stall, and flush."""
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Drive all inputs and controls to a safe default before reset release.
    for stage in STAGE_FIELDS:
        _write_stage(_stage_input_handles(dut, stage), {})
        getattr(dut, f"{stage}_stall").value = 0
        getattr(dut, f"{stage}_flush").value = 0

    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await Timer(1, units="ns")
    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    await Timer(1, units="ns")

    # After reset every output should be the bubble record (all zero).
    for stage in STAGE_FIELDS:
        q = _read_stage(_stage_output_handles(dut, stage))
        for f in BUBBLE_CHECKS[stage]:
            assert q[f] == 0, f"{stage}: reset bubble {f} not zero: {q[f]}"

    for stage in STAGE_FIELDS:
        await _test_one_stage(dut, stage)

    dut._log.info("merlin_pipe_regs test PASSED")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"merlin_pipe_regs {lvl}") for lvl in reg_level_grid()])
def test_merlin_pipe_regs(request, test_level, description):
    """Pytest wrapper for the merlin pipeline-register cocotb test."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})

    dut_name = "merlin_pipe_regs_tb_top"
    test_name_plus_params = f"test_merlin_pipe_regs_{test_level}"

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
        "DUT": dut_name,
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        **level_env(test_level),
    }

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND", "-Wno-CASEINCOMPLETE",
        "-Wno-BLKANDNBLK", FIELD_COMBO_VLT, "-Wno-TIMESCALEMOD",
        "-Wno-MODDUP", "-Wno-GENUNNAMED", "-Wno-PINCONNECTEMPTY",
        "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM", "-Wno-SYNCASYNCNET",
        "-Wno-DECLFILENAME", "-Wno-VARHIDDEN",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_merlin_pipe_regs",
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
