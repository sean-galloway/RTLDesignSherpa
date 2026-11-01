# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_merlin_hazard
# Purpose: Functional unit test for the merlin forwarding and interlock unit.
#          Covers the no-hazard, EX/MEM-forward, MEM/WB-forward, both-pending
#          (EX/MEM wins), x0-never-forwards, load-use stall, load-use-vs-x0
#          no-stall, and flush-wins-over-stall matrix.
#
# Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
# Subsystem: riscv-ip/merlin-rv32i
#
# Created: 2026-11-01

"""Hazard-unit unit tests for merlin-rv32i."""

import os

import cocotb
import pytest
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402


# Forwarding-select encodings (mirror merlin_pkg localparams).
FWD_IDEX = 0
FWD_EXMEM = 1
FWD_MEMWB = 2


def _set_inputs(dut, **kwargs):
    """Drive named scalar inputs to the DUT; unspecified inputs default to 0."""
    defaults = {
        "id_rs1_addr": 0,
        "id_rs2_addr": 0,
        "idex_rd_addr": 0,
        "idex_rd_wen": 0,
        "idex_is_load": 0,
        "exmem_rd_addr": 0,
        "exmem_rd_wen": 0,
        "memwb_rd_addr": 0,
        "memwb_rd_wen": 0,
        "ex_flush": 0,
    }
    defaults.update(kwargs)
    for name, value in defaults.items():
        getattr(dut, name).value = value


async def _sample(dut):
    """Sample the DUT outputs after combinational propagation."""
    await Timer(1, unit="ns")
    return {
        "fwd_a": int(dut.fwd_a.value),
        "fwd_b": int(dut.fwd_b.value),
        "stall_ifid": int(dut.stall_ifid.value),
        "flush_ifid": int(dut.flush_ifid.value),
        "flush_idex": int(dut.flush_idex.value),
    }


async def _check_case(dut, expected, **inputs):
    """Drive one input vector and assert the expected outputs."""
    _set_inputs(dut, **inputs)
    actual = await _sample(dut)
    assert actual == expected, f"inputs={inputs}: expected {expected}, got {actual}"


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_merlin_hazard(dut):
    """Verify the hazard unit forwarding and interlock matrix."""
    # 1) No hazard: no producer matches, both forwards select register file.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_IDEX, "fwd_b": FWD_IDEX,
                  "stall_ifid": 0, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=1, id_rs2_addr=2,
        idex_rd_addr=3, idex_rd_wen=1,
        exmem_rd_addr=4, exmem_rd_wen=1,
        memwb_rd_addr=5, memwb_rd_wen=1,
    )

    # 2) EX/MEM hit on port A.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_EXMEM, "fwd_b": FWD_IDEX,
                  "stall_ifid": 0, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=7, id_rs2_addr=8,
        exmem_rd_addr=7, exmem_rd_wen=1,
    )

    # 3) EX/MEM hit on port B.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_IDEX, "fwd_b": FWD_EXMEM,
                  "stall_ifid": 0, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=9, id_rs2_addr=10,
        exmem_rd_addr=10, exmem_rd_wen=1,
    )

    # 4) MEM/WB hit on port A.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_MEMWB, "fwd_b": FWD_IDEX,
                  "stall_ifid": 0, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=11, id_rs2_addr=12,
        memwb_rd_addr=11, memwb_rd_wen=1,
    )

    # 5) Both EX/MEM and MEM/WB pending: EX/MEM wins on port A.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_EXMEM, "fwd_b": FWD_IDEX,
                  "stall_ifid": 0, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=13,
        exmem_rd_addr=13, exmem_rd_wen=1,
        memwb_rd_addr=13, memwb_rd_wen=1,
    )

    # 6) x0 producer never forwards, even with wen=1 and address match.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_IDEX, "fwd_b": FWD_IDEX,
                  "stall_ifid": 0, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=0, id_rs2_addr=0,
        idex_rd_addr=0, idex_rd_wen=1,
        exmem_rd_addr=0, exmem_rd_wen=1,
        memwb_rd_addr=0, memwb_rd_wen=1,
    )

    # 7) Load-use stall: load in EX writing a register that ID reads.
    #    The load has not reached MEM yet, so forwarding selects the regfile
    #    and the pipeline stalls for one cycle.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_IDEX, "fwd_b": FWD_IDEX,
                  "stall_ifid": 1, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=14, id_rs2_addr=15,
        idex_rd_addr=14, idex_rd_wen=1, idex_is_load=1,
    )

    # 8) Load-use vs x0: load in EX writing x0 must not stall.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_IDEX, "fwd_b": FWD_IDEX,
                  "stall_ifid": 0, "flush_ifid": 0, "flush_idex": 0},
        id_rs1_addr=0, id_rs2_addr=16,
        idex_rd_addr=0, idex_rd_wen=1, idex_is_load=1,
    )

    # 9) ex_flush asserts both flush outputs and beats stall.
    await _check_case(
        dut,
        expected={"fwd_a": FWD_IDEX, "fwd_b": FWD_IDEX,
                  "stall_ifid": 1, "flush_ifid": 1, "flush_idex": 1},
        id_rs1_addr=17,
        idex_rd_addr=17, idex_rd_wen=1, idex_is_load=1,
        ex_flush=1,
    )

    dut._log.info("merlin_hazard test PASSED")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"merlin_hazard {lvl}") for lvl in reg_level_grid()])
def test_merlin_hazard(request, test_level, description):
    """Pytest wrapper for the merlin hazard-unit cocotb test."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})

    dut_name = "merlin_hazard_tb_top"
    test_name_plus_params = f"test_merlin_hazard_{test_level}"

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
        testcase="cocotb_test_merlin_hazard",
        sim_build=sim_build,
        extra_env=extra_env,
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
