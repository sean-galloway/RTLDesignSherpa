# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_merlin_core_regression
# Purpose: Regression tests for CRITICAL-1 and CRITICAL-2 from Task 3 review.
#          These cases are deliberately not covered by the golden kestrel
#          programs: a load after a non-memory ALU predecessor, and load-use
#          hazards at distances 1/2/3.
#
# Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
# Subsystem: riscv-ip/merlin-rv32i

"""merlin_core regression tests for load datapath and load-use interlock."""

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
    "cocotb_test_merlin_core_load_after_alu":
        ("load_after_alu.hex", 0x0000_0000),
    "cocotb_test_merlin_core_load_use_distances":
        ("load_use_distances.hex", 0x0000_0000),
    "cocotb_test_merlin_core_mem_wait_in_wb":
        ("mem_wait_in_wb.hex", 0x0000_0000),
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


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_core_load_after_alu(dut):
    """CRITICAL-1: a lw whose MEM-stage predecessor is a non-memory ALU op.

    Before the fix the load captured the previous MEM slot's dmem_rdata and
    produced the wrong value.
    """
    tb, _ = await _run_case(dut, "load_after_alu.hex", 0x0000_0000)

    # The lw at PC 0x14 writes x4; it must read the stored 0x12345678.
    load_beat = next(b for b in tb.trace if b["pc"] == 0x14)
    assert load_beat["rd_wdata"] == 0x12345678, (
        f"lw rd_wdata=0x{load_beat['rd_wdata']:x} expected 0x12345678")
    dut._log.info("load_after_alu: lw saw correct stored word")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_core_load_use_distances(dut):
    """CRITICAL-2: load-use consumers at distances 1, 2, 3 retire once.

    Distance-1 must cost exactly one bubble; distances 2/3 resolve through
    forwarding without double retirement.
    """
    tb, _ = await _run_case(dut, "load_use_distances.hex", 0x0000_0000)

    by_pc = {b["pc"]: b for b in tb.trace}

    load = by_pc[0x10]
    d1 = by_pc[0x14]   # add x4, x3, x0
    d2 = by_pc[0x1c]   # add x6, x3, x5
    d3 = by_pc[0x28]   # add x9, x3, x8

    assert d1["rd_wdata"] == 0x12345678, (
        f"distance-1 consumer rd_wdata=0x{d1['rd_wdata']:x}")
    assert d2["rd_wdata"] == 0x12345689, (
        f"distance-2 consumer rd_wdata=0x{d2['rd_wdata']:x}")
    assert d3["rd_wdata"] == 0x123456AB, (
        f"distance-3 consumer rd_wdata=0x{d3['rd_wdata']:x}")

    # Distance-1 must be delayed by exactly one cycle vs. back-to-back retirement.
    assert d1["cycle"] == load["cycle"] + 2, (
        f"distance-1 bubble count wrong: load cycle={load['cycle']} "
        f"consumer cycle={d1['cycle']}")

    # No consumer retired twice.
    for pc in (0x14, 0x1c, 0x28):
        assert sum(1 for b in tb.trace if b["pc"] == pc) == 1, (
            f"consumer at pc=0x{pc:x} retired more than once")

    dut._log.info(
        f"load_use_distances: d1 cycle={d1['cycle']}, d2 cycle={d2['cycle']}, "
        f"d3 cycle={d3['cycle']}, all consumers retired exactly once")


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def cocotb_test_merlin_core_mem_wait_in_wb(dut):
    """IMPORTANT-1: mem_wait parks a load in WB while its follower sits in MEM.

    The first load's request is accepted and captured, then mem_wait is
    asserted so load1 advances into WB while load2 is in MEM presenting a
    different address.  The waited load must retire with its own data, not
    the follower's word.
    """
    imem_words = load_verilog_hex(PROGRAMS_DIR / "mem_wait_in_wb.hex")
    golden = RV32IInterpreter(imem_words, reset_addr=0x0000_0000)
    golden.run()

    tb = MerlinTB(dut, reset_addr=0x0000_0000)

    first_load_cycle = [None]
    prev_load_req = [False]

    def pulse_mem_wait(dut, cycle):
        is_load = int(dut.dmem_req.value) and (int(dut.dmem_wstrb.value) == 0)
        # Detect the rising edge of a load request so we do not mis-trigger on
        # the tail of a preceding store cycle where dmem_wstrb has fallen.
        if is_load and not prev_load_req[0]:
            first_load_cycle[0] = cycle
        prev_load_req[0] = is_load
        if first_load_cycle[0] is not None:
            rel = cycle - first_load_cycle[0]
            # Fire one cycle after the rising edge of the first load request.
            # That gives the load one accepted request cycle (capture), then
            # asserts mem_wait so load1 is parked in WB while load2 sits in
            # MEM with dmem_req suppressed.
            return rel == 1
        return False

    await tb.run(pulse_mem_wait=pulse_mem_wait)

    assert first_load_cycle[0] is not None, "no load request observed"
    tb.check_halt(expected_cause=golden.halt_cause,
                  expected_halt_pc=golden.halt_pc)
    tb.check_first_pc()
    tb.check_order_sequence()
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)

    by_pc = {b["pc"]: b for b in tb.trace}
    load1 = by_pc[0x1C]   # lw x13, 0(x10)  -> 0x12345678
    load2 = by_pc[0x20]   # lw x14, 4(x10)  -> 0xabcddef0

    assert load1["rd_wdata"] == 0x12345678, (
        f"stalled load1 rd_wdata=0x{load1['rd_wdata']:x} expected 0x12345678")
    assert load2["rd_wdata"] == 0xabcddef0, (
        f"follower load2 rd_wdata=0x{load2['rd_wdata']:x} expected 0xabcddef0")

    # The trace is sampled at the same falling edge that drives mem_wait, so
    # it cannot see a clobbered commit edge.  The architectural ground truth
    # is the register file: read x13/x14 back out of the DUT.
    x13 = int(dut.u_merlin_core.u_regfile.regs[13].value)
    x14 = int(dut.u_merlin_core.u_regfile.regs[14].value)
    assert x13 == 0x12345678, (
        f"regfile x13=0x{x13:08x}: waited load committed the wrong word "
        f"(dmem_rdata clobbered while parked in WB)")
    assert x14 == 0xabcddef0, (
        f"regfile x14=0x{x14:08x}: follower load corrupted")

    dut._log.info(
        f"mem_wait_in_wb: load1 retired at cycle {load1['cycle']} with "
        f"0x{load1['rd_wdata']:x}, load2 at cycle {load2['cycle']} with "
        f"0x{load2['rd_wdata']:x}")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"merlin_core_regression {lvl}")
                          for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_merlin_core_regression(request, cocotb_testcase, test_level, description):
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
