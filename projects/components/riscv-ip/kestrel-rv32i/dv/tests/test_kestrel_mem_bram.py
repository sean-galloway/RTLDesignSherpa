# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_mem_bram
# Purpose: kestrel_core behind kestrel_mem_bram (registered-read block RAM):
#          (a) the rv32ui battery through the AXIL port with the golden
#          interpreter diff + spike lockstep, every image at func level;
#          (b) the wrapper's registers -- status, counters, the gp verdict,
#          stop/reload/rerun; (c) AXIL backpressure on the 2-stage read.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-20
"""Registered-read board path for kestrel (kestrel_bram_tb_top)."""

import os
import sys
from pathlib import Path

import cocotb
import pytest
from cocotb.triggers import FallingEdge, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = str(Path(__file__).resolve().parents[1])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)
PROGRAMS_DIR = Path(__file__).resolve().parent / "programs"
if str(PROGRAMS_DIR) not in sys.path:
    sys.path.insert(0, str(PROGRAMS_DIR))

from tbclasses.kestrel.kestrel_bram_tb import (                      # noqa: E402
    BUILD_ID, REG_BUILD_ID, KestrelBramTB,
)
from tbclasses.kestrel.rv32i_interpreter import RV32IInterpreter     # noqa: E402
from tbclasses.kestrel.rv32ui_battery import LINK_BASE, RV32UIBattery  # noqa: E402
from test_kestrel_mem_loader import PROG_STORE_AXIL, PROG_WORDS      # noqa: E402


async def _registers(dut):
    """BUILD_ID, load + readback with strobes, run to halt (golden diff),
    the status registers, then stop / reload / run again."""
    tb = KestrelBramTB(dut, reset_addr=0x0000_0000)
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.enter_load_mode_only()
    assert int(dut.core_rst_n.value) == 0, "core_rst_n high in load mode"
    assert await tb.axil_read(REG_BUILD_ID) == BUILD_ID

    st = await tb.status()
    assert (st["run"], st["halted"]) == (0, 0), f"load-mode status {st}"

    await tb.axil_write(0x100, 0xAABB_CCDD)
    assert await tb.axil_read(0x100) == 0xAABB_CCDD
    await tb.axil_write(0x100, 0x1122_3344, strb=0b0101)
    assert await tb.axil_read(0x100) == 0xAA22_CC44, "wstrb merge"
    await tb.axil_write(0x10100, 0x5566_7788)
    assert await tb.axil_read(0x10100) == 0x5566_7788

    golden = RV32IInterpreter(PROG_WORDS, reset_addr=0)
    golden.run()
    for attempt in range(2):
        await tb.backdoor_load(PROG_WORDS)
        await tb.release_reset()      # streams the image; the core stays in load mode
        await tb.run_to_halt()
        tb.check_halt(expected_cause=golden.halt_cause, expected_halt_pc=golden.halt_pc)
        tb.check_first_pc()
        tb.check_order_sequence()
        tb.check_trace(golden.trace)
        tb.check_trap_beat()
        st = await tb.status()
        dut._log.info("run %d status: %s (golden retired %d)", attempt, st, len(golden.trace))
        assert (st["run"], st["halted"], st["cause"]) == (1, 1, golden.halt_cause), st
        assert st["instret"] == len(tb.trace), \
            f"INSTRET {st['instret']} != {len(tb.trace)} RVFI beats"
        assert 2 * st["instret"] <= st["cycles"] <= 3 * st["instret"] + 8, \
            f"CYCLES {st['cycles']} outside CPI 2..3 for {st['instret']} instructions"
        assert await tb.axil_read(PROG_STORE_AXIL) == 0x123, "core store not visible"
        await tb.stop()
        await RisingEdge(dut.clk)
        assert int(dut.core_rst_n.value) == 0, "stop did not return to load mode"
        await tb.axil_write(PROG_STORE_AXIL, 0)       # the rerun must store it again
    dut._log.info("kestrel_mem_bram registers PASSED")


async def _golden(dut):
    """The rv32ui battery through the block-RAM path: every image at func
    and full, rv32ui-p-add at gate."""
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    work_dir = os.path.join(log_dir, "rv32ui_battery_bram")
    tests = ("add",) if level == "gate" else None
    battery = RV32UIBattery(dut, repo_root=repo_root, level=level, work_dir=work_dir,
                            tb_class=KestrelBramTB, tests=tests)
    await battery.run()


async def _backpressure(dut):
    """rready held low across a block-RAM read: rvalid/rdata hold, nothing
    lost or duplicated."""
    tb = KestrelBramTB(dut, reset_addr=0x0000_0000)
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.enter_load_mode_only()
    await tb.axil_write(0x200, 0xA5A5_5A5A)
    await tb.axil_write(0x204, 0x1234_5678)
    tb.master["read"].r_channel.set_ready_policy("stall")
    reader = cocotb.start_soon(tb.axil_read(0x200))
    for _ in range(12):
        await FallingEdge(dut.clk)
    assert int(dut.s_axil_rvalid.value) == 1, "rvalid not raised"
    assert int(dut.s_axil_rdata.value) == 0xA5A5_5A5A, "rdata not held under backpressure"
    await RisingEdge(dut.clk)
    tb.master["read"].r_channel.set_ready_policy("always")
    assert await reader == 0xA5A5_5A5A
    assert await tb.axil_read(0x204) == 0x1234_5678
    dut._log.info("kestrel_mem_bram backpressure PASSED")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_mem_bram_registers(dut):
    await _registers(dut)


@cocotb.test(timeout_time=20000, timeout_unit="ms")
async def cocotb_test_kestrel_mem_bram_golden(dut):
    await _golden(dut)


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_mem_bram_backpressure(dut):
    await _backpressure(dut)


CASES = {
    "cocotb_test_kestrel_mem_bram_registers": 0x0000_0000,
    "cocotb_test_kestrel_mem_bram_golden": LINK_BASE,
    "cocotb_test_kestrel_mem_bram_backpressure": 0x0000_0000,
}


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"kestrel_mem_bram {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_kestrel_mem_bram(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/kestrel-rv32i/dv/filelists/kestrel_tb.f")
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="kestrel_bram_tb_top",
        module=module,
        testcase=cocotb_testcase,
        sim_build=sim_build,
        extra_env={"DUT": "kestrel_bram_tb_top", "LOG_PATH": log_path,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
                   **level_env(test_level)},
        parameters={"RESET_ADDR": str(CASES[cocotb_testcase])},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--trace-depth", "99",
                      "--timescale", "1ns/1ps", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
