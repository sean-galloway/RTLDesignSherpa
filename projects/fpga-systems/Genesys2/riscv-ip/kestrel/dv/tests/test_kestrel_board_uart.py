# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against kestrel build-bram in simulation, over UART.

`kestrel_uart_tb_top` is the board top minus its clocking: the real
uart_axil_bridge + kestrel_mem_bram + kestrel_core. A cocotb UART channel
carries the identical byte stream the board's host sends, through the
UNMODIFIED programs in ../../bin/kestrel_programs.py. One cell per program
(the battery one rv32ui image per cell, for the sim-time budget).
"""

import os
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer
from cocotb.utils import get_sim_time
from cocotb._bridge import bridge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_REPO = os.environ["REPO_ROOT"]
_AREA = os.path.join(_REPO, "projects/fpga-systems/Genesys2/riscv-ip/kestrel")
_BIN = os.path.join(_AREA, "bin")
_FPGA_BIN = os.path.join(_REPO, "projects/fpga-systems/bin")
for _p in (_BIN, _FPGA_BIN):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel  # noqa: E402
from TBClasses.harness.byte_channel import TracingChannel           # noqa: E402
from uart_axi_bridge import UARTAxiBridge                           # noqa: E402
import kestrel_board as kb                                          # noqa: E402
import kestrel_programs as progs                                    # noqa: E402

CLKS_PER_BIT = 4
SIM_TIME_BUDGET_MS = 100.0

# rv32ui images the sim runs (the board runs all 42): straight-line, loads,
# stores, self-modifying code, cross-word misaligned accesses.
SIM_TESTS = ["simple", "add", "lw", "sw", "fence_i", "ma_data"]


@cocotb.test(timeout_time=150, timeout_unit="ms")
async def cocotb_test_program(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.i_uart_rx.value = 1
    dut.aresetn.value = 0
    await Timer(200, units="ns")
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 20)
    chan = TracingChannel(make_uart_channel(dut, dut.aclk, CLKS_PER_BIT, log=dut._log))
    k = kb.KestrelBoard(bridge=UARTAxiBridge(channel=chan))
    prog = os.environ["KESTREL_PROGRAM"]
    if prog == "smoke":
        rep = await bridge(lambda: progs.smoke(k))()
    else:
        rep = await bridge(lambda: progs.battery(k, [prog]))()
    ms = get_sim_time("ns") / 1e6
    dut._log.info("%s (%.2f ms sim): %s", prog, ms, rep.line())
    for row in rep.rows:
        dut._log.info("  %s", row)
    assert ms <= SIM_TIME_BUDGET_MS, f"{prog} used {ms:.1f} ms of sim time, over budget"
    assert rep.ok, f"{prog}: " + "; ".join(rep.failures[:5])


@pytest.mark.parametrize("program", ["smoke"] + SIM_TESTS)
def test_kestrel_board_uart(request, program):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    os.environ.setdefault("CONVERTERS_ROOT",
                          os.path.join(repo_root, "projects/components/utility-ip/converters"))
    os.environ.setdefault("KESTREL_ROOT",
                          os.path.join(repo_root, "projects/components/riscv-ip/kestrel-rv32i"))
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/fpga-systems/Genesys2/riscv-ip/kestrel/dv/filelists/kestrel_uart_tb_top.f")
    name = f"kestrel_board_uart_{program}"
    sim_build = sim_build_path(tests_dir, "kestrel_board_uart")   # one build, every cell
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir, _BIN, _FPGA_BIN],
        verilog_sources=verilog_sources, includes=includes,
        toplevel="kestrel_uart_tb_top", module="test_kestrel_board_uart",
        testcase="cocotb_test_program",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": "kestrel_uart_tb_top", "REPO_ROOT": repo_root,
                   "KESTREL_PROGRAM": program, "COCOTB_LOG_LEVEL": "INFO",
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml")},
        compile_args=["-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
                      "-Wno-CASEINCOMPLETE", "-Wno-DECLFILENAME", "-Wno-UNUSEDSIGNAL",
                      "-Wno-UNUSEDPARAM", "-Wno-TIMESCALEMOD", "-Wno-PINCONNECTEMPTY"],
        keep_files=True, timescale="1ns/1ps")
