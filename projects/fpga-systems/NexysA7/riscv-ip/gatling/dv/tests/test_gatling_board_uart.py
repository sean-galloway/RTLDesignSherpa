# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against gatling build-bram in simulation, over UART.

`gatling_uart_tb_top` is the board top minus its clocking: the real
uart_axil_bridge + gatling_mem_bram + gatling_core. A cocotb UART channel
carries the identical byte stream the board's host sends, through the
UNMODIFIED programs in ../../bin/gatling_programs.py. The battery cells run
four different rv32ui images on the four harts at once, rotated so every
hart runs each (the board runs all 42; four per cell fits the sim-time
budget).
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
_AREA = os.path.join(_REPO, "projects/fpga-systems/NexysA7/riscv-ip/gatling")
_BIN = os.path.join(_AREA, "bin")
_FPGA_BIN = os.path.join(_REPO, "projects/fpga-systems/bin")
for _p in (_BIN, _FPGA_BIN):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel  # noqa: E402
from TBClasses.harness.byte_channel import TracingChannel           # noqa: E402
from uart_axi_bridge import UARTAxiBridge                           # noqa: E402
import gatling_board as gb                                          # noqa: E402
import gatling_programs as progs                                    # noqa: E402
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402  (not -Wno-MULTIDRIVEN)

CLKS_PER_BIT = 4
SIM_TIME_BUDGET_MS = 100.0

# Two four-image cells: straight-line and ALU, loads and stores of every
# width, self-modifying code, and ma_data's expected misaligned-load halt.
PROGRAMS = {
    "smoke": None,
    "quad_a": ["simple", "add", "lw", "sw"],
    "quad_b": ["fence_i", "ma_data", "sb", "jalr"],
}


@cocotb.test(timeout_time=150, timeout_unit="ms")
async def cocotb_test_program(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.i_uart_rx.value = 1
    dut.aresetn.value = 0
    await Timer(200, units="ns")
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 20)
    chan = TracingChannel(make_uart_channel(dut, dut.aclk, CLKS_PER_BIT, log=dut._log))
    k = gb.GatlingBoard(bridge=UARTAxiBridge(channel=chan))
    prog = os.environ["GATLING_PROGRAM"]
    if prog == "smoke":
        rep = await bridge(lambda: progs.smoke(k))()
    else:
        rep = await bridge(lambda: progs.battery(k, PROGRAMS[prog]))()
    ms = get_sim_time("ns") / 1e6
    dut._log.info("%s (%.2f ms sim): %s", prog, ms, rep.line())
    for row in rep.rows:
        dut._log.info("  %s", row)
    assert ms <= SIM_TIME_BUDGET_MS, f"{prog} used {ms:.1f} ms of sim time, over budget"
    assert rep.ok, f"{prog}: " + "; ".join(rep.failures[:5])


@pytest.mark.parametrize("program", list(PROGRAMS))
def test_gatling_board_uart(request, program):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    for var, rel in (("CONVERTERS_ROOT", "projects/components/utility-ip/converters"),
                     ("GATLING_ROOT", "projects/components/riscv-ip/gatling-rv32i"),
                     ("RV32I_COMMON_ROOT", "projects/components/riscv-ip/common-rv32i")):
        os.environ.setdefault(var, os.path.join(repo_root, rel))
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/fpga-systems/NexysA7/riscv-ip/gatling/dv/filelists/gatling_uart_tb_top.f")
    name = f"gatling_board_uart_{program}"
    sim_build = sim_build_path(tests_dir, "gatling_board_uart")   # one build, every cell
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir, _BIN, _FPGA_BIN],
        verilog_sources=verilog_sources, includes=includes,
        toplevel="gatling_uart_tb_top", module="test_gatling_board_uart",
        testcase="cocotb_test_program",
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": "gatling_uart_tb_top", "REPO_ROOT": repo_root,
                   "GATLING_PROGRAM": program, "COCOTB_LOG_LEVEL": "INFO",
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml")},
        compile_args=[FIELD_COMBO_VLT, "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
                      "-Wno-CASEINCOMPLETE", "-Wno-DECLFILENAME", "-Wno-UNUSEDSIGNAL",
                      "-Wno-UNUSEDPARAM", "-Wno-TIMESCALEMOD", "-Wno-PINCONNECTEMPTY"],
        keep_files=True, timescale="1ns/1ps")
