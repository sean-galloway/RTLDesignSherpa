# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against the ALU harness in simulation, over UART.

`alu_uart_tb_top` wraps the real uart_axil_bridge + alu_harness (with
build-infer's alu_slot); a cocotb UART channel
(TBClasses.harness.cocotb_axil_bridge.make_uart_channel) carries the identical
ASCII byte stream the board's host sends, through the UNMODIFIED programs in
../../bin/alu_programs.py. One cocotb test per program, each on both build
profiles (LEAN, FULL).
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
_AREA = os.path.join(_REPO, "projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer")
_BIN = os.path.join(_AREA, "bin")
_FPGA_BIN = os.path.join(_REPO, "projects/fpga-systems/bin")
for _p in (_BIN, _FPGA_BIN):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel  # noqa: E402
from TBClasses.harness.byte_channel import TracingChannel           # noqa: E402
from uart_axi_bridge import UARTAxiBridge                           # noqa: E402
import alu_harness as ah                                            # noqa: E402
import alu_programs as progs                                        # noqa: E402

CLKS_PER_BIT = 4
SIM_TIME_BUDGET_MS = 100.0


async def _bringup(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.i_uart_rx.value = 1
    dut.aresetn.value = 0
    await Timer(200, units="ns")
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 20)
    chan = TracingChannel(make_uart_channel(dut, dut.aclk, CLKS_PER_BIT, log=dut._log))
    return ah.AluHarness(bridge=UARTAxiBridge(channel=chan))


async def _program(dut, name):
    h = await _bringup(dut)
    rep = await bridge(lambda: progs.PROGRAMS[name](h))()
    ms = get_sim_time("ns") / 1e6
    dut._log.info("%s (%.2f ms sim): %s", name, ms, rep.line())
    for f in rep.failures[:10]:
        dut._log.error("  %s", f)
    assert ms <= SIM_TIME_BUDGET_MS, (
        f"{name} used {ms:.1f} ms of sim time, over the {SIM_TIME_BUDGET_MS:.0f} ms budget -- "
        "raise the sim baud, do not shrink the program")
    assert rep.ok, f"{name}: " + "; ".join(rep.failures[:5])


@cocotb.test(timeout_time=150, timeout_unit="ms")
async def cocotb_test_program(dut):
    await _program(dut, os.environ["ALU_PROGRAM"])


PROFILES = ["LEAN", "FULL"]


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("program", list(progs.PROGRAMS))
def test_alu_harness_uart(request, program, profile):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "alu_uart_tb_top"
    filelist = "projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/dv/filelists/alu_uart_tb_top.f"
    os.environ.setdefault("CONVERTERS_ROOT",
                          os.path.join(repo_root, "projects/components/utility-ip/converters"))
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist)
    name = f"alu_harness_uart_{program}_{profile.lower()}"
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir, _BIN, _FPGA_BIN],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_alu_harness_uart",
        testcase="cocotb_test_program",
        parameters={"PROFILE": f'"{profile}"'},
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": dut_name, "REPO_ROOT": repo_root, "ALU_PROGRAM": program,
                   "COCOTB_LOG_LEVEL": "INFO",
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml")},
        compile_args=["-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
                      "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
                      "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM", "-Wno-VARHIDDEN",
                      "-Wno-IMPLICIT", "-Wno-CASEOVERLAP", "-Wno-MODDUP",
                      "-Wno-TIMESCALEMOD", "-Wno-PINCONNECTEMPTY"],
        keep_files=True, timescale="1ns/1ps")
