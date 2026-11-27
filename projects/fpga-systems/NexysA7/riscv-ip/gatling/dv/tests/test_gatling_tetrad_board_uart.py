# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against gatling build-tetrad in simulation, over UART.

The toplevel is `gatling_tetrad_rig`, the board top minus its clocking: the
real uart_axil_bridge, AXIL split, gatling_mem_bram, cell harness and
gatling_tetrad (bf16 ALU profile, as built). A cocotb UART channel carries the
identical byte stream the board's host sends, through the UNMODIFIED programs
in ../../bin/gatling_tetrad_programs.py. The sim runs the tetrad program at a
smaller N than the board (sim-time budget); everything else is the same run.
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
import gatling_tetrad_board as tb_board                             # noqa: E402
import gatling_tetrad_programs as progs                             # noqa: E402
from TBClasses.shared.verilator_cfg import FIELD_COMBO_VLT  # noqa: E402

CLKS_PER_BIT = 4
SIM_TIME_BUDGET_MS = 200.0
PROGRAMS = {"smoke": None, "tetrad": 40}     # tetrad: N ACCUMULATE invocations per cell;
#                                             40 overfills both 32-line memories (refill + PUSH waits)


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_program(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.i_uart_rx.value = 1
    dut.aresetn.value = 0
    await Timer(200, units="ns")
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 20)
    chan = TracingChannel(make_uart_channel(dut, dut.aclk, CLKS_PER_BIT, log=dut._log))
    k = tb_board.TetradBoard(bridge=UARTAxiBridge(channel=chan))
    prog = os.environ["GATLING_PROGRAM"]
    seed = int(os.environ.get("SEED", "1"))
    if prog == "smoke":
        rep = await bridge(lambda: progs.smoke(k))()
    else:
        rep = await bridge(lambda: progs.tetrad(k, count=PROGRAMS[prog], seed=seed,
                                                timeout_s=3600.0))()
    ms = get_sim_time("ns") / 1e6
    dut._log.info("%s (%.2f ms sim, seed %d): %s", prog, ms, seed, rep.line())
    for row in rep.rows:
        dut._log.info("  %s", row)
    with open(os.environ["REPORT_FILE"], "w") as fh:     # the verdict outlives the sim log
        fh.write(f"{prog} ({ms:.2f} ms sim, seed {seed}): {rep.line()}\n")
        fh.writelines(f"  {row}\n" for row in rep.rows)
        fh.writelines(f"  FAIL {f}\n" for f in rep.failures)
    assert ms <= SIM_TIME_BUDGET_MS, f"{prog} used {ms:.1f} ms of sim time, over budget"
    assert rep.ok, f"{prog}: " + "; ".join(rep.failures[:5])


@pytest.mark.parametrize("program", list(PROGRAMS))
def test_gatling_tetrad_board_uart(request, program):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    for var, rel in (("CONVERTERS_ROOT", "projects/components/utility-ip/converters"),
                     ("GATLING_ROOT", "projects/components/riscv-ip/gatling-rv32i"),
                     ("RV32I_COMMON_ROOT", "projects/components/riscv-ip/common-rv32i")):
        os.environ.setdefault(var, os.path.join(repo_root, rel))
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/fpga-systems/NexysA7/riscv-ip/gatling/dv/filelists/gatling_tetrad_rig_tb.f")
    name = f"gatling_tetrad_board_uart_{program}"
    sim_build = sim_build_path(tests_dir, "gatling_tetrad_board_uart")   # one build, every cell
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    seed = os.environ.get("SEED", "1")
    run(python_search=[tests_dir, _BIN, _FPGA_BIN],
        verilog_sources=verilog_sources, includes=includes,
        toplevel="gatling_tetrad_rig", module="test_gatling_tetrad_board_uart",
        testcase="cocotb_test_program",
        parameters={"CLKS_PER_BIT": CLKS_PER_BIT},
        sim_build=sim_build, simulator="verilator",
        extra_env={"DUT": "gatling_tetrad_rig", "REPO_ROOT": repo_root,
                   "GATLING_PROGRAM": program, "SEED": seed, "COCOTB_LOG_LEVEL": "INFO",
                   "REPORT_FILE": os.path.join(log_dir, f"report_{name}.txt"),
                   "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml")},
        compile_args=[FIELD_COMBO_VLT, "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
                      "-Wno-CASEINCOMPLETE", "-Wno-DECLFILENAME", "-Wno-UNUSEDSIGNAL",
                      "-Wno-UNUSEDPARAM", "-Wno-TIMESCALEMOD", "-Wno-PINCONNECTEMPTY"],
        keep_files=True, timescale="1ns/1ps")
