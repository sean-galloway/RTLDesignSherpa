# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against the cdc_demo harness in simulation, over UART.

This is the sim half of the silicon/sim equivalence. `cdc_demo_uart_tb_top` wraps
the FULL harness (real uart_axil_bridge + cdc_demo_harness + 4x
cdc_counter_domain); a cocotb UARTMaster/Monitor drives the identical ASCII W/R
byte stream the host sends to the FPGA. The per-counter ctr_clk[i] are driven
here at co-prime periods (the MMCM/BUFGMUX clock tree in cdc_demo_top does not
simulate in Verilator — it is the "analog" part, replaced behaviorally).

The synchronous host programs (cdc_programs.*) run in a worker thread via
cocotb.external and talk to the sim through CocotbUartChannel — the UNMODIFIED
programs the FPGA CLI runs. Tests:

  * uart_smoke    — BUILD_ID + SCRATCH round-trip + per-counter snapshot over the
                    real bridge RTL. Proves the byte protocol round-trips in sim.
  * uart_press    — HOST_PRESS injection advances VALUE and PRESS_COUNT (NO_CDC
                    readback, deterministic).
  * uart_cfg_load — CFG_LOAD reloads VALUE to INIT, leaving PRESS_COUNT intact.
  * uart_cdc_mode — every CDC_MODE code round-trips through the CSR fan-out.
"""

import os
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_REPO = os.environ["REPO_ROOT"]
_HOST = os.path.join(_REPO, "projects/NexysA7/cdc_counter_display/host")
_BRIDGE = os.path.join(_REPO, "projects/components/converters/bin")
for _p in (_HOST, _BRIDGE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel  # noqa: E402
from TBClasses.harness.byte_channel import TracingChannel           # noqa: E402
from uart_axi_bridge import UARTAxiBridge                           # noqa: E402
import cdc_demo as cd                                               # noqa: E402
import cdc_programs as progs                                        # noqa: E402

# Matches cdc_demo_uart_tb_top default (UART_CLKS_PER_BIT).
CLKS_PER_BIT = 16
# Per-counter source-clock periods (ns). Co-prime-ish so the four domains are
# mutually asynchronous, and fast enough that HOST_PRESS pulses land well within
# one UART transaction's worth of sys_clk cycles.
CTR_CLK_PERIODS_NS = (11, 29, 67, 128)


async def _bringup(dut):
    """Clock + reset + four async ctr clocks + UART pump; returns a
    CdcDemoDriver whose transport is the sim UART (traced)."""
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    for i, per in enumerate(CTR_CLK_PERIODS_NS):
        cocotb.start_soon(Clock(getattr(dut, f"i_ctr_clk{i}"), per,
                                units="ns").start())

    dut.i_uart_rx.value = 1  # UART idle = high
    dut.aresetn.value = 0
    await Timer(200, units="ns")
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 20)

    chan = TracingChannel(
        make_uart_channel(dut, dut.aclk, CLKS_PER_BIT, log=dut._log))
    drv = cd.CdcDemoDriver(bridge=UARTAxiBridge(channel=chan))
    return drv, chan


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_uart_smoke(dut):
    drv, chan = await _bringup(dut)
    r = await cocotb.external(lambda: progs.smoke(drv))()
    dut._log.info("smoke: build_id=0x%08X ok=%s", r.build_id, r.ok)
    assert r.build_id == cd.EXPECTED_BUILD_ID, f"BUILD_ID 0x{r.build_id:08X}"
    assert r.ok, f"smoke failed: scratch={r.scratch}"
    # Wire sanity: the host->device stream is well-formed W/R ASCII lines.
    tx = chan.tx_bytes()
    assert tx.count(b"\n") >= 8, "too few UART commands captured"
    assert tx.startswith((b"R ", b"W ")), f"unexpected first bytes: {tx[:8]!r}"


@cocotb.test(timeout_time=80, timeout_unit="ms")
async def cocotb_test_uart_press(dut):
    drv, _chan = await _bringup(dut)
    r = await cocotb.external(lambda: progs.press(drv, counter=0, count=5))()
    dut._log.info("press: 0x%04X -> 0x%04X (exp 0x%04X) dPRESS=%d",
                  r.value_before, r.value_after, r.value_expected, r.press_delta)
    assert r.ok, (f"press failed: value 0x{r.value_after:04X} exp "
                  f"0x{r.value_expected:04X}, press_delta {r.press_delta}")


@cocotb.test(timeout_time=80, timeout_unit="ms")
async def cocotb_test_uart_cfg_load(dut):
    drv, _chan = await _bringup(dut)
    r = await cocotb.external(lambda: progs.cfg_load(drv, counter=1))()
    dut._log.info("cfg_load: mid=0x%04X reload=0x%04X (target 0x%04X)",
                  r.value_mid, r.value_reload, r.reload_target)
    assert r.ok, (f"cfg_load failed: reload 0x{r.value_reload:04X} target "
                  f"0x{r.reload_target:04X}, press {r.press_reload}!={r.press_mid}")


@cocotb.test(timeout_time=80, timeout_unit="ms")
async def cocotb_test_uart_cdc_mode(dut):
    drv, _chan = await _bringup(dut)
    r = await cocotb.external(lambda: progs.cdc_mode_check(drv, counter=2))()
    dut._log.info("cdc_mode: %s", r.checks)
    assert r.ok, f"cdc_mode round-trip failed: {r.checks}"


# =============================================================================
# pytest wrappers
# =============================================================================
def _run(testcase: str):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "cdc_demo_uart_tb_top"
    filelist_path = ("projects/NexysA7/cdc_counter_display/"
                     "dv/filelists/cdc_demo_uart_tb_top.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, testcase)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "REPO_ROOT": repo_root,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}.xml"),
    }
    compile_args = [
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM", "-Wno-VARHIDDEN",
        "-Wno-IMPLICIT", "-Wno-CASEOVERLAP", "-Wno-MODDUP",
    ]
    run(python_search=[tests_dir, _HOST],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_cdc_demo_uart",
        testcase=testcase,
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, compile_args=compile_args,
        keep_files=True, timescale="1ns/1ps")


def test_cdc_demo_uart_smoke(request):
    _run("cocotb_test_uart_smoke")


def test_cdc_demo_uart_press(request):
    _run("cocotb_test_uart_press")


def test_cdc_demo_uart_cfg_load(request):
    _run("cocotb_test_uart_cfg_load")


def test_cdc_demo_uart_cdc_mode(request):
    _run("cocotb_test_uart_cdc_mode")
