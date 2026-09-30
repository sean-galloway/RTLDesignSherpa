# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against the RS loop harness in simulation, over UART.

`rs_loop_uart_tb_top` wraps the real uart_axil_bridge + rs_loop_harness; a
cocotb UART channel (TBClasses.harness.cocotb_axil_bridge.make_uart_channel)
drives the identical ASCII W/R byte stream the host sends to the FPGA, through
the UNMODIFIED programs in host/rs_loop_programs.py.

  uart_smoke     BUILD_ID + SCRATCH + PROFILE over the real bridge RTL
  uart_bypass    generator -> checkers with the codec bypassed: CRCs match
  uart_clean     no errors: every block ok, CRCs match, riBM == Euclid
  uart_correct   e = t per block: every block corrected with t symbols
  uart_over_t    e = t + 1: every block uncorrectable, riBM == Euclid
  uart_throttle  e = t under random checker ready

Blocks per run are few (2..4): a 32-bit UART transaction costs ~3000 sim
cycles, a block only 63.
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
_HOST = os.path.join(_REPO, "projects/fpga-systems/NexysA7/reed-solomon/build-loop/host")
_BRIDGE = os.path.join(_REPO, "projects/fpga-systems/bin")
for _p in (_HOST, _BRIDGE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel  # noqa: E402
from TBClasses.harness.byte_channel import TracingChannel           # noqa: E402
from uart_axi_bridge import UARTAxiBridge                           # noqa: E402
import rs_loop as rl                                                # noqa: E402
import rs_loop_programs as progs                                    # noqa: E402

CLKS_PER_BIT = 16
T = 8   # the profile's t; the smoke test also reads it back from PROFILE


async def _bringup(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    dut.i_uart_rx.value = 1
    dut.aresetn.value = 0
    await Timer(200, units="ns")
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 20)
    chan = TracingChannel(make_uart_channel(dut, dut.aclk, CLKS_PER_BIT, log=dut._log))
    drv = rl.RsLoopDriver(bridge=UARTAxiBridge(channel=chan))
    return drv, chan


def _report(dut, label, r):
    bad = progs.verdict(r, T)
    dut._log.info("%s: %d blocks in %d cycles (%.1f/block); riBM ok/corr/unc=%d/%d/%d sym=%d crc_ok=%s; "
                  "Euclid ok/corr/unc=%d/%d/%d sym=%d crc_ok=%s; inj=%d; cmp data/status=%d/%d over %d beats",
                  label, r.blocks, r.cycles, r.cycles_per_block,
                  r.a.blk_ok, r.a.blk_corr, r.a.blk_unc, r.a.sym_corr, r.a.crc_ok,
                  r.b.blk_ok, r.b.blk_corr, r.b.blk_unc, r.b.sym_corr, r.b.crc_ok,
                  r.inj_symbols, r.cmp_data_mismatch, r.cmp_status_mismatch, r.cmp_beats)
    assert not bad, f"{label}: " + "; ".join(bad)


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_uart_smoke(dut):
    drv, chan = await _bringup(dut)
    r = await cocotb.external(lambda: progs.smoke(drv))()
    dut._log.info("smoke: build_id=0x%08X profile=%s ok=%s", r.build_id, r.profile, r.ok)
    assert r.build_id == rl.EXPECTED_BUILD_ID, f"BUILD_ID 0x{r.build_id:08X}"
    assert r.ok, f"smoke failed: {r.scratch}"
    assert r.profile == dict(n=252, t=T, m=8, spb=4), r.profile
    tx = chan.tx_bytes()
    assert tx.startswith((b"R ", b"W ")), f"unexpected first bytes: {tx[:8]!r}"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_bypass(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.bypass(drv, blocks=3))()
    _report(dut, "bypass", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_clean(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, rl.RsLoopDriver.INJ_NONE, blocks=3))()
    _report(dut, "clean", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_correct(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=T, blocks=4))()
    _report(dut, f"e={T}", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_over_t(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=T + 1, blocks=4))()
    _report(dut, f"e={T + 1}", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_throttle(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=T, blocks=3,
                                                throttle=True))()
    _report(dut, f"e={T} throttled", r)


# =============================================================================
# pytest wrappers
# =============================================================================
def _run(testcase: str):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "rs_loop_uart_tb_top"
    filelist_path = "projects/fpga-systems/NexysA7/reed-solomon/build-loop/dv/filelists/rs_loop_uart_tb_top.f"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist_path)
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
        "-Wno-IMPLICIT", "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-TIMESCALEMOD",
    ]
    run(python_search=[tests_dir, _HOST],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_rs_loop_uart",
        testcase=testcase,
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, compile_args=compile_args,
        keep_files=True, timescale="1ns/1ps")


def test_rs_loop_uart_smoke(request):
    _run("cocotb_test_uart_smoke")


def test_rs_loop_uart_bypass(request):
    _run("cocotb_test_uart_bypass")


def test_rs_loop_uart_clean(request):
    _run("cocotb_test_uart_clean")


def test_rs_loop_uart_correct(request):
    _run("cocotb_test_uart_correct")


def test_rs_loop_uart_over_t(request):
    _run("cocotb_test_uart_over_t")


def test_rs_loop_uart_throttle(request):
    _run("cocotb_test_uart_throttle")
