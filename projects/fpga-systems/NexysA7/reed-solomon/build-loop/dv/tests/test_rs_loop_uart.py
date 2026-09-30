# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against the RS loop harness in simulation, over UART.

`rs_loop_uart_tb_top` wraps the real uart_axil_bridge + rs_loop_harness; a
cocotb UART channel (TBClasses.harness.cocotb_axil_bridge.make_uart_channel)
drives the identical ASCII W/R byte stream the host sends to the FPGA, through
the UNMODIFIED programs in host/rs_loop_programs.py.

  uart_smoke     BUILD_ID + SCRATCH + PROFILE over the real bridge RTL
  uart_windows   the fabric's three windows are reachable and isolated
  uart_bypass    generator -> checkers with the codec bypassed: CRCs match
  uart_clean     no errors: every block ok, CRCs match, riBM == Euclid
  uart_correct   e = t per block: every block corrected with t symbols
  uart_over_t    e = t + 1: every block uncorrectable, riBM == Euclid
  uart_throttle  e = t under random checker ready
  uart_sequences the bin/seq_*.py sequences, unmodified, through the same
                 SequenceRunner the board's run_smoke.py drives

Blocks per run are few (2..4): a 32-bit UART transaction costs ~3000 sim
cycles, a block only 63.
"""
import os
import pathlib
import sys

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_REPO = os.environ["REPO_ROOT"]
_AREA = os.path.join(_REPO, "projects/fpga-systems/NexysA7/reed-solomon")
_HOST = os.path.join(_AREA, "build-loop/host")
_SEQ = os.path.join(_AREA, "bin")
_BRIDGE = os.path.join(_REPO, "projects/fpga-systems/bin")
_BRIDGE_TOML = os.path.join(_AREA, "rtl/bridges/configs/bridge_rs_loop_axil.toml")
for _p in (_HOST, _SEQ, _BRIDGE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel  # noqa: E402
from TBClasses.harness.byte_channel import TracingChannel           # noqa: E402
from uart_axi_bridge import UARTAxiBridge                           # noqa: E402
import rs_loop as rl                                                # noqa: E402
import rs_loop_programs as progs                                    # noqa: E402

# Matches rs_loop_uart_tb_top's default. 4 clocks per bit is 25 Mbaud at the
# 100 MHz sim clock, so the whole board campaign fits inside the 100 ms
# sim-time budget and no test has to shrink its parameters.
CLKS_PER_BIT = 4

# No single sim-harness test may exceed this much SIM time. If a test does not
# fit, the lever is the sim baud (CLKS_PER_BIT above), not the parameters and
# not a longer wall: a UART-bound cosim that overruns its wall can leave its
# assertions unexecuted, which reads as a pass. Checked, not assumed.
SIM_TIME_BUDGET_MS = 100.0


def _check_sim_budget(dut, label):
    ms = get_sim_time("ns") / 1e6
    dut._log.info("%s: %.2f ms of sim time (budget %.0f ms, %.0f%%)",
                  label, ms, SIM_TIME_BUDGET_MS, 100.0 * ms / SIM_TIME_BUDGET_MS)
    assert ms <= SIM_TIME_BUDGET_MS, (
        f"{label} used {ms:.1f} ms of sim time, over the {SIM_TIME_BUDGET_MS:.0f} ms budget -- "
        f"raise the sim baud (CLKS_PER_BIT is {CLKS_PER_BIT}), do not shrink the test")
T = 8   # the profile's t; the smoke test also reads it back from PROFILE


def _fabric_windows():
    """(name, base) per slave window, PARSED from the bridge config.

    The window bases have one home -- bridge_rs_loop_axil.toml, which the
    generator reads -- so a test that restated them would be a second owner
    that drifts the day a window moves (handbook: one-source-config).
    """
    import re
    text = pathlib.Path(_BRIDGE_TOML).read_text()
    out, name = [], None
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        m = re.match(r'name\s*=\s*"([^"]+)"', line)
        if m:
            name = m.group(1)
        m = re.match(r'base_addr\s*=\s*"(0x[0-9A-Fa-f]+)"', line)
        if m and name:
            out.append((name, int(m.group(1), 16)))
    assert len(out) >= 2, f"parsed {len(out)} windows from {_BRIDGE_TOML}"
    return out


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
    _check_sim_budget(dut, label)
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


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_uart_windows(dut):
    """The fabric's three windows are reachable and isolated.

    A reserved window must read 0 (the harness ties its PRDATA low) and must
    COMPLETE rather than hang. If the host address is truncated anywhere
    between the UART bridge and the fabric, every window folds back into the
    low one and these reads return the loop block's BUILD_ID instead -- which
    is exactly what a board probe found after the fabric first went in.
    """
    drv, _ = await _bringup(dut)
    windows = _fabric_windows()
    # the loop window is read again at the end: it must still answer after the
    # reserved ones have been poked
    plan = windows + [windows[0]]
    reads = await cocotb.external(lambda: [(n, a, drv.bridge.read(a)) for n, a in plan])()
    for name, addr, val in reads:
        dut._log.info("window %-24s @0x%05X -> 0x%08X", name, addr, val)
    assert reads[0][2] == rl.EXPECTED_BUILD_ID, (
        f"the loop window ({reads[0][0]}) read 0x{reads[0][2]:08X}")
    for name, addr, val in reads[1:-1]:
        assert val == 0, (f"the reserved window {name} @0x{addr:05X} read 0x{val:08X}, not 0 -- "
                          "the host address is being truncated before the fabric")
    assert reads[-1][2] == rl.EXPECTED_BUILD_ID, "the loop window stopped answering after the others"


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


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_uart_sequences(dut):
    """Run the RS loop SEQUENCES -- unmodified -- against the sim.

    The other tests prove the authored-once PROGRAMS are portable. This proves
    the layer above them: the `seq_*.py` files that `bin/run_smoke.py` drives
    on the board, executed here through the same SequenceRunner with the same
    dependency resolution, `board=None`, and the cocotb UART as the transport.
    No sequence knows the difference, which is the whole point -- without this
    test a sequence-layer bug is invisible in sim, and the handbook records a
    flow where exactly that happened (the cosim reimplemented the campaigns
    inline and the shared runner was never exercised).

    There are NO deviations. The sequences run on their own defaults, which is
    what `bin/run_smoke.py --sequences init smoke sweep` does on the board with
    no flags: 16 blocks per point and the full e = 0 .. 2t+2 sweep. The earlier
    version of this test passed blocks=2 and a three-point sweep because the
    UART was the bottleneck at 16 clocks per bit -- the wrong lever. The sim
    transport runs at 4 clocks per bit, which is what makes the real campaign
    fit the 100 ms sim-time budget.
    """
    drv, _ = await _bringup(dut)

    def prog():
        from sequence import SequenceContext, SequenceRunner

        ctx = SequenceContext(
            bus=drv,
            board=None,                  # sim: no board, same sequences
            params={},                   # and the same defaults: no deviation
            log=dut._log.info,
        )
        runner = SequenceRunner(ctx=ctx).discover(_SEQ)
        return runner.run(["init", "smoke", "sweep"])

    report = await cocotb.external(prog)()
    dut._log.info("sequence run:\n%s", report.summary())
    _check_sim_budget(dut, "sequences (init -> smoke -> sweep, board defaults)")
    assert report.ok, f"the RS loop sequences failed in sim:\n{report.summary()}"


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


def test_rs_loop_uart_windows(request):
    _run("cocotb_test_uart_windows")


def test_rs_loop_uart_sequences(request):
    _run("cocotb_test_uart_sequences")


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
