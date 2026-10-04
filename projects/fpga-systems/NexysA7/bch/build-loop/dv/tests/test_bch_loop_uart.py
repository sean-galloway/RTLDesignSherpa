# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Run the SAME host programs against the BCH loop harness in simulation, over UART.

`bch_loop_uart_tb_top` wraps the real uart_axil_bridge + bch_loop_harness; a
cocotb UART channel (TBClasses.harness.cocotb_axil_bridge.make_uart_channel)
drives the identical ASCII W/R byte stream the host sends to the FPGA, through
the UNMODIFIED programs in host/bch_loop_programs.py.

  uart_smoke     BUILD_ID + SCRATCH + PROFILE over the real bridge RTL
  uart_windows   the fabric's three windows are reachable and isolated
  uart_bypass    generator -> checker with the codec bypassed
  uart_clean     no errors: every block ok
  uart_correct   e = t per block: every block corrected with t bits
  uart_over_t    e = t + 1: every block uncorrectable
  uart_throttle  e = t under random checker ready
  uart_axi4      the IFACE = "AXI4" build: memory-to-memory job chain
  uart_observers the axis4 interface observer on the four AXIS seams
  uart_axi4_observers
                 the IFACE = "AXI4" build's master observer
  uart_sequences the bin/seq_*.py sequences, unmodified
  uart_random    the random campaign on its board defaults

Blocks per run are few (2..4): a 32-bit UART transaction costs ~3000 sim
cycles, and a BCH block is 132 beats.
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
_AREA = os.path.join(_REPO, "projects/fpga-systems/NexysA7/bch")
_HOST = os.path.join(_AREA, "build-loop/host")
_SEQ = os.path.join(_AREA, "bin")
_BRIDGE = os.path.join(_REPO, "projects/fpga-systems/bin")
_BRIDGE_TOML = os.path.join(_AREA, "rtl/bridges/configs/bridge_bch_loop_axil.toml")
for _p in (_HOST, _SEQ, _BRIDGE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel  # noqa: E402
from TBClasses.harness.byte_channel import TracingChannel           # noqa: E402
from uart_axi_bridge import UARTAxiBridge                           # noqa: E402
import bch_loop as bl                                               # noqa: E402
import bch_loop_programs as progs                                   # noqa: E402

CLKS_PER_BIT = 4
SIM_TIME_BUDGET_MS = 100.0
T = 8


def _check_sim_budget(dut, label):
    ms = get_sim_time("ns") / 1e6
    dut._log.info("%s: %.2f ms of sim time (budget %.0f ms, %.0f%%)",
                  label, ms, SIM_TIME_BUDGET_MS, 100.0 * ms / SIM_TIME_BUDGET_MS)
    assert ms <= SIM_TIME_BUDGET_MS, (
        f"{label} used {ms:.1f} ms of sim time, over the {SIM_TIME_BUDGET_MS:.0f} ms budget -- "
        f"raise the sim baud (CLKS_PER_BIT is {CLKS_PER_BIT}), do not shrink the test")


def _fabric_windows():
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
    drv = bl.BchLoopDriver(bridge=UARTAxiBridge(channel=chan))
    return drv, chan


def _report(dut, label, r):
    _check_sim_budget(dut, label)
    bad = progs.verdict(r, T)
    dut._log.info("%s: %d blocks in %d cycles (%.1f/block); ok/corr/unc=%d/%d/%d sym=%d data_err=%s; "
                  "inj=%d",
                  label, r.blocks, r.cycles, r.cycles_per_block,
                  r.a.blk_ok, r.a.blk_corr, r.a.blk_unc, r.a.sym_corr, r.a.data_err,
                  r.inj_symbols)
    assert not bad, f"{label}: " + "; ".join(bad)


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_uart_smoke(dut):
    drv, chan = await _bringup(dut)
    r = await cocotb.external(lambda: progs.smoke(drv))()
    dut._log.info("smoke: build_id=0x%08X profile=%s ok=%s", r.build_id, r.profile, r.ok)
    assert r.build_id == bl.EXPECTED_BUILD_ID, f"BUILD_ID 0x{r.build_id:08X}"
    assert r.ok, f"smoke failed: {r.scratch}"
    assert r.profile == dict(n=4224, k=4120, t=T, m=13, spb=4), r.profile
    tx = chan.tx_bytes()
    assert tx.startswith((b"R ", b"W ")), f"unexpected first bytes: {tx[:8]!r}"


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cocotb_test_uart_windows(dut):
    drv, _ = await _bringup(dut)
    windows = _fabric_windows()
    plan = windows + [windows[0]]
    reads = await cocotb.external(lambda: [(n, a, drv.bridge.read(a)) for n, a in plan])()
    for name, addr, val in reads:
        dut._log.info("window %-24s @0x%05X -> 0x%08X", name, addr, val)
    assert reads[0][2] == bl.EXPECTED_BUILD_ID, (
        f"the loop window ({reads[0][0]}) read 0x{reads[0][2]:08X}")
    for name, addr, val in reads[1:-1]:
        assert val != bl.EXPECTED_BUILD_ID, (
            f"window {name} @0x{addr:05X} read back BUILD_ID -- "
            "the host address is being truncated before the fabric")
    assert reads[-1][2] == bl.EXPECTED_BUILD_ID, "the loop window stopped answering after the others"

    caps = await cocotb.external(drv.observer_caps)()
    dut._log.info("observer caps: %s", caps)
    assert caps["axis"]["bus_meter"] and caps["axis"]["rd_ports"] == 4, caps["axis"]
    assert caps["axi4"]["rd_ports"] == 0 and caps["axi4"]["caps0"] == 0, caps["axi4"]


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_bypass(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.bypass(drv, blocks=3))()
    _report(dut, "bypass", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_clean(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, bl.BchLoopDriver.INJ_NONE, blocks=3))()
    _report(dut, "clean", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_correct(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=T, blocks=4))()
    _report(dut, f"e={T}", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_over_t(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=T + 1, blocks=4))()
    _report(dut, f"e={T + 1}", r)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_throttle(dut):
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=T, blocks=3,
                                                throttle=True))()
    _report(dut, f"e={T} throttled", r)


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_uart_sequences(dut):
    drv, _ = await _bringup(dut)

    def prog():
        from sequence import SequenceContext, SequenceRunner

        ctx = SequenceContext(
            bus=drv,
            board=None,
            params={},
            log=dut._log.info,
        )
        runner = SequenceRunner(ctx=ctx).discover(_SEQ)
        return runner.run(["init", "smoke", "sweep"])

    report = await cocotb.external(prog)()
    dut._log.info("sequence run:\n%s", report.summary())
    _check_sim_budget(dut, "sequences (init -> smoke -> sweep, board defaults)")
    assert report.ok, f"the BCH loop sequences failed in sim:\n{report.summary()}"


@cocotb.test(timeout_time=900, timeout_unit="ms")
async def cocotb_test_uart_random(dut):
    drv, _ = await _bringup(dut)

    def prog():
        from sequence import SequenceContext, SequenceRunner

        ctx = SequenceContext(bus=drv, board=None, params={}, log=dut._log.info)
        runner = SequenceRunner(ctx=ctx).discover(_SEQ)
        return runner.run(["init", "random"])

    report = await cocotb.external(prog)()
    dut._log.info("random campaign:\n%s", report.summary())
    _check_sim_budget(dut, "random campaign (64 runs, board defaults)")
    assert report.ok, f"the random campaign failed in sim:\n{report.summary()}"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_axi4(dut):
    drv, _ = await _bringup(dut)
    topo = await cocotb.external(drv.topology)()
    assert topo["iface"] == "AXI4", f"expected an AXI4 build, TOPOLOGY says {topo['iface']}"
    assert topo["decoders"] == 1, f"the AXI4 chain carries one decoder, got {topo['decoders']}"

    for label, mode, count in (("clean", bl.BchLoopDriver.INJ_COUNT, 0),
                               (f"e={T}", bl.BchLoopDriver.INJ_COUNT, T),
                               (f"e={T + 1}", bl.BchLoopDriver.INJ_COUNT, T + 1)):
        r = await cocotb.external(lambda m=mode, c=count: progs.run(drv, m, count=c, blocks=3))()
        assert (r.axi4_stage & progs.AXI4_STAGE_MASK) == progs.AXI4_STAGE_MASK, (
            f"AXI4 {label}: chain stopped at stage 0x{r.axi4_stage:02X}, "
            f"wanted 0x{progs.AXI4_STAGE_MASK:02X}")
        assert not r.axi4_overflow, f"AXI4 {label}: run refused as oversized"
        _report(dut, f"AXI4 {label}", r)

    over = bl.BchLoopDriver.INJ_COUNT
    r = await cocotb.external(lambda: progs.run(drv, over, count=0, blocks=4096))()
    assert r.axi4_overflow, "an oversized AXI4 run should set STATUS.axi4_overflow and never kick"
    assert r.axi4_stage == 0x00, f"a refused run must not start any stage, got 0x{r.axi4_stage:02X}"
    bad = progs.verdict(r, T)
    assert any("refused" in b for b in bad), f"the verdict should name the refusal; it said {bad}"
    dut._log.info("AXI4 oversized run correctly refused: stage=0x%02X", r.axi4_stage)


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_observers(dut):
    drv, _ = await _bringup(dut)
    prof = await cocotb.external(drv.profile)()
    s = prof["spb"]
    k_beats = -(-prof["k"] // (s * 8))
    cw_beats = -(-prof["n"] // (s * 8))
    blocks = 3

    caps = await cocotb.external(drv.observer_caps)()
    dut._log.info("observer caps: %s", caps)
    assert caps["axis"]["bus_meter"] and not caps["axis"]["mon_taps"], caps["axis"]
    assert caps["axis"]["rd_ports"] == 4, caps["axis"]
    assert caps["axi4"]["rd_ports"] == 0, caps["axi4"]

    r = await cocotb.external(
        lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=0, blocks=blocks,
                          iface_obs=True))()
    _report(dut, "observers: clean", r)
    obs = r.iface_obs["axis"]
    want = {"msg_in": blocks * k_beats, "cw_out": blocks * cw_beats,
            "cw_in": blocks * cw_beats, "msg_out": blocks * k_beats}
    for seam, beats in want.items():
        d = obs[seam]
        dut._log.info("  %-7s %d beats, %d packets, %d bytes, util %.1f%% ",
                      seam, d["beats"], d["packets"], d["bytes"],
                      100.0 * d["utilisation"])
        assert d["beats"] == beats, f"{seam}: {d['beats']} beats, want {beats}"
        assert d["productive"] == beats, f"{seam}: productive {d['productive']} != beats {d['beats']}"
        assert d["packets"] == blocks, f"{seam}: {d['packets']} packets, want {blocks}"
        assert d["bytes"] == beats * s, f"{seam}: {d['bytes']} bytes, want {beats * s}"
        assert d["window"] > 0, f"{seam}: empty bucket window"
    assert r.obs["cw_out"]["productive"] == obs["cw_out"]["productive"], (
        f"old meter {r.obs['cw_out']['productive']} != observer {obs['cw_out']['productive']}")

    obs2 = (await cocotb.external(
        lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=0, blocks=blocks,
                          iface_obs=True))()).iface_obs["axis"]
    for seam in want:
        assert obs2[seam]["beats"] == want[seam], (
            f"{seam}: second run read {obs2[seam]['beats']} beats -- meters are accumulating")
    _check_sim_budget(dut, "observers")


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_axi4_observers(dut):
    drv, _ = await _bringup(dut)
    topo = await cocotb.external(drv.topology)()
    assert topo["iface"] == "AXI4", f"expected an AXI4 build, TOPOLOGY says {topo['iface']}"
    prof = await cocotb.external(drv.profile)()
    s = prof["spb"]
    k_beats = -(-prof["k"] // (s * 8))
    cw_beats = -(-prof["n"] // (s * 8))
    blocks = 3

    caps = await cocotb.external(drv.observer_caps)()
    dut._log.info("observer caps: %s", caps)
    assert caps["axi4"]["bus_meter"] and not caps["axi4"]["mon_taps"], caps["axi4"]
    assert (caps["axi4"]["rd_ports"], caps["axi4"]["wr_ports"]) == (2, 2), caps["axi4"]

    r = await cocotb.external(
        lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=0, blocks=blocks,
                          iface_obs=True))()
    _report(dut, "AXI4 observers: clean", r)
    obs = r.iface_obs["axi4"]
    want = {"enc_rd": blocks * k_beats, "dec_rd": blocks * cw_beats,
            "enc_wr": blocks * cw_beats, "dec_wr": blocks * k_beats}
    for port, beats in want.items():
        d = obs[port]
        dut._log.info("  %-7s productive %d, %d timed xacts", port, d["productive"], d["hist_total"])
        assert d["productive"] == beats, f"{port}: productive {d['productive']}, want {beats}"
        assert d["hist_total"] > 0, f"{port}: no transactions timed"

    hist = await cocotb.external(lambda: drv.axi4_observer(hist=True))()
    for hm, label in ((0, "AR->first-R"), (1, "AR->RLAST")):
        total = hist["enc_rd"]["hist_total"]
        binned = sum(hist["enc_rd"]["hist"][hm])
        dut._log.info("  enc_rd %s: bins sum %d over %d timed", label, binned, total)
        assert binned == total, f"enc_rd {label}: bins sum {binned} != hist_total {total}"

    axis = await cocotb.external(drv.axis_observer)()
    assert axis["msg_in"]["beats"] == blocks * k_beats, axis["msg_in"]
    assert axis["msg_out"]["beats"] == blocks * k_beats, axis["msg_out"]
    assert axis["msg_in"]["beats"] == obs["enc_rd"]["productive"], (
        f"axis msg_in {axis['msg_in']['beats']} != axi4 enc_rd {obs['enc_rd']['productive']}")
    assert axis["msg_out"]["beats"] == obs["dec_wr"]["productive"], (
        f"axis msg_out {axis['msg_out']['beats']} != axi4 dec_wr {obs['dec_wr']['productive']}")
    assert axis["cw_out"]["beats"] == 0 and axis["cw_in"]["beats"] == 0, (
        f"codec seams should be tied in AXI4 flavour, got cw_out={axis['cw_out']['beats']} "
        f"cw_in={axis['cw_in']['beats']}")
    _check_sim_budget(dut, "AXI4 observers")


def _slope_stats(small, large, key):
    a, b = small.obs[key], large.obs[key]
    d_prod = b["productive"] - a["productive"]
    d_win = b["window"] - a["window"]
    d_blocks = large.blocks - small.blocks
    return d_prod, d_win, d_prod / d_win, d_win / d_blocks


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_bw_slope(dut):
    drv, _ = await _bringup(dut)
    prof = await cocotb.external(drv.profile)()
    n, k, s = prof["n"], prof["k"], prof["spb"]
    small = await cocotb.external(
        lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=0, blocks=16))()
    large = await cocotb.external(
        lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=0, blocks=64))()
    dut._log.info("AXIS slope 16 -> 64 blocks:\n" +
                  progs.bandwidth_slope(small, large, n, k, s))
    cw_beats = -(-n // (s * 8))
    for key in ("cw_out", "cw_in"):
        d_prod, d_win, util, per_blk = _slope_stats(small, large, key)
        assert d_prod == d_win == 48 * cw_beats, (
            f"{key}: {d_prod} beats in {d_win} cycles over 48 blocks")
    _check_sim_budget(dut, "AXIS slope")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_axi4_bw_slope(dut):
    drv, _ = await _bringup(dut)
    topo = await cocotb.external(drv.topology)()
    assert topo["iface"] == "AXI4", f"expected an AXI4 build, TOPOLOGY says {topo['iface']}"
    prof = await cocotb.external(drv.profile)()
    n, k, s = prof["n"], prof["k"], prof["spb"]
    small = await cocotb.external(
        lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=0, blocks=16))()
    large = await cocotb.external(
        lambda: progs.run(drv, bl.BchLoopDriver.INJ_COUNT, count=0, blocks=64))()
    dut._log.info("AXI4 slope 16 -> 64 blocks:\n" +
                  progs.bandwidth_slope(small, large, n, k, s))
    cw_beats = -(-n // (s * 8))
    msg_beats = -(-k // (s * 8))
    for key, beats in (("cw_out", 48 * cw_beats), ("cw_in", 48 * cw_beats),
                       ("in", 48 * msg_beats), ("out", 48 * msg_beats)):
        d_prod, d_win, util, per_blk = _slope_stats(small, large, key)
        assert d_prod == beats, f"{key}: {d_prod} beats, want {beats}"
    _check_sim_budget(dut, "AXI4 slope")


def _run(testcase: str, parameters=None, suffix=""):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "bch_loop_uart_tb_top"
    filelist_path = "projects/fpga-systems/NexysA7/bch/build-loop/dv/filelists/bch_loop_uart_tb_top.f"
    verilog_sources, includes = get_sources_from_filelist(repo_root=repo_root, filelist_path=filelist_path)
    sim_build = sim_build_path(tests_dir, testcase + suffix)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    extra_env = {
        "DUT": dut_name,
        "REPO_ROOT": repo_root,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{testcase}{suffix}.xml"),
    }
    compile_args = [
        "-Wno-MULTIDRIVEN", "-Wno-UNUSED", "-Wno-UNDRIVEN", "-Wno-WIDTH",
        "-Wno-CASEINCOMPLETE", "-Wno-SELRANGE", "-Wno-DECLFILENAME",
        "-Wno-UNUSEDSIGNAL", "-Wno-UNUSEDPARAM", "-Wno-VARHIDDEN",
        "-Wno-IMPLICIT", "-Wno-CASEOVERLAP", "-Wno-MODDUP", "-Wno-TIMESCALEMOD",
    ]
    run(python_search=[tests_dir, _HOST],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_bch_loop_uart",
        testcase=testcase,
        parameters=parameters or {},
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, compile_args=compile_args,
        keep_files=True, timescale="1ns/1ps")


def test_bch_loop_uart_smoke(request):
    _run("cocotb_test_uart_smoke")


def test_bch_loop_uart_windows(request):
    _run("cocotb_test_uart_windows")


def test_bch_loop_uart_sequences(request):
    _run("cocotb_test_uart_sequences")


def test_bch_loop_uart_bypass(request):
    _run("cocotb_test_uart_bypass")


def test_bch_loop_uart_clean(request):
    _run("cocotb_test_uart_clean")


def test_bch_loop_uart_correct(request):
    _run("cocotb_test_uart_correct")


def test_bch_loop_uart_over_t(request):
    _run("cocotb_test_uart_over_t")


def test_bch_loop_uart_throttle(request):
    _run("cocotb_test_uart_throttle")


def test_bch_loop_uart_random(request):
    _run("cocotb_test_uart_random")


def test_bch_loop_uart_axi4(request):
    _run("cocotb_test_uart_axi4", parameters={"IFACE": '"AXI4"'}, suffix="_axi4")


def test_bch_loop_uart_observers(request):
    _run("cocotb_test_uart_observers")


def test_bch_loop_uart_axi4_observers(request):
    _run("cocotb_test_uart_axi4_observers", parameters={"IFACE": '"AXI4"'}, suffix="_axi4obs")


def test_bch_loop_uart_bw_slope(request):
    _run("cocotb_test_uart_bw_slope")


def test_bch_loop_uart_axi4_bw_slope(request):
    _run("cocotb_test_uart_axi4_bw_slope", parameters={"IFACE": '"AXI4"'}, suffix="_axi4slope")
