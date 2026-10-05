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
  uart_skew      e = t with ONLY checker A throttled, so the two decoder
                 outputs drain at different rates. This is the case that
                 caught a missing comparator backpressure term: with both
                 sides throttled equally the comparator FIFOs stayed in
                 lockstep and the bug was invisible in every other test.
  uart_axi4      the IFACE = "AXI4" build: the codecs become job engines over
                 four memories and the stages run in sequence, with the SAME
                 generator in and checker out. Clean, correctable and
                 beyond-threshold runs, plus the chain's own stage dones.
  uart_observers the axis4 interface observer on the four AXIS seams: caps,
                 exact beat/byte/packet counts, cleared per run, and agreement
                 with the old in-regblock meters on the shared seam
  uart_axi4_observers
                 the IFACE = "AXI4" build's master observer on the codec's own
                 ports: exact R/W beat counts per port, and the latency
                 histogram's bins summing to the transaction total
  uart_bw_slope  the board's `bw --slope` on a single-solver AXIS build at
                 16 -> 64 blocks: the codeword seams at exactly 100% -- the
                 control for the AXI4 figure
  uart_axi4_bw_slope
                 the AXI4 board run's slope, block counts and all: the
                 codeword seams must land on the board's own windows (97%,
                 not 100% -- the sdpram slave's documented per-burst boundary
                 cost, in the same RTL the board runs)
  uart_single    the ENABLE_COMPARE = 0 build: one Euclid decoder, no
                 comparator. Proves the run still finishes with checker B
                 tied off, and that the comparator reports inactive rather
                 than falsely clean.
  uart_sequences the bin/seq_*.py sequences, unmodified, through the same
                 SequenceRunner the board's run_smoke.py drives
  uart_random    the random campaign, on ITS OWN board defaults: 64 runs, each
                 a fresh data seed, error seed, injection mode, error count and
                 per-checker throttle. This is the test that has teeth -- every
                 other test here pins one pattern, and two harness bugs
                 (dropped and duplicated beats under a skewed drain) survived
                 the entire bring-up because of it.

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
_AREA = os.path.join(_REPO, "projects/fpga-systems/Genesys2/reed-solomon")
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
    """The fabric's three windows are reachable, isolated, and answer as built.

    Every window must COMPLETE rather than hang, and none may fold back into
    another. If the host address is truncated anywhere between the UART
    bridge and the fabric, every window folds back into the low one and these
    reads return the loop block's BUILD_ID instead -- which is exactly what a
    board probe found after the fabric first went in.

    What a window answers WITH moved on 2026-10-01: the two expansion windows
    now carry obs_regs interface observers. The base read alone cannot tell a
    live observer from a stub -- offset 0 is AXI_PKT_MASK, which defaults to 0
    either way -- so the caps read carries the verdict. On this AXIS build the
    obs window's axis4 observer is live (bus_meter, 4 ports) and the rs_regs
    window is the read-0 stub, which is ALSO the cross-window isolation check:
    the two expansion windows folding together would make their caps agree.
    """
    drv, _ = await _bringup(dut)
    windows = _fabric_windows()
    # the loop window is read again at the end: it must still answer after the
    # others have been poked
    plan = windows + [windows[0]]
    reads = await cocotb.external(lambda: [(n, a, drv.bridge.read(a)) for n, a in plan])()
    for name, addr, val in reads:
        dut._log.info("window %-24s @0x%05X -> 0x%08X", name, addr, val)
    assert reads[0][2] == rl.EXPECTED_BUILD_ID, (
        f"the loop window ({reads[0][0]}) read 0x{reads[0][2]:08X}")
    for name, addr, val in reads[1:-1]:
        assert val != rl.EXPECTED_BUILD_ID, (
            f"window {name} @0x{addr:05X} read back BUILD_ID -- "
            "the host address is being truncated before the fabric")
    assert reads[-1][2] == rl.EXPECTED_BUILD_ID, "the loop window stopped answering after the others"

    caps = await cocotb.external(drv.observer_caps)()
    dut._log.info("observer caps: %s", caps)
    assert caps["axis"]["bus_meter"] and caps["axis"]["rd_ports"] == 4, (
        f"the obs window should carry the live axis4 observer, got {caps['axis']}")
    assert caps["axi4"]["rd_ports"] == 0 and caps["axi4"]["caps0"] == 0, (
        f"the rs_regs window should be the read-0 stub on an AXIS build, got {caps['axi4']}")


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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_skew(dut):
    """Asymmetric drain: only checker A is throttled.

    The two decoders then produce at the same rate but are consumed at
    different rates. If the comparator's FIFO write is not part of the
    decoder's drain condition, the faster side overruns its 64-deep FIFO,
    beats are dropped, and the comparator starts pairing beat N of one
    decoder with beat N+k of the other -- reporting almost every beat as a
    riBM-vs-Euclid mismatch when the two agree completely.
    """
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=T, blocks=4,
                                                throttle_a=True, throttle_b=False))()
    assert not r.cmp_misaligned, "comparator streams misaligned: a beat was dropped"
    _report(dut, f"e={T} skewed drain", r)


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


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_uart_erasure(dut):
    """The erasure SEQUENCE, unmodified, against the sim (TASK-002).

    INJ_CFG.mark turns the injector's hit mask into the decoders' in_erasure
    sideband: f = t and f = 2t must correct every block with exactly f
    symbols, and f = 2t+1 must be refused by inspection on EVERY block --
    the one place the deterministic refusal can be asserted, because an
    erasure run has no miscorrection case. Same SequenceRunner, same
    programs, same verdict the board uses; `bin/run_smoke.py --sequences
    init erasure` runs exactly this on the hardware.
    """
    drv, _ = await _bringup(dut)

    def prog():
        from sequence import SequenceContext, SequenceRunner

        ctx = SequenceContext(bus=drv, board=None, params={}, log=dut._log.info)
        runner = SequenceRunner(ctx=ctx).discover(_SEQ)
        return runner.run(["init", "erasure"])

    report = await cocotb.external(prog)()
    dut._log.info("erasure run:\n%s", report.summary())
    _check_sim_budget(dut, "erasure (init -> erasure, board defaults)")
    assert report.ok, f"the erasure sequence failed in sim:\n{report.summary()}"


@cocotb.test(timeout_time=900, timeout_unit="ms")
async def cocotb_test_uart_random(dut):
    """The random campaign, unmodified, on its own defaults.

    64 runs x 4 blocks, each with a fresh data seed, error seed, mode, error
    count and independently drawn per-checker throttles. No deviation: these
    are the same defaults `host_rs_loop.py random` uses on the board.

    The campaign is the reason the other tests are not enough. Each of them
    fixes GEN_SEED and INJ_SEED, so they exercise one data pattern with the
    error in one place, many times over. Randomizing the two throttles
    independently is what broke the comparator open.
    """
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


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_single(dut):
    """The ENABLE_COMPARE = 0 build: ONE decoder, no comparator.

    A parameter's off state needs its own test, or the only thing that ever
    elaborates it is a lint pass. Two things have to hold here that the
    two-decoder build cannot check:

      - the run still FINISHES. chk_b_done is a packet compare in the default
        build, and with checker B tied off it would sit at zero forever and
        hold w_all_done low. It reads a constant 1 when there is no B.
      - the comparator reports INACTIVE, not clean. Zero mismatches over zero
        beats must not be mistaken for agreement, so CMP_BEATS is required to
        be 0 rather than merely non-contradictory.

    The decoder built here is Euclid, which is the one the default build puts
    in the B slot -- so this cell is also the only place Euclid is exercised
    as the primary decoder with its own checker and CRC.
    """
    drv, _ = await _bringup(dut)
    r = await cocotb.external(lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=T, blocks=4))()
    assert not r.timed_out, "the single-decoder run never finished"
    assert r.a.blk_corr == r.blocks, (
        f"single decoder: corrected {r.a.blk_corr}/{r.blocks}")
    assert r.a.sym_corr == T * r.blocks, (
        f"single decoder: {r.a.sym_corr} symbols corrected, want {T * r.blocks}")
    assert not r.a.data_err and r.a.crc_ok, (
        f"single decoder: data_err={r.a.data_err} crc_ok={r.a.crc_ok}")
    assert r.cmp_beats == 0 and not r.cmp_err and not r.cmp_misaligned, (
        f"comparator should be INACTIVE with one decoder, got beats={r.cmp_beats} "
        f"err={r.cmp_err} misaligned={r.cmp_misaligned}")
    _report(dut, f"single Euclid decoder, e={T}", r)


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_axi4(dut):
    """The AXI4 datapath: a memory-to-memory job chain in place of the stream.

    The generator and the checker are the same blocks, so this reaches the
    verdict through the same CSRs and the same data_err evidence. What is new
    is that the middle is five sequential jobs over four memories rather than
    one flowing pipe, and the chain has to actually run to completion -- which
    the host checks through STATUS.axi4_stage rather than inferring from a
    timeout.

    Three regimes, the same three the stream path is held to: no errors means
    every block clean, e = t means every block corrected with exactly t
    symbols, and e > t means the errors reached the checker. The host reads
    TOPOLOGY to learn it is talking to an AXI4 build, so the programs and the
    verdict are unmodified.
    """
    drv, _ = await _bringup(dut)
    topo = await cocotb.external(drv.topology)()
    assert topo["iface"] == "AXI4", f"expected an AXI4 build, TOPOLOGY says {topo['iface']}"
    assert topo["decoders"] == 1, f"the AXI4 chain carries one decoder, got {topo['decoders']}"

    for label, mode, count in (("clean", rl.RsLoopDriver.INJ_COUNT, 0),
                               (f"e={T}", rl.RsLoopDriver.INJ_COUNT, T),
                               (f"e={T + 1}", rl.RsLoopDriver.INJ_COUNT, T + 1)):
        r = await cocotb.external(lambda m=mode, c=count: progs.run(drv, m, count=c, blocks=3))()
        # progs.AXI4_STAGE_MASK, not a literal: the chain lost its inject stage
        # when the injector moved onto the decoder's read channel, and a second
        # copy of the expected value is how that change got caught here by a
        # 42-minute cosim instead of by the host check it already fixed.
        assert (r.axi4_stage & progs.AXI4_STAGE_MASK) == progs.AXI4_STAGE_MASK, (
            f"AXI4 {label}: chain stopped at stage 0x{r.axi4_stage:02X}, "
            f"wanted 0x{progs.AXI4_STAGE_MASK:02X}")
        assert not r.axi4_overflow, f"AXI4 {label}: run refused as oversized"
        _report(dut, f"AXI4 {label}", r)

    # The memories cap how many blocks one kick can carry, and past that the
    # regions would wrap and the decode would read the wrong words. That is a
    # silently wrong answer, so the harness refuses the run instead. A guard
    # whose refusing path is never exercised is a guard nobody has tested.
    over = rl.RsLoopDriver.INJ_COUNT
    r = await cocotb.external(lambda: progs.run(drv, over, count=0, blocks=4096))()
    assert r.axi4_overflow, (
        "an oversized AXI4 run should set STATUS.axi4_overflow and never kick")
    assert r.axi4_stage == 0x00, (
        f"a refused run must not start any stage, got 0x{r.axi4_stage:02X}")
    bad = progs.verdict(r, T)
    assert any("refused" in b for b in bad), (
        f"the verdict should name the refusal; it said {bad}")
    dut._log.info("AXI4 oversized run correctly refused: stage=0x%02X", r.axi4_stage)


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_observers(dut):
    """The interface observer on the four AXIS seams, read by name over the
    fabric's obs window.

    Four things have to hold before a board BW curve can trust this readout:

      - the window ANSWERS and says what it built: bus meter, no mon taps,
        four ports (OBS_CAPS*, not an assumption). The rs_regs window on this
        AXIS build is the stub and must report zero ports.
      - the counts are EXACT. A clean 3-block run moves 3*ceil(k/S) message
        beats and 3*ceil(n/S) codeword beats, and a meter's productive bucket
        is precisely its beat count -- no approximation, no sampling.
      - the meters CLEAR with the run: a second identical run reads the same
        numbers, not double. The first cut left i_meter_clear/i_meter_freeze
        dangling, which is exactly the failure this catches -- free-running
        counters accumulate across runs and every curve is garbage.
      - the OLD in-regblock meters and the observer agree on the seam they
        share, so the new readout is not a second opinion.
    """
    drv, _ = await _bringup(dut)
    prof = await cocotb.external(drv.profile)()
    s = prof["spb"]
    k_beats = -(-(prof["n"] - 2 * prof["t"]) // s)
    cw_beats = -(-prof["n"] // s)
    blocks = 3

    caps = await cocotb.external(drv.observer_caps)()
    dut._log.info("observer caps: %s", caps)
    assert caps["axis"]["bus_meter"] and not caps["axis"]["mon_taps"], caps["axis"]
    assert caps["axis"]["rd_ports"] == 4, caps["axis"]
    assert caps["axi4"]["rd_ports"] == 0, (
        f"the AXI4 window on an AXIS build should be the stub, got {caps['axi4']}")

    r = await cocotb.external(
        lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=0, blocks=blocks,
                          iface_obs=True))()
    _report(dut, "observers: clean", r)
    obs = r.iface_obs["axis"]
    want = {"msg_in": blocks * k_beats, "cw_out": blocks * cw_beats,
            "cw_in": blocks * cw_beats, "msg_out": blocks * k_beats}
    for seam, beats in want.items():
        d = obs[seam]
        dut._log.info("  %-7s %d beats, %d packets, %d bytes, util %.1f%% "
                      "(bp %d, starv %d, idle %d)",
                      seam, d["beats"], d["packets"], d["bytes"],
                      100.0 * d["utilisation"], d["backpressure"],
                      d["starvation"], d["idle"])
        assert d["beats"] == beats, f"{seam}: {d['beats']} beats, want {beats}"
        assert d["productive"] == beats, (
            f"{seam}: productive {d['productive']} != beats {d['beats']}")
        assert d["packets"] == blocks, f"{seam}: {d['packets']} packets, want {blocks}"
        assert d["bytes"] == beats * s, (
            f"{seam}: {d['bytes']} bytes, want {beats * s} -- a partial beat showed up "
            "at a profile that has none")
        assert d["window"] > 0, f"{seam}: empty bucket window"
    # the shared seam: old meter and new observer count the same beats
    assert r.obs["cw_out"]["productive"] == obs["cw_out"]["productive"], (
        f"old meter {r.obs['cw_out']['productive']} != observer "
        f"{obs['cw_out']['productive']} on the codeword-out seam")

    # clear-with-the-run: an identical second run reads the same, not double
    obs2 = (await cocotb.external(
        lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=0, blocks=blocks,
                          iface_obs=True))()).iface_obs["axis"]
    for seam in want:
        assert obs2[seam]["beats"] == want[seam], (
            f"{seam}: second run read {obs2[seam]['beats']} beats -- the meters are "
            "accumulating across runs (i_meter_clear is not clearing)")
    _check_sim_budget(dut, "observers")


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_uart_axi4_observers(dut):
    """The AXI4 flavour's master observer on the codec's own four ports.

    RD meters snoop the R handshake and WR meters the W handshake, so the
    productive bucket IS the beat count: enc_rd and dec_wr move the messages
    (3*ceil(k/S)), dec_rd and enc_wr the codewords (3*ceil(n/S)). The latency
    histogram must account for every transaction it timed: the bin counts sum
    to HIST_TOTAL. And the AXIS observer -- always built, seams tied off on
    this flavour -- must read all zeros rather than hang or count noise.
    """
    drv, _ = await _bringup(dut)
    topo = await cocotb.external(drv.topology)()
    assert topo["iface"] == "AXI4", f"expected an AXI4 build, TOPOLOGY says {topo['iface']}"
    prof = await cocotb.external(drv.profile)()
    s = prof["spb"]
    k_beats = -(-(prof["n"] - 2 * prof["t"]) // s)
    cw_beats = -(-prof["n"] // s)
    blocks = 3

    caps = await cocotb.external(drv.observer_caps)()
    dut._log.info("observer caps: %s", caps)
    assert caps["axi4"]["bus_meter"] and not caps["axi4"]["mon_taps"], caps["axi4"]
    assert (caps["axi4"]["rd_ports"], caps["axi4"]["wr_ports"]) == (2, 2), caps["axi4"]

    r = await cocotb.external(
        lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=0, blocks=blocks,
                          iface_obs=True))()
    _report(dut, "AXI4 observers: clean", r)
    obs = r.iface_obs["axi4"]
    want = {"enc_rd": blocks * k_beats, "dec_rd": blocks * cw_beats,
            "enc_wr": blocks * cw_beats, "dec_wr": blocks * k_beats}
    for port, beats in want.items():
        d = obs[port]
        dut._log.info("  %-7s productive %d (bp %d, starv %d, idle %d), %d timed xacts",
                      port, d["productive"], d["backpressure"], d["starvation"],
                      d["idle"], d["hist_total"])
        assert d["productive"] == beats, (
            f"{port}: productive {d['productive']}, want {beats}")
        assert d["hist_total"] > 0, f"{port}: no transactions timed"

    # the histogram is exact accounting: bins sum to the transaction total
    hist = await cocotb.external(lambda: drv.axi4_observer(hist=True))()
    for hm, label in ((0, "AR->first-R"), (1, "AR->RLAST")):
        total = hist["enc_rd"]["hist_total"]
        binned = sum(hist["enc_rd"]["hist"][hm])
        dut._log.info("  enc_rd %s: bins sum %d over %d timed", label, binned, total)
        assert binned == total, (
            f"enc_rd {label}: bins sum {binned} != hist_total {total}")

    # The AXIS observer is built on this flavour too, and its OUTER seams are
    # live: the generator still streams in (port 0) and the pipeline's drain
    # still streams out (port 3), while the codec seams (ports 1, 2) are tied.
    # That is a cross-check, not dead hardware: the two observers watched the
    # same messages, so their counts must agree.
    axis = await cocotb.external(drv.axis_observer)()
    for seam, d in axis.items():
        dut._log.info("  axis %-7s %d beats on this flavour", seam, d["beats"])
    assert axis["msg_in"]["beats"] == blocks * k_beats, axis["msg_in"]
    assert axis["msg_out"]["beats"] == blocks * k_beats, axis["msg_out"]
    assert axis["msg_in"]["beats"] == obs["enc_rd"]["productive"], (
        f"axis msg_in {axis['msg_in']['beats']} != axi4 enc_rd "
        f"{obs['enc_rd']['productive']} -- the two observers disagree on the same stream")
    assert axis["msg_out"]["beats"] == obs["dec_wr"]["productive"], (
        f"axis msg_out {axis['msg_out']['beats']} != axi4 dec_wr "
        f"{obs['dec_wr']['productive']} -- the two observers disagree on the same stream")
    assert axis["cw_out"]["beats"] == 0 and axis["cw_in"]["beats"] == 0, (
        "the codec seams should be tied in the AXI4 flavour, got "
        f"cw_out={axis['cw_out']['beats']} cw_in={axis['cw_in']['beats']}")
    _check_sim_budget(dut, "AXI4 observers")


def _slope_stats(small, large, key):
    """Differenced meter counts for one seam: beats, window, utilisation,
    cycles per block. The difference cancels the pipeline fill exactly."""
    a, b = small.obs[key], large.obs[key]
    d_prod = b["productive"] - a["productive"]
    d_win = b["window"] - a["window"]
    d_blocks = large.blocks - small.blocks
    return d_prod, d_win, d_prod / d_win, d_win / d_blocks


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_bw_slope(dut):
    """The board's `bw --slope` on the single-solver AXIS image, smaller counts.

    Board axis_ribm reads both codeword seams at 100.0% as a slope over
    64 -> 256 blocks. The sim uses 16 -> 64: the fill is one fixed term, so
    any two block counts cancel it, and a block's cost here is the register
    traffic, not its 63 beats. ENABLE_COMPARE=0 matches the board images
    one-for-one (one riBM decoder, no comparator -- the comparator changes
    the very handshake the meters measure).
    """
    drv, _ = await _bringup(dut)
    prof = await cocotb.external(drv.profile)()
    n, k, s = prof["n"], prof["n"] - 2 * prof["t"], prof["spb"]
    small = await cocotb.external(
        lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=0, blocks=16))()
    large = await cocotb.external(
        lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=0, blocks=64))()
    dut._log.info("AXIS slope 16 -> 64 blocks:\n" +
                  progs.bandwidth_slope(small, large, n, k, s))
    cw_beats = -(-n // s)
    for key in ("cw_out", "cw_in"):
        d_prod, d_win, util, per_blk = _slope_stats(small, large, key)
        assert d_prod == d_win == 48 * cw_beats, (
            f"{key}: {d_prod} beats in {d_win} cycles over 48 blocks -- "
            f"line rate is {48 * cw_beats} of each")
    _check_sim_budget(dut, "AXIS slope")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_uart_axi4_bw_slope(dut):
    """The AXI4 board run, block counts and all (16 -> 64, the per-kick cap).

    After the sdpram_core burst-queue fix (2026-10-02, amba ISSUE-004 fixed
    after all) the AXI4 codeword seams read 100.0% at slope -- exactly like
    AXIS. The ~97%/98.5% this test used to assert (cw_out 3118, cw_in 3069,
    2026-10-01 board figures) was the old slave's per-burst boundary cost,
    paid once per 64-beat burst and surviving the slope difference because
    the burst count scales with the block count. With the boundary free, the
    codeword window IS the line rate: 48 blocks x 63 beats = 3024 cycles for
    both seams. The message channel stays codec-throughput-bound (2832 beats
    in 11712 cycles, 24.2%) -- the decoder's own pace, not the memory's; it
    was 11983 before the fix. Board re-measurement against the rebuilt images
    is pending; until then bandwidth.txt's 2026-10-01 figures describe the
    OLD slave and this test's numbers are the sim's.
    """
    drv, _ = await _bringup(dut)
    topo = await cocotb.external(drv.topology)()
    assert topo["iface"] == "AXI4", f"expected an AXI4 build, TOPOLOGY says {topo['iface']}"
    prof = await cocotb.external(drv.profile)()
    n, k, s = prof["n"], prof["n"] - 2 * prof["t"], prof["spb"]
    small = await cocotb.external(
        lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=0, blocks=16))()
    large = await cocotb.external(
        lambda: progs.run(drv, rl.RsLoopDriver.INJ_COUNT, count=0, blocks=64))()
    dut._log.info("AXI4 slope 16 -> 64 blocks:\n" +
                  progs.bandwidth_slope(small, large, n, k, s))
    cw_beats = -(-n // s)
    msg_beats = -(-k // s)
    for key, beats, win in (("cw_out", 48 * cw_beats, 3024),
                            ("cw_in", 48 * cw_beats, 3024),
                            ("in", 48 * msg_beats, 11712),
                            ("out", 48 * msg_beats, 11712)):
        d_prod, d_win, util, per_blk = _slope_stats(small, large, key)
        assert d_prod == beats, f"{key}: {d_prod} beats, want {beats}"
        assert d_win == win, (
            f"{key}: window {d_win} cycles, expected {win} -- "
            "sim and board diverge on the same RTL")
        if key.startswith("cw"):
            assert d_prod == d_win, (
                f"{key}: read {util:.1%} -- the codeword seam must be at "
                "line rate now that the slave boundary is free")
        else:
            assert d_prod < d_win, f"{key}: read {util:.1%} -- the message channel is codec-bound"
    _check_sim_budget(dut, "AXI4 slope")


# =============================================================================
# pytest wrappers
# =============================================================================
def _run(testcase: str, parameters=None, suffix=""):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "rs_loop_uart_tb_top"
    filelist_path = "projects/fpga-systems/Genesys2/reed-solomon/build-loop/dv/filelists/rs_loop_uart_tb_top.f"
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
        toplevel=dut_name, module="test_rs_loop_uart",
        testcase=testcase,
        parameters=parameters or {},
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


def test_rs_loop_uart_skew(request):
    _run("cocotb_test_uart_skew")


def test_rs_loop_uart_random(request):
    _run("cocotb_test_uart_random")


def test_rs_loop_uart_erasure(request):
    """Marked runs through the erasure sequence: f = t, 2t correct; 2t+1 refused."""
    _run("cocotb_test_uart_erasure")


def test_rs_loop_uart_single(request):
    """ENABLE_COMPARE=0 with Euclid as the only decoder."""
    _run("cocotb_test_uart_single",
         parameters={"ENABLE_COMPARE": "0", "KES_ALGO_A": '"EUCLID"'},
         suffix="_ec0")


def test_rs_loop_uart_axi4(request):
    """IFACE=AXI4: the memory-to-memory job chain, one decoder."""
    _run("cocotb_test_uart_axi4",
         parameters={"IFACE": '"AXI4"', "ENABLE_COMPARE": "0"},
         suffix="_axi4")


def test_rs_loop_uart_observers(request):
    """The axis4 interface observer: exact counts, cleared per run."""
    _run("cocotb_test_uart_observers")


def test_rs_loop_uart_axi4_observers(request):
    """IFACE=AXI4: the master observer's buckets and latency histogram."""
    _run("cocotb_test_uart_axi4_observers",
         parameters={"IFACE": '"AXI4"', "ENABLE_COMPARE": "0"},
         suffix="_axi4obs")


def test_rs_loop_uart_bw_slope(request):
    """The board's bw --slope on a single-solver AXIS build: 100% cw seams."""
    _run("cocotb_test_uart_bw_slope",
         parameters={"ENABLE_COMPARE": "0"},
         suffix="_slope")


def test_rs_loop_uart_axi4_bw_slope(request):
    """The AXI4 board run's slope: the slave's per-burst cost, sim == board."""
    _run("cocotb_test_uart_axi4_bw_slope",
         parameters={"IFACE": '"AXI4"', "ENABLE_COMPARE": "0"},
         suffix="_axi4slope")
