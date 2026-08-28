# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axis_bus_meter
# Purpose: Unit test for axis_bus_meter (rtl/amba/shared/axis_bus_meter.sv)
#
# axis_bus_meter is a pure passive observer of bare tvalid/tready/tlast/
# tstrb/tid taps (see rtl/amba/shared/axis_bus_meter.sv and
# docs/markdown/rtl-amba/shared/axis_bus_meter.md) -- same rationale as its
# axi_bus_meter cousin (test_axi_bus_meter.py): no framed AXIS transfer
# exists to hand an AXIS BFM, so directed per-cycle stimulus plus a software
# mirror (AxisBusMeterTB, in bin/TBClasses/amba/) is the right tool.
#
# Coverage:
#   - idle / back-to-back / backpressure / starvation: each bucket alone
#   - mixed random traffic (valid/ready/tid/tstrb/tlast), mirrored
#     cycle-by-cycle
#   - channel boundary (tid 0 and NUM_CHANNELS-1)
#   - byte/beat/packet throughput counters (tstrb popcount, tlast)
#   - design contract: per-channel idle is NEVER attributed (o_ch_idle stays
#     0 for every channel), unlike axi_bus_meter where it can be
#   - i_freeze holds every counter + sticky exactly; resumes cleanly after
#   - i_clear zeroes every counter + sticky synchronously
#   - 16-bit per-channel overflow wrap (FULL only, ~64K cycles -- same
#     rationale as the AXI meter's overflow test; the 64-bit byte counter
#     wrap is not cheaply reachable and out of scope)

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.axis_bus_meter_tb import AxisBusMeterTB

OVERFLOW_BIT_PRODUCTIVE = 3  # matches AxisBusMeterTB.OVERFLOW_BIT['productive']


@cocotb.test(timeout_time=20, timeout_unit="sec")
async def cocotb_test_axis_bus_meter(dut):
    test_type = os.environ.get("TEST_TYPE", "back_to_back")
    tb = AxisBusMeterTB(dut,
                         num_channels=int(os.environ.get("NUM_CHANNELS", "4")),
                         sw=int(os.environ.get("SW", "4")))
    await tb.setup_clocks_and_reset()
    scenarios = {
        "idle":              _idle,
        "back_to_back":      _back_to_back,
        "backpressure":      _backpressure,
        "starvation":        _starvation,
        "mixed_random":      _mixed_random,
        "channel_boundary":  _channel_boundary,
        "bytes_and_packets": _bytes_and_packets,
        "ch_idle_never_set": _ch_idle_never_set,
        "freeze_holds":      _freeze_holds,
        "clear_resets":      _clear_resets,
        "overflow_wrap":     _overflow_wrap,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _idle(tb: AxisBusMeterTB):
    N = 30
    for _ in range(N):
        await tb.drive_cycle(tvalid=0, tready=0, tid=2)
    await tb.settle()
    tb.assert_agg_matches("idle/agg")
    assert tb.agg["idle"] == N
    tb.assert_all_ch_match("idle/ch")
    # Structural: idle is never attributed per channel, so all o_ch_idle
    # stay 0 regardless of tid.
    for idx in range(tb.NUM_CHANNELS):
        assert tb.read_ch(idx)["idle"] == 0


async def _back_to_back(tb: AxisBusMeterTB):
    N = 40
    CH = 2
    for _ in range(N):
        await tb.drive_cycle(tvalid=1, tready=1, tid=CH)
    await tb.settle()
    tb.assert_agg_matches("b2b/agg")
    assert tb.agg["productive"] == N
    tb.assert_all_ch_match("b2b/ch")
    assert tb.ch[CH]["productive"] == N
    # Default tstrb (all-ones) => bytes == beats * SW.
    tb.assert_throughput_matches("b2b/throughput")
    assert tb.agg_bytes == N * tb.SW
    assert tb.read_ch_overflow(CH) == 0


async def _backpressure(tb: AxisBusMeterTB):
    N = 40
    CH = 0
    for _ in range(N):
        await tb.drive_cycle(tvalid=1, tready=0, tid=CH)
    await tb.settle()
    tb.assert_agg_matches("bp/agg")
    assert tb.agg["backpressure"] == N
    tb.assert_all_ch_match("bp/ch")
    assert tb.ch[CH]["backpressure"] == N
    tb.assert_throughput_matches("bp/throughput")
    assert tb.agg_bytes == 0, "backpressure cycles must not count bytes"


async def _starvation(tb: AxisBusMeterTB):
    N = 40
    CH = 3
    for _ in range(N):
        await tb.drive_cycle(tvalid=0, tready=1, tid=CH)
    await tb.settle()
    tb.assert_agg_matches("starv/agg")
    assert tb.agg["starvation"] == N
    tb.assert_all_ch_match("starv/ch")
    assert tb.ch[CH]["starvation"] == N
    tb.assert_throughput_matches("starv/throughput")
    assert tb.agg_bytes == 0


async def _mixed_random(tb: AxisBusMeterTB):
    """Random per-cycle tvalid/tready/tid/tstrb/tlast. The mirror tracks
    every cycle; asserts full agg + per-channel + overflow + throughput
    match."""
    test_level = os.environ.get("TEST_LEVEL", "func").lower()
    N = {"gate": 200, "func": 800, "full": 3000}.get(test_level, 800)
    rng = random.Random(tb.SEED)
    strb_mask = (1 << tb.SW) - 1
    for _ in range(N):
        tvalid = rng.randint(0, 1)
        tready = rng.randint(0, 1)
        tid = rng.randrange(tb.NUM_CHANNELS)
        tstrb = rng.randint(0, strb_mask)
        tlast = rng.randint(0, 1)
        await tb.drive_cycle(tvalid=tvalid, tready=tready, tid=tid,
                              tlast=tlast, tstrb=tstrb)
    await tb.settle()
    tb.assert_agg_matches("mixed/agg")
    tb.assert_all_ch_match("mixed/ch")
    tb.assert_throughput_matches("mixed/throughput")
    assert sum(tb.agg.values()) == N


async def _channel_boundary(tb: AxisBusMeterTB):
    LAST = tb.NUM_CHANNELS - 1
    N = 25
    for _ in range(N):
        await tb.drive_cycle(tvalid=1, tready=1, tid=0)
        await tb.drive_cycle(tvalid=1, tready=0, tid=LAST)
    await tb.settle()
    tb.assert_agg_matches("boundary/agg")
    tb.assert_all_ch_match("boundary/ch")
    assert tb.ch[0]["productive"] == N
    assert tb.ch[LAST]["backpressure"] == N
    for mid in range(1, LAST):
        assert tb.ch[mid]["productive"] == 0
        assert tb.ch[mid]["backpressure"] == 0


async def _bytes_and_packets(tb: AxisBusMeterTB):
    """Sparse tstrb + periodic tlast: pins byte-exact popcount accumulation
    and packet counting independent of the cycle-bucket counters."""
    strb_mask = (1 << tb.SW) - 1
    PACKET_LEN = 4
    N = 24
    rng = random.Random(tb.SEED ^ 0xB5)
    for i in range(N):
        tstrb = rng.randint(1, strb_mask)  # at least 1 lane, sparse mix
        tlast = 1 if ((i + 1) % PACKET_LEN == 0) else 0
        await tb.drive_cycle(tvalid=1, tready=1, tid=1, tlast=tlast, tstrb=tstrb)
    await tb.settle()
    tb.assert_agg_matches("bytesnpkts/agg")
    tb.assert_throughput_matches("bytesnpkts/throughput")
    assert tb.agg_beats == N
    assert tb.agg_packets == N // PACKET_LEN
    assert tb.agg_bytes > 0


async def _ch_idle_never_set(tb: AxisBusMeterTB):
    """Interleave idle cycles (various tid values -- meaningless while
    idle) with real traffic; o_ch_idle must stay 0 for every channel while
    o_agg_idle accumulates normally. This is the design contract documented
    in axis_bus_meter.md ("Per-Channel Idle Is Not Attributed")."""
    rng = random.Random(tb.SEED ^ 0x1D1E)
    idle_count = 0
    for _ in range(60):
        if rng.random() < 0.5:
            await tb.drive_cycle(tvalid=0, tready=0, tid=rng.randrange(tb.NUM_CHANNELS))
            idle_count += 1
        else:
            await tb.drive_cycle(tvalid=1, tready=1, tid=rng.randrange(tb.NUM_CHANNELS))
    await tb.settle()
    tb.assert_agg_matches("ch_idle/agg")
    assert tb.agg["idle"] == idle_count
    for idx in range(tb.NUM_CHANNELS):
        assert tb.read_ch(idx)["idle"] == 0, f"ch[{idx}].idle must stay 0"
    tb.assert_all_ch_match("ch_idle/ch")


async def _freeze_holds(tb: AxisBusMeterTB):
    CH = 1
    for _ in range(15):
        await tb.drive_cycle(tvalid=1, tready=1, tid=CH)
    await tb.settle()
    tb.assert_agg_matches("freeze/pre")
    tb.assert_throughput_matches("freeze/pre throughput")
    pre_agg = dict(tb.agg)
    pre_ch = dict(tb.ch[CH])
    pre_thr = tb.read_throughput()

    for _ in range(20):
        await tb.drive_cycle(tvalid=random.randint(0, 1), tready=random.randint(0, 1),
                              tid=CH, tlast=1, freeze=1)
    await tb.settle()
    assert tb.agg == pre_agg, "mirror drifted during freeze (bug in test, not DUT)"
    tb.assert_agg_matches("freeze/during")
    tb.assert_ch_matches(CH, "freeze/during ch")
    assert tb.read_agg() == pre_agg
    assert tb.read_ch(CH) == pre_ch
    assert tb.read_throughput() == pre_thr, "throughput counters moved while frozen"

    for _ in range(10):
        await tb.drive_cycle(tvalid=1, tready=1, tid=CH)
    await tb.settle()
    tb.assert_agg_matches("freeze/post")
    tb.assert_ch_matches(CH, "freeze/post ch")
    assert tb.agg["productive"] == pre_agg["productive"] + 10


async def _clear_resets(tb: AxisBusMeterTB):
    CH = 2
    for _ in range(12):
        await tb.drive_cycle(tvalid=1, tready=1, tid=CH)
    await tb.settle()
    assert tb.agg["productive"] == 12
    tb.assert_throughput_matches("clear/pre throughput")

    await tb.clear_pulse()
    await tb.settle()
    tb.assert_agg_matches("clear/post")
    tb.assert_all_ch_match("clear/post ch")
    tb.assert_throughput_matches("clear/post throughput")
    assert all(v == 0 for v in tb.agg.values())
    assert tb.agg_bytes == 0 and tb.agg_beats == 0 and tb.agg_packets == 0

    for _ in range(7):
        await tb.drive_cycle(tvalid=1, tready=0, tid=CH)
    await tb.settle()
    tb.assert_agg_matches("clear/resume")
    assert tb.agg["backpressure"] == 7


async def _overflow_wrap(tb: AxisBusMeterTB):
    """Drive one channel's productive counter through its 16-bit wrap.
    Confirms wrap value, sticky latch, and that the 32-bit aggregate +
    64-bit byte counters are unaffected by the 16-bit per-channel wrap."""
    CH = 0
    OVER = 4
    N = 0x10000 + OVER
    for _ in range(N):
        await tb.drive_cycle(tvalid=1, tready=1, tid=CH)
    await tb.settle()
    tb.assert_agg_matches("overflow/agg")
    assert tb.agg["productive"] == N
    tb.assert_ch_matches(CH, "overflow/ch")
    assert tb.ch[CH]["productive"] == (N & 0xFFFF) == OVER
    assert tb.read_ch_overflow(CH) == (1 << OVERFLOW_BIT_PRODUCTIVE)
    tb.assert_throughput_matches("overflow/throughput")
    assert tb.agg_bytes == N * tb.SW

    await tb.clear_pulse()
    await tb.settle()
    assert tb.read_ch_overflow(CH) == 0, "i_clear must drop the overflow sticky too"


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["idle", "back_to_back", "backpressure", "starvation",
              "mixed_random", "channel_boundary", "bytes_and_packets",
              "ch_idle_never_set", "freeze_holds", "clear_resets",
              "overflow_wrap"]
_GATE = ["idle", "back_to_back", "backpressure", "starvation"]
_FUNC = _GATE + ["mixed_random", "channel_boundary", "bytes_and_packets",
                  "ch_idle_never_set", "freeze_holds", "clear_resets"]
_FULL = _FUNC + ["overflow_wrap"]

_REG_LEVEL = os.environ.get("REG_LEVEL", "FUNC").upper()
_SCENARIOS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_REG_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _SCENARIOS)
def test_axis_bus_meter(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axis_bus_meter"
    test_name = f"test_axis_bus_meter_{test_type}"

    filelist_path = "rtl/amba/filelists/axis_bus_meter.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    num_channels = 4
    data_width = 32  # SW = 4 -- small tstrb width keeps popcount trivial
    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "NUM_CHANNELS": str(num_channels),
        "SW": str(data_width // 8),
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "func"),
        "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "DATA_WIDTH":   str(data_width),
        "NUM_CHANNELS": str(num_channels),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET", "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_axis_bus_meter",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
