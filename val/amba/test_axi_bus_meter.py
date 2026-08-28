# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi_bus_meter
# Purpose: Unit test for axi_bus_meter (rtl/amba/shared/axi_bus_meter.sv)
#
# axi_bus_meter is a pure passive observer of bare i_valid/i_ready/
# i_channel_id/i_channel_valid taps (see rtl/amba/shared/axi_bus_meter.sv and
# docs/markdown/rtl-amba/shared/axi_bus_meter.md) -- there is no AXI channel
# to drive (no addr/id/burst framing to construct), so the BFM axis
# ([[bfm-usage]]) resolves to "directed per-cycle stimulus", matching the
# sibling test_axi_perf_latency_hist.py which snoops the same style of bare
# taps. Every scenario drives the DUT's inputs cycle-by-cycle while a
# software mirror (AxiBusMeterTB, in bin/TBClasses/amba/) tracks the exact
# same four-bucket classification + overflow-sticky rules as the RTL, then
# asserts bit-for-bit equality against the DUT's counters.
#
# Coverage:
#   - idle / back-to-back / backpressure / starvation: each bucket alone
#   - per-channel idle CAN be attributed for axi_bus_meter (unlike its AXIS
#     cousin) when i_channel_valid is held during idle cycles
#   - mixed random traffic, mirrored cycle-by-cycle
#   - channel boundary (id 0 and NUM_CHANNELS-1) stays correctly binned
#   - i_freeze holds every counter and sticky exactly; resumes cleanly after
#   - i_clear zeroes every counter and sticky synchronously
#   - 16-bit per-channel overflow wrap (FULL only, ~64K cycles -- the RTL has
#     no COUNTER_WIDTH parameter to narrow, so 16 bits is the cheapest
#     reachable wrap; the 32-bit aggregate wrap (~4.3B cycles) is not
#     cheaply reachable and is out of scope)

import os
import random

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.amba.axi_bus_meter_tb import AxiBusMeterTB


@cocotb.test(timeout_time=20, timeout_unit="sec")
async def cocotb_test_axi_bus_meter(dut):
    test_type = os.environ.get("TEST_TYPE", "back_to_back")
    tb = AxiBusMeterTB(dut, num_channels=int(os.environ.get("NUM_CHANNELS", "4")))
    await tb.setup_clocks_and_reset()
    scenarios = {
        "idle":            _idle,
        "back_to_back":    _back_to_back,
        "backpressure":    _backpressure,
        "starvation":      _starvation,
        "mixed_random":    _mixed_random,
        "channel_boundary": _channel_boundary,
        "freeze_holds":    _freeze_holds,
        "clear_resets":    _clear_resets,
        "overflow_wrap":   _overflow_wrap,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _idle(tb: AxiBusMeterTB):
    """Pure idle: valid=0, ready=0. Normal usage (i_channel_valid=0) only
    attributes to the aggregate idle bucket -- per the module doc, callers
    leave i_channel_valid low when no channel is on the hook."""
    N = 30
    for _ in range(N):
        await tb.drive_cycle(valid=0, ready=0, ch_valid=0)
    await tb.settle()
    tb.assert_agg_matches("idle/agg")
    assert tb.agg["idle"] == N
    tb.assert_all_ch_match("idle/ch (untouched)")

    # But axi_bus_meter (unlike axis_bus_meter) has no structural block on
    # per-channel idle: if the caller holds i_channel_valid high through an
    # idle cycle, the per-channel idle bucket for that channel DOES advance.
    # This is the documented distinction between the two meters' per-channel
    # idle behavior -- pin it explicitly so a future "make them identical"
    # refactor is caught.
    M = 10
    for _ in range(M):
        await tb.drive_cycle(valid=0, ready=0, ch_id=1, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("idle/agg (ch_valid held)")
    tb.assert_all_ch_match("idle/ch (ch_valid held)")
    assert tb.ch[1]["idle"] == M, "per-channel idle must accumulate when ch_valid is held"


async def _back_to_back(tb: AxiBusMeterTB):
    """valid=1, ready=1 every cycle: pure productive traffic on one channel."""
    N = 40
    CH = 2
    for _ in range(N):
        await tb.drive_cycle(valid=1, ready=1, ch_id=CH, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("b2b/agg")
    assert tb.agg["productive"] == N
    tb.assert_all_ch_match("b2b/ch")
    assert tb.ch[CH]["productive"] == N
    assert tb.read_ch_overflow(CH) == 0


async def _backpressure(tb: AxiBusMeterTB):
    """valid=1, ready=0: master offers, slave stalls."""
    N = 40
    CH = 0
    for _ in range(N):
        await tb.drive_cycle(valid=1, ready=0, ch_id=CH, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("bp/agg")
    assert tb.agg["backpressure"] == N
    tb.assert_all_ch_match("bp/ch")
    assert tb.ch[CH]["backpressure"] == N


async def _starvation(tb: AxiBusMeterTB):
    """valid=0, ready=1: slave ready, master not producing."""
    N = 40
    CH = 3
    for _ in range(N):
        await tb.drive_cycle(valid=0, ready=1, ch_id=CH, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("starv/agg")
    assert tb.agg["starvation"] == N
    tb.assert_all_ch_match("starv/ch")
    assert tb.ch[CH]["starvation"] == N


async def _mixed_random(tb: AxiBusMeterTB):
    """Random per-cycle valid/ready/channel_id/channel_valid. The mirror
    tracks every cycle; asserts full agg + per-channel + overflow match."""
    test_level = os.environ.get("TEST_LEVEL", "func").lower()
    N = {"gate": 200, "func": 800, "full": 3000}.get(test_level, 800)
    rng = random.Random(tb.SEED)
    for _ in range(N):
        valid = rng.randint(0, 1)
        ready = rng.randint(0, 1)
        ch_id = rng.randrange(tb.NUM_CHANNELS)
        ch_valid = rng.randint(0, 1)
        await tb.drive_cycle(valid=valid, ready=ready, ch_id=ch_id, ch_valid=ch_valid)
    await tb.settle()
    tb.assert_agg_matches("mixed/agg")
    tb.assert_all_ch_match("mixed/ch")
    assert sum(tb.agg.values()) == N


async def _channel_boundary(tb: AxiBusMeterTB):
    """Distinct traffic on channel 0 and channel NUM_CHANNELS-1, alternating,
    to catch an off-by-one in the channel index / array bound."""
    LAST = tb.NUM_CHANNELS - 1
    N = 25
    for i in range(N):
        await tb.drive_cycle(valid=1, ready=1, ch_id=0, ch_valid=1)
        await tb.drive_cycle(valid=1, ready=0, ch_id=LAST, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("boundary/agg")
    tb.assert_all_ch_match("boundary/ch")
    assert tb.ch[0]["productive"] == N
    assert tb.ch[LAST]["backpressure"] == N
    for mid in range(1, LAST):
        assert tb.ch[mid]["productive"] == 0
        assert tb.ch[mid]["backpressure"] == 0


async def _freeze_holds(tb: AxiBusMeterTB):
    """i_freeze must hold every counter + sticky exactly, then resume
    accumulating cleanly once released."""
    CH = 1
    for _ in range(15):
        await tb.drive_cycle(valid=1, ready=1, ch_id=CH, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("freeze/pre")
    pre_agg = dict(tb.agg)
    pre_ch = dict(tb.ch[CH])

    # Freeze, then drive a DIFFERENT mix -- none of it should count.
    for _ in range(20):
        await tb.drive_cycle(valid=random.randint(0, 1), ready=random.randint(0, 1),
                              ch_id=CH, ch_valid=1, freeze=1)
    await tb.settle()
    assert tb.agg == pre_agg, "mirror drifted during freeze (bug in test, not DUT)"
    tb.assert_agg_matches("freeze/during")
    tb.assert_ch_matches(CH, "freeze/during ch")
    assert tb.read_agg() == pre_agg, "counters moved while frozen"
    assert tb.read_ch(CH) == pre_ch, "per-channel counters moved while frozen"

    # Resume: traffic after freeze accumulates on top of the held values.
    for _ in range(10):
        await tb.drive_cycle(valid=1, ready=1, ch_id=CH, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("freeze/post")
    tb.assert_ch_matches(CH, "freeze/post ch")
    assert tb.agg["productive"] == pre_agg["productive"] + 10


async def _clear_resets(tb: AxiBusMeterTB):
    """i_clear zeroes every counter + sticky synchronously; traffic after
    clear restarts cleanly from zero."""
    CH = 2
    for _ in range(12):
        await tb.drive_cycle(valid=1, ready=1, ch_id=CH, ch_valid=1)
    await tb.settle()
    assert tb.agg["productive"] == 12
    tb.assert_agg_matches("clear/pre")

    await tb.clear_pulse()
    await tb.settle()
    tb.assert_agg_matches("clear/post")
    tb.assert_all_ch_match("clear/post ch")
    assert all(v == 0 for v in tb.agg.values())

    for _ in range(7):
        await tb.drive_cycle(valid=1, ready=0, ch_id=CH, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("clear/resume")
    assert tb.agg["backpressure"] == 7


OVERFLOW_BIT_PRODUCTIVE = 3  # matches AxiBusMeterTB.OVERFLOW_BIT['productive']


async def _overflow_wrap(tb: AxiBusMeterTB):
    """Drive one channel's productive counter through its 16-bit wrap.
    Confirms: (a) the per-channel counter wraps to the correct residual
    value, (b) the overflow sticky bit latches exactly (and only) for the
    bucket that wrapped, (c) the 32-bit aggregate counter is unaffected by
    the 16-bit per-channel wrap -- the two widths are independent."""
    CH = 0
    OVER = 4  # cycles past the 16-bit wrap boundary
    N = 0x10000 + OVER
    for _ in range(N):
        await tb.drive_cycle(valid=1, ready=1, ch_id=CH, ch_valid=1)
    await tb.settle()
    tb.assert_agg_matches("overflow/agg")
    assert tb.agg["productive"] == N, "32-bit aggregate must not be affected by the 16-bit wrap"
    tb.assert_ch_matches(CH, "overflow/ch")
    assert tb.ch[CH]["productive"] == (N & 0xFFFF) == OVER
    assert tb.read_ch_overflow(CH) == (1 << OVERFLOW_BIT_PRODUCTIVE)

    # i_clear must also drop the sticky.
    await tb.clear_pulse()
    await tb.settle()
    assert tb.read_ch_overflow(CH) == 0, "i_clear must drop the overflow sticky too"


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = ["idle", "back_to_back", "backpressure", "starvation",
              "mixed_random", "channel_boundary", "freeze_holds",
              "clear_resets", "overflow_wrap"]
_GATE = ["idle", "back_to_back", "backpressure", "starvation"]
_FUNC = _GATE + ["mixed_random", "channel_boundary", "freeze_holds", "clear_resets"]
_FULL = _FUNC + ["overflow_wrap"]

_REG_LEVEL = os.environ.get("REG_LEVEL", "FUNC").upper()
_SCENARIOS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_REG_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _SCENARIOS)
def test_axi_bus_meter(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi_bus_meter"
    test_name = f"test_axi_bus_meter_{test_type}"

    filelist_path = "rtl/amba/filelists/axi_bus_meter.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    num_channels = 4
    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "NUM_CHANNELS": str(num_channels),
        "SEED": os.environ.get('SEED', str(random.randint(0, 100000))),
        "TEST_LEVEL": os.environ.get("TEST_LEVEL", "func"),
        "LOG_PATH": os.path.join(log_dir, f"{test_name}.log"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
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
        testcase="cocotb_test_axi_bus_meter",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
