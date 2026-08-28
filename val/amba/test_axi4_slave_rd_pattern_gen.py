# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit-test runner for `axi4_slave_rd_pattern_gen`.

This block IS an AXI4 slave (LFSR pattern source + per-channel CRC-32
accumulator over AR/R). The TB drives it with the RDS-DV framework's
AXI4MasterRead BFM -- never a hand-rolled AR/R poke.

Pins:
  - a single-beat read returns the LFSR seed word (replicated across the
    data bus) and marks crc_valid/beat_count for its channel
  - sequential single-beat reads on one channel continue the SAME LFSR
    sequence beat-by-beat (burst boundaries don't reset/skip it)
  - a multi-beat burst returns consecutive LFSR advances
  - per-channel CRC-32 telemetry matches an independent software CRC-32
    reference (REFIN=1/REFOUT=1 standard CRC-32; see the TB docstring for
    the byte-order verification)
  - NUM_CHANNELS>1: each channel's LFSR/CRC state is independent -- only
    the served channel's stream advances

REG_LEVEL (env, default FUNC) selects how many (test_type, test_level)
combinations run; TEST_LEVEL (gate/func/full) scales how much work each
combination does (burst sizes / repeat counts). See
vault/handbook/dv/test-runner.md.
"""

import os
import random
import pytest

import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.axi4.axi4_slave_rd_pattern_gen_tb import SlaveRdPatternGenTB


# ---------------------------------------------------------------------------
# Depth knobs -- TEST_LEVEL scales how much work each scenario does.
# ---------------------------------------------------------------------------

_DEPTH = {
    "gate": {"seq_n": 4,  "burst": 4,  "crc_len": 4,  "ch0a": 2, "ch1": 2, "ch0b": 2},
    "func": {"seq_n": 8,  "burst": 8,  "crc_len": 16, "ch0a": 4, "ch1": 3, "ch0b": 4},
    "full": {"seq_n": 16, "burst": 32, "crc_len": 64, "ch0a": 8, "ch1": 6, "ch0b": 8},
}


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_axi4_slave_rd_pattern_gen(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    test_level = os.environ.get("TEST_LEVEL", "gate").lower()
    if test_level not in _DEPTH:
        test_level = "gate"
    depth = _DEPTH[test_level]

    tb = SlaveRdPatternGenTB(dut)
    await tb.setup_clocks_and_reset()

    scenarios = {
        "smoke": _smoke,
        "sequential": _sequential,
        "multi_beat_burst": _multi_beat_burst,
        "crc_telemetry": _crc_telemetry,
        "two_channel_interleave": _two_channel_interleave,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb, depth)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------


async def _smoke(tb: SlaveRdPatternGenTB, depth: dict):
    """Single-beat read on channel 0 returns the LFSR seed word."""
    data = await tb.read_burst(addr=0x100, burst_len=1, axi_id=0)
    expected = tb.expected_data_words(1, channel=0)
    assert data == expected, f"beat0: got {[hex(d) for d in data]} want {[hex(e) for e in expected]}"
    await tb.settle()
    assert tb.crc_valid(0) == 1
    assert tb.beat_count(0) == 1
    assert tb.beat_count_total() == 1


async def _sequential(tb: SlaveRdPatternGenTB, depth: dict):
    """N single-beat reads on channel 0 continue ONE LFSR sequence --
    burst boundaries must not reset or skip beats."""
    n = depth["seq_n"]
    got = []
    for i in range(n):
        beat = await tb.read_burst(addr=0x1000 + i * 0x10, burst_len=1, axi_id=0)
        got.extend(beat)
    expected = tb.expected_data_words(n, channel=0)
    assert got == expected, (
        f"sequential mismatch: got {[hex(d) for d in got]} "
        f"want {[hex(e) for e in expected]}"
    )
    await tb.settle()
    assert tb.beat_count(0) == n
    assert tb.crc_value(0) == tb.expected_crc32(n, channel=0)


async def _multi_beat_burst(tb: SlaveRdPatternGenTB, depth: dict):
    """One AR burst of N beats returns N consecutive LFSR advances."""
    n = depth["burst"]
    got = await tb.read_burst(addr=0x2000, burst_len=n, axi_id=0)
    expected = tb.expected_data_words(n, channel=0)
    assert got == expected
    await tb.settle()
    assert tb.beat_count(0) == n
    assert tb.beat_count_total() == n


async def _crc_telemetry(tb: SlaveRdPatternGenTB, depth: dict):
    """Per-channel CRC-32 + beat-count telemetry match the software
    reference after reading N beats."""
    n = depth["crc_len"]
    got = await tb.read_burst(addr=0x3000, burst_len=n, axi_id=0)
    expected = tb.expected_data_words(n, channel=0)
    assert got == expected
    await tb.settle()
    assert tb.crc_valid(0) == 1
    assert tb.beat_count(0) == n
    assert tb.beat_count_total() == n
    want_crc = tb.expected_crc32(n, channel=0)
    got_crc = tb.crc_value(0)
    assert got_crc == want_crc, (
        f"CRC mismatch: got 0x{got_crc:08X} want 0x{want_crc:08X} over {n} beats"
    )


async def _two_channel_interleave(tb: SlaveRdPatternGenTB, depth: dict):
    """NUM_CHANNELS=2 build: interleave bursts across channel 0 and
    channel 1. Each channel's LFSR/CRC stream must be independent of the
    other's traffic -- ch0's second burst continues where its first
    burst left off, ch1's seed is LFSR_SEED ^ 1."""
    assert tb.NUM_CHANNELS == 2, "this scenario requires a NUM_CHANNELS=2 build"

    n0a, n1, n0b = depth["ch0a"], depth["ch1"], depth["ch0b"]

    got0a = await tb.read_burst(addr=0x4000, burst_len=n0a, axi_id=0)
    got1 = await tb.read_burst(addr=0x5000, burst_len=n1, axi_id=1)
    got0b = await tb.read_burst(addr=0x4100, burst_len=n0b, axi_id=0)
    await tb.settle()

    exp0 = tb.expected_data_words(n0a + n0b, channel=0)
    exp1 = tb.expected_data_words(n1, channel=1)

    assert got0a == exp0[:n0a], "ch0 first burst diverged from ch0's LFSR seed"
    assert got0b == exp0[n0a:], (
        "ch0 second burst did not continue ch0's LFSR sequence -- "
        "ch1 traffic must not perturb ch0's state"
    )
    assert got1 == exp1, "ch1 diverged from its own seed (LFSR_SEED ^ 1)"

    assert tb.beat_count(0) == n0a + n0b
    assert tb.beat_count(1) == n1
    assert tb.beat_count_total() == n0a + n0b + n1

    assert tb.crc_value(0) == tb.expected_crc32(n0a + n0b, channel=0)
    assert tb.crc_value(1) == tb.expected_crc32(n1, channel=1)


# ---------------------------------------------------------------------------
# REG_LEVEL grid -- selects (test_type, test_level) combinations.
# ---------------------------------------------------------------------------

_CORE_TYPES = ["smoke", "multi_beat_burst", "crc_telemetry"]
_FUNC_TYPES = _CORE_TYPES + ["sequential", "two_channel_interleave"]
_ALL_TYPES = _FUNC_TYPES

_REG_LEVEL = os.environ.get("REG_LEVEL", "FUNC").upper()

if _REG_LEVEL == "GATE":
    _COMBOS = [(t, "gate") for t in _CORE_TYPES]
elif _REG_LEVEL == "FULL":
    _COMBOS = [(t, lvl) for t in _ALL_TYPES for lvl in ("gate", "func", "full")]
else:  # FUNC (default)
    _COMBOS = [(t, "func") for t in _FUNC_TYPES]

_NUM_CHANNELS_FOR = {"two_channel_interleave": 2}


@pytest.mark.parametrize("test_type, test_level", _COMBOS)
def test_axi4_slave_rd_pattern_gen(request, test_type, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "axi4_slave_rd_pattern_gen"
    test_name = f"test_axi4_slave_rd_pattern_gen_{test_type}_{test_level}_{_REG_LEVEL.lower()}"

    filelist_path = "rtl/amba/filelists/axi4_slave_rd_pattern_gen.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    num_channels = _NUM_CHANNELS_FOR.get(test_type, 1)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "TEST_LEVEL": test_level,
        "REG_LEVEL": _REG_LEVEL,
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH": "8",
        "NUM_CHANNELS": str(num_channels),
        "SEED": os.environ.get("SEED", str(random.randint(0, 100000))),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "AXI_DATA_WIDTH": "64",
        "AXI_ID_WIDTH": "8",
        "AXI_ADDR_WIDTH": "32",
        "AXI_USER_WIDTH": "1",
        "NUM_CHANNELS": str(num_channels),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET", "-Wno-WIDTHTRUNC"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_axi4_slave_rd_pattern_gen",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
