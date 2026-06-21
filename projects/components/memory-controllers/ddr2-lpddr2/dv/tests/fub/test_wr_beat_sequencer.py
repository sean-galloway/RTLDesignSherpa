# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-19

"""
Unit-test runner for `wr_beat_sequencer`.

Scenarios (all scoreboarded via WrBeatSequencerTB.expected_dfi_cycles):
  smoke           single 4-beat burst with full strb, t_phy_wrlat=2
  burst_len_sweep lens {1, 2, 3, 4, 8, 16, 33, 64} — partial-tail packing
  tphy_sweep      t_phy_wrlat ∈ {0, 1, 2, 5, 10}
  partial_strb    alternating full/partial wstrb beats → DFI mask packing
  back_to_back    3 bursts issued sequentially, single in-flight slot
  random_soak     random bursts (length, strb pattern, t_phy_wrlat)
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.wr_beat_sequencer_tb import WrBeatSequencerTB  # noqa: E402


# ---------------------------------------------------------------------------
# CocoTB dispatch
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_wr_beat_sequencer(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    log = logging.getLogger("wr_beat_sequencer_test")
    log.info(f"TEST_TYPE={test_type}")

    tb = WrBeatSequencerTB(dut)
    await tb.setup_clocks_and_reset()

    scenarios = {
        "smoke":             _smoke,
        "burst_len_sweep":   _burst_len_sweep,
        "tphy_sweep":        _tphy_sweep,
        "partial_strb":      _partial_strb,
        "back_to_back":      _back_to_back,
        "multi_outstanding": _multi_outstanding,
        "random_soak":       _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    await tb.wait_clocks('mc_clk', 10)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------

async def _run_one_burst(tb: WrBeatSequencerTB, *, slot: int, length: int,
                         full_strb: bool, t_phy_wrlat: int,
                         seed_tag: int = 0):
    burst = tb.make_burst(slot=slot, length=length,
                          full_strb=full_strb,
                          t_phy_wrlat=t_phy_wrlat,
                          seed_tag=seed_tag)
    await tb.issue_op(burst)
    await tb.await_burst_complete(burst)
    tb.verify_capture(burst)
    return burst


async def _smoke(tb: WrBeatSequencerTB):
    await _run_one_burst(tb, slot=3, length=4, full_strb=True, t_phy_wrlat=2)


async def _burst_len_sweep(tb: WrBeatSequencerTB):
    # Include lens that exercise: minimum (1), tail-of-DFI-cycle packing
    # at rate-2 (3, 33), powers of two (4, 8, 16, 64).
    for length in [1, 2, 3, 4, 8, 16, 33, 64]:
        await _run_one_burst(tb, slot=(length & 0xF), length=length,
                             full_strb=True, t_phy_wrlat=2,
                             seed_tag=length)
        # Settle between bursts so b_complete / capture state clears
        await tb.wait_clocks('mc_clk', 4)


async def _tphy_sweep(tb: WrBeatSequencerTB):
    # Same burst, different PHY wait latencies.
    for t in [0, 1, 2, 5, 10]:
        await _run_one_burst(tb, slot=5, length=4, full_strb=True,
                             t_phy_wrlat=t, seed_tag=t)
        await tb.wait_clocks('mc_clk', 4)


async def _partial_strb(tb: WrBeatSequencerTB):
    # Alternating full/partial wstrb across the burst — verifies the
    # DFI mask polarity inversion AND per-lane packing.
    for length in [2, 4, 8, 16]:
        await _run_one_burst(tb, slot=(length & 0xF), length=length,
                             full_strb=False, t_phy_wrlat=2,
                             seed_tag=length)
        await tb.wait_clocks('mc_clk', 4)


async def _back_to_back(tb: WrBeatSequencerTB):
    # Three bursts issued sequentially, each verified independently.
    # v1 sequencer is single-in-flight; each await_burst_complete drains.
    for i, length in enumerate([4, 8, 16]):
        await _run_one_burst(tb, slot=i, length=length, full_strb=True,
                             t_phy_wrlat=2, seed_tag=i)
        await tb.wait_clocks('mc_clk', 2)


async def _multi_outstanding(tb: WrBeatSequencerTB):
    """v2 multi-outstanding: issue two ops back-to-back without waiting
    for the first to drain. Verifies op_ready stays high so the second
    handshake succeeds immediately, and both bursts produce correct DFI
    output in op-issue order."""
    burst_a = tb.make_burst(slot=2, length=4, full_strb=True,
                            t_phy_wrlat=2, seed_tag=0xAA)
    burst_b = tb.make_burst(slot=7, length=8, full_strb=True,
                            t_phy_wrlat=2, seed_tag=0xBB)

    await tb.issue_op(burst_a)
    # Issue B immediately — op_ready should stay high since MAX_CONCURRENT≥2.
    await tb.issue_op(burst_b, clear_captures=False)

    await tb.await_burst_complete(burst_a)
    await tb.await_burst_complete(burst_b)

    # The captured_cycles list contains A's cycles followed by B's cycles
    # (FIFO drive order). Split by burst length.
    n_a = (len(burst_a.beats) + tb.DFI_RATE - 1) // tb.DFI_RATE
    n_b = (len(burst_b.beats) + tb.DFI_RATE - 1) // tb.DFI_RATE

    captured_a = tb.captured_cycles[:n_a]
    captured_b = tb.captured_cycles[n_a:n_a + n_b]

    expected_a = tb.expected_dfi_cycles(burst_a)
    expected_b = tb.expected_dfi_cycles(burst_b)

    for i, (g, e) in enumerate(zip(captured_a, expected_a)):
        assert g.data == e.data, f"A cycle {i} data: got {g.data:#x} want {e.data:#x}"
        assert g.mask == e.mask, f"A cycle {i} mask: got {g.mask:#x} want {e.mask:#x}"
    for i, (g, e) in enumerate(zip(captured_b, expected_b)):
        assert g.data == e.data, f"B cycle {i} data: got {g.data:#x} want {e.data:#x}"
        assert g.mask == e.mask, f"B cycle {i} mask: got {g.mask:#x} want {e.mask:#x}"

    # b_complete order must match op-issue order (slot A then slot B).
    assert tb.b_completes == [burst_a.slot, burst_b.slot], (
        f"b_complete order: got {tb.b_completes} want [{burst_a.slot}, {burst_b.slot}]"
    )


async def _random_soak(tb: WrBeatSequencerTB):
    rng = random.Random(tb.SEED ^ 0xBEEF)
    n_bursts = {'gate': 8, 'func': 32, 'full': 96}.get(tb.TEST_LEVEL, 32)
    for _ in range(n_bursts):
        length      = rng.randint(1, 32)
        slot        = rng.randint(0, (1 << tb.WSL) - 1)
        full_strb   = rng.random() < 0.6
        t_phy_wrlat = rng.randint(0, 6)
        seed_tag    = rng.randint(0, 0xFFFF)
        await _run_one_burst(tb, slot=slot, length=length,
                             full_strb=full_strb,
                             t_phy_wrlat=t_phy_wrlat,
                             seed_tag=seed_tag)
        await tb.wait_clocks('mc_clk', rng.randint(1, 5))


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = [
    "smoke",
    "burst_len_sweep",
    "tphy_sweep",
    "partial_strb",
    "back_to_back",
    "multi_outstanding",
    "random_soak",
]

# (test_type, DFI_RATE)
_GATE = [(t, 2) for t in ["smoke", "burst_len_sweep", "partial_strb"]]
_FUNC = [(t, 2) for t in _ALL_TYPES] + [(t, 4) for t in ["smoke", "burst_len_sweep", "partial_strb"]]
_FULL = _FUNC + [
    (t, 4) for t in _ALL_TYPES
] + [
    ("random_soak", 2),
    ("random_soak", 4),
]
# Dedupe FULL so every (type, rate) tuple is unique. Without this, pytest
# auto-disambiguates the colliding IDs with _0/_1 suffixes, and parallel
# workers race on the same local_sim_build/ directory → make Error 2.
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,dfi_rate", _PARAMS,
                         ids=[f"{t[0]}-r{t[1]}" for t in _PARAMS])
def test_wr_beat_sequencer(request, test_type, dfi_rate):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "wr_beat_sequencer"

    test_name = f"test_wr_beat_sequencer_{test_type}_r{dfi_rate}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/fub/wr_beat_sequencer.f"
    )
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path
    )

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path     = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT":               dut_name,
        "LOG_PATH":          log_path,
        "COCOTB_LOG_LEVEL":  "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED":              str(random.randint(0, 100000)),
        "TEST_TYPE":         test_type,
        "TEST_LEVEL":        _TEST_LEVEL.lower(),
        "WR_CAM_DEPTH":      "16",
        "W_BUF_PTR_WIDTH":   "7",
        "BURST_LEN_WIDTH":   "8",
        "DRAM_BEAT_WIDTH":   "64",
        "DFI_RATE":          str(dfi_rate),
        "MAX_BURST_LEN":     "256",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        extra_env["VERILATOR_TRACE"] = "1"
        extra_env["VERILATOR_TRACE_FST"] = "1"

    parameters = {
        "WR_CAM_DEPTH":    "16",
        "W_BUF_PTR_WIDTH": "7",
        "BURST_LEN_WIDTH": "8",
        "DRAM_BEAT_WIDTH": "64",
        "DFI_RATE":        str(dfi_rate),
        "MAX_BURST_LEN":   "256",
    }

    sim_args  = []
    plus_args = []
    if enable_waves:
        sim_args  += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_wr_beat_sequencer",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=parameters,
        compile_args=compile_args,
        sim_args=sim_args,
        plus_args=plus_args,
        waves=enable_waves,
        keep_files=True,
        timescale="1ns/1ps",
    )
