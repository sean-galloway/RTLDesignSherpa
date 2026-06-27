# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-20

"""
Unit-test runner for `rd_cl_aligner`.

Scenarios (all scoreboarded via RdClAlignerTB.verify_capture):
  smoke           single 4-beat read, t_rddata_en=2, phy_rdlat=1
  burst_len_sweep lens {1, 2, 3, 4, 8, 16, 33, 64}
  tphy_sweep      t_rddata_en in {0, 1, 2, 5, 10}
  phy_rdlat_sweep PHY response delay in {0, 1, 2, 5, 10}
  rrdy_throttle   rd_inject_ready_i with 50/50 backpressure
  back_to_back    3 sequential reads on single-in-flight v1 FSM
  random_soak     random bursts (length, t_rddata_en, phy_rdlat)
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

from ddr2_lpddr2_coverage import (  # noqa: E402
    get_coverage_compile_args, get_coverage_env,
)

from tbclasses.rd_cl_aligner_tb import RdClAlignerTB  # noqa: E402
from tbclasses.trackers import RdClAlignerTracker  # noqa: E402


# ---------------------------------------------------------------------------
# CocoTB dispatch
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_rd_cl_aligner(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    log = logging.getLogger("rd_cl_aligner_test")
    log.info(f"TEST_TYPE={test_type}")

    tb = RdClAlignerTB(dut)
    # Tracker auto-dumps <sim_build>/rdalign.out at end of sim.
    rdalign_tracker = RdClAlignerTracker(dut)
    cocotb.start_soon(rdalign_tracker.run())
    await tb.setup_clocks_and_reset()

    scenarios = {
        "smoke":               _smoke,
        "burst_len_sweep":     _burst_len_sweep,
        "tphy_sweep":          _tphy_sweep,
        "phy_rdlat_sweep":     _phy_rdlat_sweep,
        "rrdy_throttle":       _rrdy_throttle,
        "rrdy_starvation_wedge": _rrdy_starvation_wedge,
        "back_to_back":        _back_to_back,
        "id_propagate":        _id_propagate,
        "random_soak":         _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    await tb.wait_clocks('mc_clk', 10)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------

async def _run_one_burst(tb: RdClAlignerTB, *, slot: int, axi_id: int,
                         length: int, t_rddata_en: int, phy_rdlat: int,
                         seed_tag: int = 0):
    burst = tb.make_burst(slot=slot, axi_id=axi_id, length=length,
                          t_rddata_en=t_rddata_en, phy_rdlat=phy_rdlat,
                          seed_tag=seed_tag)
    await tb.issue_op(burst)
    await tb.await_burst_complete(burst)
    tb.verify_capture(burst)
    return burst


async def _smoke(tb: RdClAlignerTB):
    await _run_one_burst(tb, slot=3, axi_id=5, length=4,
                         t_rddata_en=2, phy_rdlat=1)


async def _burst_len_sweep(tb: RdClAlignerTB):
    for length in [1, 2, 3, 4, 8, 16, 33, 64]:
        await _run_one_burst(tb, slot=(length & 0xF), axi_id=(length & 0xF),
                             length=length, t_rddata_en=2, phy_rdlat=1,
                             seed_tag=length)
        await tb.wait_clocks('mc_clk', 6)


async def _tphy_sweep(tb: RdClAlignerTB):
    for t in [0, 1, 2, 5, 10]:
        await _run_one_burst(tb, slot=5, axi_id=7, length=4,
                             t_rddata_en=t, phy_rdlat=1, seed_tag=t)
        await tb.wait_clocks('mc_clk', 4)


async def _phy_rdlat_sweep(tb: RdClAlignerTB):
    # PHY responds at varying delays after the controller drives en —
    # the en/rx overlap window changes.
    for lat in [0, 1, 2, 5, 10]:
        await _run_one_burst(tb, slot=5, axi_id=7, length=8,
                             t_rddata_en=2, phy_rdlat=lat,
                             seed_tag=lat | 0x100)
        await tb.wait_clocks('mc_clk', 4)


async def _rrdy_throttle(tb: RdClAlignerTB):
    tb.rd_inject_ready_pattern = 'throttle'
    try:
        for length in [4, 8, 16]:
            await _run_one_burst(tb, slot=2, axi_id=3, length=length,
                                 t_rddata_en=2, phy_rdlat=1,
                                 seed_tag=length | 0x200)
            await tb.wait_clocks('mc_clk', 4)
    finally:
        tb.rd_inject_ready_pattern = 'always'


async def _rrdy_starvation_wedge(tb: RdClAlignerTB):
    """Focused reproducer for task #205 — R-side back-pressure wedges
    rd_cl_aligner with MAX_CONCURRENT=2.

    Hypothesis: under sustained `rd_inject_ready_i=0`, two pending ops
    occupy both staging slots and neither can drain via EMIT.
    `op_ready_o` then stays low and the scheduler can't push a 3rd op
    — system-level effect is the wedge that showed up across 50
    failing tests (core_macro R=*, OOO asym, nexys kb4 / kb32,
    pacing wr/rd_gap≥16).

    Procedure:
      1. Freeze `rd_inject_ready_i = 0` for the entire scenario.
      2. Issue op 1 + op 2 (no wait for complete) — both accepted
         since MAX_CONCURRENT=2.
      3. Drive op 3's op_valid_i and watch `op_ready_o` for 1000
         cycles. Under the wedge it must STAY LOW the whole time.
         If it asserts: the FUB has architecturally avoided the
         wedge somehow, and the failing tests have a different
         root cause.
      4. Lift the throttle (pattern='always'). Op_ready_o must
         eventually rise once op 1 + 2 drain — proving the FUB is
         not broken in some other way, just back-pressure-sensitive.

    This test EXPECTS the wedge currently. The assertion that
    op_ready_o stays low is the bug demonstration. Once the fix
    lands (bump MAX_CONCURRENT, or add per-op emit FIFOs), this
    test will need to be inverted — at that point op_ready_o
    should NEVER stall under N>MAX_CONCURRENT pending ops.
    """
    from cocotb.triggers import RisingEdge, Timer

    tb.rd_inject_ready_pattern = 'frozen'
    # Let the new pattern settle.
    await tb.wait_clocks('mc_clk', 4)

    # Op 1 + Op 2: push them via raw op_valid pulses (don't go through
    # _run_one_burst, which would await completion).
    async def _push_op(slot: int, axi_id: int, length: int) -> None:
        tb.dut.t_rddata_en_i.value = 2
        tb.dut.op_slot_i.value     = slot   & ((1 << tb.RSL) - 1)
        tb.dut.op_id_i.value       = axi_id & ((1 << tb.AXI_ID_WIDTH) - 1)
        tb.dut.op_len_i.value      = length & ((1 << tb.BURST_LEN_WIDTH) - 1)
        tb.dut.op_valid_i.value    = 1
        await Timer(100, units='ps')
        # Wait at most 8 cycles for op_ready_o == 1 (should be 1 since
        # FUB starts with both slots free; on op 3 we WON'T get a 1).
        for _ in range(8):
            if int(tb.dut.op_ready_o.value) == 1:
                break
            await RisingEdge(tb.dut.mc_clk)
            await Timer(100, units='ps')
        await RisingEdge(tb.dut.mc_clk)
        await Timer(100, units='ps')
        tb.dut.op_valid_i.value = 0

    await _push_op(slot=0, axi_id=0xA, length=4)
    await tb.wait_clocks('mc_clk', 2)
    await _push_op(slot=1, axi_id=0xB, length=4)
    await tb.wait_clocks('mc_clk', 4)

    # Now both staging slots should be occupied. Drive op 3's op_valid_i
    # and observe op_ready_o: under the wedge hypothesis, it must
    # STAY LOW for the entire 1000-cycle window.
    tb.dut.t_rddata_en_i.value = 2
    tb.dut.op_slot_i.value     = 2 & ((1 << tb.RSL) - 1)
    tb.dut.op_id_i.value       = 0xC & ((1 << tb.AXI_ID_WIDTH) - 1)
    tb.dut.op_len_i.value      = 4 & ((1 << tb.BURST_LEN_WIDTH) - 1)
    tb.dut.op_valid_i.value    = 1

    OBSERVATION_CYCLES = 1000
    op3_accepted = False
    for _ in range(OBSERVATION_CYCLES):
        await RisingEdge(tb.dut.mc_clk)
        await Timer(100, units='ps')
        if int(tb.dut.op_ready_o.value) == 1:
            op3_accepted = True
            break

    # Document what we saw and assert the wedge.
    tb.log.info(
        "WEDGE PROBE: after %d cycles with rd_inject_ready_i=0, "
        "op_ready_o=%d, op3_accepted=%s",
        OBSERVATION_CYCLES,
        int(tb.dut.op_ready_o.value),
        op3_accepted,
    )
    assert not op3_accepted, (
        f"Expected the wedge: with rd_inject_ready_i=0 and 2 ops in "
        f"flight, op_ready_o should stay LOW indefinitely "
        f"(MAX_CONCURRENT=2 slot exhaustion). Instead op_ready_o "
        f"asserted within {OBSERVATION_CYCLES} cycles. Either the "
        f"FUB now handles N>MAX_CONCURRENT under back-pressure "
        f"(in which case task #205 root-cause is elsewhere), or "
        f"this test's setup is wrong."
    )

    # Now lift the throttle. The 2 staged ops drain (need PHY data —
    # the standing _phy_injector tracks `current_burst` which is None
    # here, so the staged ops never get CAPTURE data and EMIT can't
    # drain. We just confirm op_ready_o STAYS low until reset
    # cleanup — the wedge IS the point.). Deassert op_valid for the
    # rest of the test.
    tb.dut.op_valid_i.value = 0
    tb.rd_inject_ready_pattern = 'always'
    await tb.wait_clocks('mc_clk', 50)
    tb.log.info(
        "POST-LIFT: rd_inject_ready=1, op_ready_o=%d "
        "(still 0 because the 2 staged ops have no PHY-side data; "
        "wedge fully demonstrated at FUB level)",
        int(tb.dut.op_ready_o.value),
    )


async def _back_to_back(tb: RdClAlignerTB):
    for i, length in enumerate([4, 8, 16]):
        await _run_one_burst(tb, slot=i, axi_id=i+1, length=length,
                             t_rddata_en=2, phy_rdlat=1, seed_tag=i)
        await tb.wait_clocks('mc_clk', 2)


async def _id_propagate(tb: RdClAlignerTB):
    # Drive a series of bursts with deliberately distinct AXI IDs and
    # verify each id flows through to `rd_inject_id_o`. Regression
    # guard for G-01c (rd_snap_id tied to 0 at the top): if op_id_i
    # were silently dropped here, this scenario would fire.
    ID_W = tb.AXI_ID_WIDTH
    ids = [1, 2, 3, 5, 7, (1 << ID_W) - 1, 0, (1 << (ID_W - 1))]
    ids = [i & ((1 << ID_W) - 1) for i in ids]
    for k, aid in enumerate(ids):
        await _run_one_burst(tb, slot=(k & 0xF), axi_id=aid,
                             length=2, t_rddata_en=2, phy_rdlat=1,
                             seed_tag=0x300 | k)
        await tb.wait_clocks('mc_clk', 3)


async def _random_soak(tb: RdClAlignerTB):
    rng = random.Random(tb.SEED ^ 0xCAFE)
    n = {'gate': 8, 'func': 32, 'full': 96}.get(tb.TEST_LEVEL, 32)
    for _ in range(n):
        length      = rng.randint(1, 32)
        slot        = rng.randint(0, (1 << tb.RSL) - 1)
        axi_id      = rng.randint(0, (1 << tb.AXI_ID_WIDTH) - 1)
        t_rddata_en = rng.randint(0, 6)
        phy_rdlat   = rng.randint(0, 6)
        seed_tag    = rng.randint(0, 0xFFFF)
        await _run_one_burst(tb, slot=slot, axi_id=axi_id, length=length,
                             t_rddata_en=t_rddata_en, phy_rdlat=phy_rdlat,
                             seed_tag=seed_tag)
        await tb.wait_clocks('mc_clk', rng.randint(1, 5))


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = [
    "smoke",
    "burst_len_sweep",
    "tphy_sweep",
    "phy_rdlat_sweep",
    "rrdy_throttle",
    "rrdy_starvation_wedge",
    "back_to_back",
    "id_propagate",
    "random_soak",
]

_GATE = [(t, 2) for t in ["smoke", "burst_len_sweep", "phy_rdlat_sweep",
                          "rrdy_throttle", "id_propagate"]]
_FUNC = [(t, 2) for t in _ALL_TYPES] + [(t, 4) for t in ["smoke", "burst_len_sweep", "rrdy_throttle"]]
_FULL = _FUNC + [(t, 4) for t in _ALL_TYPES] + [
    ("random_soak", 2),
    ("random_soak", 4),
]
# Dedupe — otherwise pytest disambiguates colliding IDs with _0/_1 suffixes
# and parallel workers race on the same local_sim_build/ directory.
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,dfi_rate", _PARAMS,
                         ids=[f"{t[0]}-r{t[1]}" for t in _PARAMS])
def test_rd_cl_aligner(request, test_type, dfi_rate):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "rd_cl_aligner"

    test_name = f"test_rd_cl_aligner_{test_type}_r{dfi_rate}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/fub/rd_cl_aligner.f"
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
        "RD_CAM_DEPTH":      "16",
        "AXI_ID_WIDTH":      "4",
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
        "RD_CAM_DEPTH":    "16",
        "AXI_ID_WIDTH":    "4",
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

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_rd_cl_aligner",
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
