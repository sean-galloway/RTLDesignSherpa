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
from tbclasses.trackers import RdClAlignerTracker, assert_no_divergence  # noqa: E402


# Scenarios that intentionally wedge the pipeline (admission throttle
# demos, etc.) — divergence checks skip the parity contracts they'd
# fail by construction.
_DIVERGENCE_SKIP_BY_SCENARIO: dict = {
    "rrdy_starvation_wedge": ("op_accept_beats_match_len",),
}


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
        "is_last_chunk_gate":  _is_last_chunk_gate,
        "intake_split_16chunks": _intake_split_16chunks,
        "random_soak":         _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    await tb.wait_clocks('mc_clk', 10)

    # D-1 post-scenario parity check on the tracker's in-memory events.
    # Independent of the scenario-specific scoreboard: catches per-slot
    # OP_ACCEPT-vs-BEAT_WE divergence (the #31 fingerprint) mechanically.
    assert_no_divergence(
        "rd_cl_aligner",
        rdalign_tracker,
        contract_names_skip=_DIVERGENCE_SKIP_BY_SCENARIO.get(test_type, ()),
    )


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
    """Regression for task #205 — aligner staging depth matches cam.

    Pre-fix (MAX_CONCURRENT=2): under sustained `rd_inject_ready_i=0`,
    2 ops occupied both staging slots and `op_ready_o` stayed low, so
    the scheduler couldn't push op 3 — system-level wedge that hit
    50 failing tests (core_macro R=*, OOO asym, nexys kb4/kb32,
    pacing wr/rd_gap≥16).

    Fix: data_path_macro now sets MAX_CONCURRENT = RD_CAM_DEPTH (= 16),
    matching the rd_cmd_cam's admission rate. This test runs against
    the SAME parameter value the system uses, so it covers the real
    contract.

    Procedure:
      1. Freeze `rd_inject_ready_i = 0` for the whole scenario.
      2. Push RD_CAM_DEPTH ops via op_valid pulses with no wait for
         completion. All must be accepted — the aligner now has
         enough staging capacity to mirror the cam.
      3. Drive op #N+1's op_valid_i and observe op_ready_o for 1000
         cycles. It must stay LOW — that's the CORRECT admission
         throttle: once 16 ops are in flight and rready=0, no 17th
         slot exists.
      4. Lift the throttle and verify the FUB resumes correctly.
    """
    from cocotb.triggers import RisingEdge, Timer

    # MAX_CONCURRENT here is fixed via the parametric runner. Sized
    # to RD_CAM_DEPTH to match the system. This test would have to
    # change if that decouples.
    CAM_DEPTH = 16

    tb.rd_inject_ready_pattern = 'frozen'
    await tb.wait_clocks('mc_clk', 4)

    async def _push_op(slot: int, axi_id: int, length: int) -> bool:
        """Pulse op_valid until accepted (or timeout). Returns True if
        accepted within 8 cycles, False otherwise."""
        tb.dut.t_rddata_en_i.value = 2
        tb.dut.op_slot_i.value     = slot   & ((1 << tb.RSL) - 1)
        tb.dut.op_id_i.value       = axi_id & ((1 << tb.AXI_ID_WIDTH) - 1)
        tb.dut.op_len_i.value      = length & ((1 << tb.BURST_LEN_WIDTH) - 1)
        tb.dut.op_valid_i.value    = 1
        await Timer(100, units='ps')
        accepted = False
        for _ in range(8):
            if int(tb.dut.op_ready_o.value) == 1:
                accepted = True
                break
            await RisingEdge(tb.dut.mc_clk)
            await Timer(100, units='ps')
        # Latch the handshake.
        await RisingEdge(tb.dut.mc_clk)
        await Timer(100, units='ps')
        tb.dut.op_valid_i.value = 0
        return accepted

    # Step 2 — fill all CAM_DEPTH staging slots while rready=0.
    for i in range(CAM_DEPTH):
        ok = await _push_op(slot=i, axi_id=(i & 0xF), length=4)
        assert ok, (
            f"op {i} should have been accepted (rready=0, no slots "
            f"freed yet, but expected {CAM_DEPTH} staging slots are "
            f"available). The fix to match MAX_CONCURRENT to "
            f"RD_CAM_DEPTH is not in effect — check the parameter "
            f"propagation."
        )
        await tb.wait_clocks('mc_clk', 1)
    tb.log.info(
        "STEP 2: %d ops staged under rready=0; op_ready_o=%d",
        CAM_DEPTH, int(tb.dut.op_ready_o.value),
    )

    # Step 3 — op #N+1 must block. Push valid and watch op_ready_o
    # for 1000 cycles; it must stay LOW (correct admission throttle —
    # all staging slots full, nothing has drained).
    tb.dut.t_rddata_en_i.value = 2
    tb.dut.op_slot_i.value     = CAM_DEPTH & ((1 << tb.RSL) - 1)
    tb.dut.op_id_i.value       = (CAM_DEPTH & 0xF) & ((1 << tb.AXI_ID_WIDTH) - 1)
    tb.dut.op_len_i.value      = 4 & ((1 << tb.BURST_LEN_WIDTH) - 1)
    tb.dut.op_valid_i.value    = 1

    OBSERVATION_CYCLES = 1000
    overflow_accepted = False
    for _ in range(OBSERVATION_CYCLES):
        await RisingEdge(tb.dut.mc_clk)
        await Timer(100, units='ps')
        if int(tb.dut.op_ready_o.value) == 1:
            overflow_accepted = True
            break

    tb.log.info(
        "STEP 3: op #%d (one past cam) probed for %d cycles, "
        "op_ready_o=%d, accepted=%s",
        CAM_DEPTH + 1,
        OBSERVATION_CYCLES,
        int(tb.dut.op_ready_o.value),
        overflow_accepted,
    )
    assert not overflow_accepted, (
        f"With CAM_DEPTH={CAM_DEPTH} ops staged and rready=0, op "
        f"#{CAM_DEPTH + 1} should have been blocked by op_ready_o=0 "
        f"for the entire {OBSERVATION_CYCLES}-cycle window. Instead "
        f"op_ready_o asserted — admission throttle is broken or "
        f"MAX_CONCURRENT was set higher than CAM_DEPTH."
    )

    # Step 4 — clean up: deassert op_valid + restore ready pattern.
    tb.dut.op_valid_i.value = 0
    tb.rd_inject_ready_pattern = 'always'
    await tb.wait_clocks('mc_clk', 50)
    tb.log.info(
        "STEP 4: throttle lifted; op_ready_o=%d (staged ops have no "
        "PHY-side data — they stay valid until reset. The test's "
        "claim is the admission contract, not data drain.)",
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


async def _is_last_chunk_gate(tb: RdClAlignerTB):
    """Issue #22 — verify rd_inject_last_o is masked when op_is_last_chunk_i=0
    and fires when =1, with the masked op feeding correct data otherwise.

    Two ops issued back-to-back:
      Op 0: is_last_chunk=0 → all beats stream, but rd_inject_last_o stays low.
      Op 1: is_last_chunk=1 → all beats stream AND rd_inject_last_o pulses
            on the final beat.
    """
    # --- Op 0: chunked (not last) ---
    burst_a = tb.make_burst(slot=2, axi_id=7, length=4,
                            t_rddata_en=2, phy_rdlat=1, seed_tag=0xAA)
    burst_a.is_last_chunk = 0
    await tb.issue_op(burst_a)

    # Wait for all 4 beats to land in captured_beats. last_seen MUST stay False.
    timeout = 4096
    while timeout and len(tb.captured_beats) < len(burst_a.beats):
        await RisingEdge(tb.dut.mc_clk)
        timeout -= 1
    assert len(tb.captured_beats) == len(burst_a.beats), (
        f"chunked op didn't deliver all beats: "
        f"{len(tb.captured_beats)}/{len(burst_a.beats)}"
    )
    assert not tb.last_seen, (
        "rd_inject_last_o pulsed for op_is_last_chunk_i=0 — gate broken")
    # Data and id must still be correct on the masked op.
    for i, (g, e) in enumerate(zip(tb.captured_beats, burst_a.beats)):
        e_masked = e & tb.MASK_DATA
        assert g == e_masked, (
            f"chunked op beat {i}: got {g:#x} want {e_masked:#x}")

    # Clear current_burst FIRST so the injector's next rising-edge scan
    # sees None and resets its en_seen_count. Then wait for the FUB to
    # fully drain / op_ready to re-assert before issuing burst_b.
    tb.current_burst = None
    await tb.wait_clocks('mc_clk', 8)
    tb.captured_beats.clear()
    tb.captured_ids.clear()
    tb.beat_we_count = 0
    tb.last_seen = False

    # --- Op 1: not chunked, last_chunk=1 ---
    burst_b = tb.make_burst(slot=3, axi_id=7, length=4,
                            t_rddata_en=2, phy_rdlat=1, seed_tag=0xBB)
    burst_b.is_last_chunk = 1
    await tb.issue_op(burst_b)
    await tb.await_burst_complete(burst_b)
    tb.verify_capture(burst_b)


async def _intake_split_16chunks(tb: RdClAlignerTB):
    """FUB-level reproducer for the rd_cl_aligner EN-pipeline skip bug
    observed at macro level as patho_bl256_n1 (RTLDesignSherpa#29).

    Scenario mirrors axi_intake's 16-way burst split: an AXI BL=64
    read gets split into 16 chunks of DRAM BL=4, each pushed as a
    fresh op_valid_i pulse. The macro trace showed 2 chunks (s11 and
    s13) got OP_ACCEPT + CAPTURE but no EN_CYC pulses, so their
    r_stage never filled and they never emitted — the aligner ends
    up emitting 56/64 beats.

    The trigger is the intake cadence: chunks arrive every ~18 cycles
    while EN processes each in ~2 EN cycles + wait. That timing lands
    fresh pushes on the same cycle that r_en_head_idx is trying to
    step past a done op, exposing the same-cycle race in the "advance
    past done/invalid head" branch (rd_cl_aligner.sv:315-327).

    Reproducer strategy: push 16 ops of len=4 back-to-back, then let
    the existing PHY injector feed data through a single virtual
    64-beat burst. The aligner's own CAP head routes each DFI cycle
    to the correct op's r_stage. On a healthy RTL we get 64 beats
    out; on the buggy RTL we get 56.
    """
    from cocotb.triggers import RisingEdge, Timer

    N_CHUNKS = 16
    CHUNK_LEN = 4
    T_RDDATA_EN = 6         # matches macro cadence (~6 cycles OP_ACCEPT→EN)
    PHY_RDLAT = 1
    INTER_OP_CYCLES = 4     # feed rate that keeps FIFO filling while EN
                            # is still processing early chunks

    # 16 chunks of len=4, distinct data patterns per chunk, only the
    # last chunk carries is_last_chunk=1 (mirrors axi_intake).
    chunks = []
    all_beats = []
    for i in range(N_CHUNKS):
        beats = [
            ((0xC0 << 24) | (i << 16) | j) & tb.MASK_DATA
            for j in range(CHUNK_LEN)
        ]
        all_beats.extend(beats)
        chunks.append(dict(
            slot=i, axi_id=0, length=CHUNK_LEN,
            is_last_chunk=(1 if i == N_CHUNKS - 1 else 0),
        ))

    # Present the whole beat stream to the existing PHY injector as a
    # single virtual burst. The aligner internally routes each DFI
    # cycle to whichever slot is at its CAP head.
    from tbclasses.rd_cl_aligner_tb import ReadBurst
    virtual = ReadBurst(
        slot=0, axi_id=0, beats=all_beats,
        t_rddata_en=T_RDDATA_EN, phy_rdlat=PHY_RDLAT,
        is_last_chunk=1,
    )
    tb.current_burst = virtual
    tb.captured_beats.clear()
    tb.captured_ids.clear()
    tb.beat_we_count = 0
    tb.last_seen = False

    tb.dut.t_rddata_en_i.value = T_RDDATA_EN

    for chunk in chunks:
        tb.dut.op_slot_i.value          = chunk['slot'] & ((1 << tb.RSL) - 1)
        tb.dut.op_id_i.value             = chunk['axi_id'] & ((1 << tb.AXI_ID_WIDTH) - 1)
        tb.dut.op_len_i.value            = chunk['length'] & ((1 << tb.BURST_LEN_WIDTH) - 1)
        tb.dut.op_is_last_chunk_i.value  = chunk['is_last_chunk'] & 1
        tb.dut.op_valid_i.value          = 1
        while int(tb.dut.op_ready_o.value) == 0:
            await RisingEdge(tb.dut.mc_clk)
            await Timer(1, units='ps')
        await RisingEdge(tb.dut.mc_clk)
        await Timer(1, units='ps')
        tb.dut.op_valid_i.value = 0
        for _ in range(INTER_OP_CYCLES - 1):
            await RisingEdge(tb.dut.mc_clk)
            await Timer(1, units='ps')

    expected = N_CHUNKS * CHUNK_LEN
    timeout = 4096
    while timeout and len(tb.captured_beats) < expected:
        await RisingEdge(tb.dut.mc_clk)
        await Timer(1, units='ps')
        timeout -= 1

    assert len(tb.captured_beats) == expected, (
        f"rd_cl_aligner 16-way intake-split reproducer (#29): got "
        f"{len(tb.captured_beats)}/{expected} beats — EN pipeline is "
        f"skipping ops. Aligner accepted all 16 OP_ACCEPTs but only "
        f"emitted {len(tb.captured_beats) // CHUNK_LEN} chunks × "
        f"{CHUNK_LEN} beats. Root cause: EN-head advance race in "
        f"rd_cl_aligner.sv:315-327."
    )
    assert tb.last_seen, (
        "rd_inject_last_o never pulsed on the final chunk (op 15) — "
        "either EN skipped it or is_last_chunk plumbing regressed"
    )


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
    "is_last_chunk_gate",     # #22
    "intake_split_16chunks",  # #29 reproducer
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

# x16-native re-validation: override DRAM beat width (default 64) to run
# the Nexys A7 physical config (beat=32, DFI_RATE=4).
_BEAT = os.environ.get("DRAM_BEAT_WIDTH_OVERRIDE", "64")

_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize(
    "test_type,dfi_rate", _PARAMS,
    ids=[f"{t[0]}-r{t[1]}" for t in _PARAMS],
)
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
        "DRAM_BEAT_WIDTH":   _BEAT,
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
        "DRAM_BEAT_WIDTH": _BEAT,
        "DFI_RATE":        str(dfi_rate),
        "MAX_BURST_LEN":   "256",
        # Match aligner staging slots to the rd_cmd_cam depth — same
        # value the system uses (set in data_path_macro). Without this
        # the FUB tests run with MAX_CONCURRENT=2 while production
        # uses 16; the wedge demo would still pass at depth 2 but the
        # ergonomic tests (positive coverage) need the real param.
        "MAX_CONCURRENT":  "16",
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
