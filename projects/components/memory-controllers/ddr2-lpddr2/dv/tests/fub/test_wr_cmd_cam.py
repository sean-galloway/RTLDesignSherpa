# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-18

"""
Unit-test runner for `wr_cmd_cam`.

Structure follows stream's fub-level tests:
  * single cocotb test that dispatches on TEST_TYPE
  * single pytest wrapper parametrized over (TEST_TYPE, depth, num_ranks)
  * TEST_LEVEL (env var, default FUNC) controls matrix density

Scenarios (every one is self-checking via the WrCmdCamScoreboard):
  smoke              one push, then one b_complete; verify every output
  fill_to_full       push CAM_DEPTH entries; verify push_ready_o drops
  free_slot_picker   complete a middle slot; next push must take it
  match_query        push diverse (rank,bank); query all (rank,bank) combos
  match_rowhit       same as above but adds row matching
  issued_masking     mark issued → match_pending must drop for that slot
  beat_pull_walk     pull all beats of a single burst; walk ptr/strb_ptr/last
  beat_pull_interleave  two bursts; interleave beat pulls per slot
  b_complete_cycle   pull all beats, b_complete, verify slot recycles
  snapshot           assorted state, verify the snap_* bus
  occupancy          random push/complete pattern; tick-accurate occupancy
  random_soak        random push/issue/pull/complete for N cycles
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

from tbclasses.wr_cmd_cam_tb import WrCmdCamTB  # noqa: E402


# ---------------------------------------------------------------------------
# CocoTB dispatch
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_wr_cmd_cam(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    log = logging.getLogger("wr_cmd_cam_test")
    log.info(f"TEST_TYPE={test_type}")

    tb = WrCmdCamTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.check_occupancy()  # 0 after reset

    scenarios = {
        "smoke":               _smoke,
        "fill_to_full":        _fill_to_full,
        "free_slot_picker":    _free_slot_picker,
        "match_query":         _match_query,
        "match_rowhit":        _match_rowhit,
        "issued_masking":      _issued_masking,
        "beat_pull_walk":      _beat_pull_walk,
        "beat_pull_interleave":_beat_pull_interleave,
        "b_complete_cycle":    _b_complete_cycle,
        "snapshot":            _snapshot,
        "occupancy":           _occupancy,
        "random_soak":         _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    # idle a few cycles
    await tb.wait_clocks('mc_clk', 10)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------

async def _smoke(tb: WrCmdCamTB):
    slot = await tb.push(axi_id=3, rank=0, bank=2, row=0x100, col=0x40,
                         length=4, wptr=0, sptr=0)
    assert slot == 0, f"first push should land in slot 0, got {slot}"
    await tb.verify_snapshot()
    await tb.check_occupancy()

    # Pull every beat
    for _ in range(4):
        await tb.beat_pull(slot)
    # Finalize with b_complete
    await tb.b_complete(slot)
    await tb.check_occupancy()


async def _fill_to_full(tb: WrCmdCamTB):
    """Push until ready drops; verify ready and slot recycle behaviour."""
    depth = tb.WR_CAM_DEPTH
    for i in range(depth):
        slot = await tb.push(axi_id=i & tb.MASK_ID,
                             rank=0, bank=i & tb.MASK_BNK,
                             row=(0x100 + i) & tb.MASK_ROW,
                             col=(0x10 * i) & tb.MASK_COL,
                             length=2, wptr=(i * 2) & tb.MASK_WPW,
                             sptr=(i * 2) & tb.MASK_WPW)
        assert slot == i, f"expected slot {i}, got {slot}"
    # Now CAM is full. push_ready_o must be 0.
    await tb.wait_clocks('mc_clk', 1)
    await tb.check_occupancy()
    # Attempt a push that must be refused (expect_ready=False inhibits the
    # ready-must-be-high assertion).
    await tb.push(axi_id=0xF, rank=0, bank=0, row=0, col=0, length=1,
                  wptr=0, sptr=0, expect_ready=False)
    assert tb.scb.occupancy() == depth


async def _free_slot_picker(tb: WrCmdCamTB):
    """Complete a middle slot and check the free-slot priority encoder picks
    the lowest free index next."""
    for i in range(4):
        await tb.push(axi_id=i, rank=0, bank=i & tb.MASK_BNK,
                      row=i, col=0, length=1, wptr=i, sptr=i)
    # Drive a single beat then b_complete on slot 1
    await tb.beat_pull(1)
    await tb.b_complete(1)
    await tb.wait_clocks('mc_clk', 1)
    # Next push must take slot 1 (lowest free)
    slot = await tb.push(axi_id=0xA, rank=0, bank=3, row=0xABC, col=0,
                         length=2, wptr=0x40, sptr=0x40)
    assert slot == 1, f"expected slot 1 (lowest free), got {slot}"


async def _match_query(tb: WrCmdCamTB):
    """Populate slots with distinct (rank,bank); query every (rank,bank)
    pair and verify match_pending vector."""
    items = [
        # (rank, bank, row, col)
        (0, 0, 0x000, 0x00),
        (0, 1, 0x100, 0x10),
        (0, 1, 0x200, 0x20),   # same (rank,bank) as above
        (0, 2, 0x300, 0x30),
        (0, 7, 0x3FF, 0x40),
    ]
    for i, (r, b, row, col) in enumerate(items):
        await tb.push(axi_id=i, rank=r, bank=b, row=row, col=col,
                      length=1, wptr=i, sptr=i)

    for rnk in range(min(2, tb.NUM_RANKS)):
        for bnk in range(tb.NUM_BANKS):
            await tb.query(q_rank=rnk, q_bank=bnk, q_row=0)


async def _match_rowhit(tb: WrCmdCamTB):
    """Same as match_query but adds a row check."""
    items = [
        (0, 1, 0x100, 0x10),
        (0, 1, 0x100, 0x20),   # same (rank,bank,row) → both rowhit
        (0, 1, 0x200, 0x30),   # different row
        (0, 2, 0x100, 0x40),   # different bank but same row
    ]
    for i, (r, b, row, col) in enumerate(items):
        await tb.push(axi_id=i, rank=r, bank=b, row=row, col=col,
                      length=1, wptr=i, sptr=i)

    # Query (rank=0, bank=1, row=0x100) → expect slots 0 and 1 in rowhit
    await tb.query(q_rank=0, q_bank=1, q_row=0x100)
    await tb.query(q_rank=0, q_bank=1, q_row=0x200)
    await tb.query(q_rank=0, q_bank=2, q_row=0x100)


async def _issued_masking(tb: WrCmdCamTB):
    """Mark a slot issued and verify match_pending drops for it."""
    slot_a = await tb.push(axi_id=1, rank=0, bank=2, row=0x100, col=0,
                           length=1, wptr=0, sptr=0)
    slot_b = await tb.push(axi_id=2, rank=0, bank=2, row=0x100, col=8,
                           length=1, wptr=1, sptr=1)
    pend, _ = await tb.query(q_rank=0, q_bank=2, q_row=0x100)
    assert pend == ((1 << slot_a) | (1 << slot_b))
    await tb.mark_issued(slot_a)
    pend, _ = await tb.query(q_rank=0, q_bank=2, q_row=0x100)
    assert pend == (1 << slot_b), (
        f"after issued, expected only slot {slot_b}, got 0b{pend:b}"
    )


async def _beat_pull_walk(tb: WrCmdCamTB):
    """Single burst, walk every beat; verify ptr/strb_ptr/last each cycle."""
    L = 8
    WP = 0x10
    SP = 0x20
    slot = await tb.push(axi_id=5, rank=0, bank=0, row=0x100, col=0,
                         length=L, wptr=WP, sptr=SP)
    for beat in range(L):
        ptr, sptr, last = await tb.beat_pull(slot)
        assert ptr  == ((WP + beat) & tb.MASK_WPW), \
            f"beat {beat}: ptr {ptr} != {WP + beat}"
        assert sptr == ((SP + beat) & tb.MASK_WPW), \
            f"beat {beat}: strb_ptr {sptr} != {SP + beat}"
        assert last == (beat == L - 1), \
            f"beat {beat}: last={last} expected {beat == L - 1}"
    # b_complete clears the slot
    await tb.b_complete(slot)


async def _beat_pull_interleave(tb: WrCmdCamTB):
    """Two bursts pull beats interleaved per cycle."""
    L = 4
    sa = await tb.push(axi_id=1, rank=0, bank=0, row=0, col=0,
                       length=L, wptr=0x00, sptr=0x00)
    sb = await tb.push(axi_id=2, rank=0, bank=1, row=0, col=0,
                       length=L, wptr=0x40, sptr=0x40)
    order = [sa, sb, sa, sb, sa, sb, sa, sb]
    for slot in order:
        await tb.beat_pull(slot)
    await tb.b_complete(sa)
    await tb.b_complete(sb)


async def _b_complete_cycle(tb: WrCmdCamTB):
    """Full lifecycle: push → beat_pull(s) → b_complete → push again."""
    L = 2
    slot = await tb.push(axi_id=7, rank=0, bank=3, row=0x123, col=0,
                         length=L, wptr=0x00, sptr=0x00)
    for _ in range(L):
        await tb.beat_pull(slot)
    await tb.b_complete(slot)
    await tb.check_occupancy()
    # Slot should be empty now; a new push should take slot 0 again
    slot2 = await tb.push(axi_id=8, rank=0, bank=3, row=0x456, col=0,
                          length=1, wptr=0x10, sptr=0x10)
    assert slot2 == slot, f"expected slot {slot} recycled, got {slot2}"


async def _snapshot(tb: WrCmdCamTB):
    """Push a few diverse entries and verify the snap_* bus matches."""
    items = [
        (1, 0, 0, 0x010, 0x01, 1, 0x00, 0x00),
        (2, 0, 1, 0x020, 0x02, 2, 0x10, 0x10),
        (3, 0, 7, 0x3FF, 0x03, 3, 0x20, 0x20),
    ]
    slots = []
    for it in items:
        s = await tb.push(*it)
        slots.append(s)
    await tb.verify_snapshot()
    # Mark middle slot issued and recheck snapshot
    await tb.mark_issued(slots[1])
    await tb.verify_snapshot()


async def _occupancy(tb: WrCmdCamTB):
    """Random push/b_complete sequence; verify dbg_occupancy_o every cycle."""
    rng = random.Random(tb.SEED)
    cycles = 60 if tb.TEST_LEVEL == 'gate' else 200
    live = []
    for _ in range(cycles):
        op = rng.choice(['push', 'push', 'complete', 'nop'])
        if op == 'push' and tb.scb.occupancy() < tb.WR_CAM_DEPTH:
            slot = await tb.push(axi_id=rng.randint(0, tb.MASK_ID),
                                 rank=0, bank=rng.randint(0, tb.NUM_BANKS - 1),
                                 row=rng.randint(0, tb.MASK_ROW),
                                 col=rng.randint(0, tb.MASK_COL),
                                 length=1,
                                 wptr=rng.randint(0, tb.MASK_WPW),
                                 sptr=rng.randint(0, tb.MASK_WPW))
            if slot is not None:
                live.append(slot)
        elif op == 'complete' and live:
            slot = rng.choice(live)
            await tb.beat_pull(slot)   # length=1, so this last beat sets b_pending
            await tb.b_complete(slot)
            live.remove(slot)
        else:
            await tb.wait_clocks('mc_clk', 1)
        await tb.check_occupancy()


async def _random_soak(tb: WrCmdCamTB):
    """Random ops with multi-beat bursts."""
    rng = random.Random(tb.SEED ^ 0xC0FFEE)
    cycles = {'gate': 200, 'func': 600, 'full': 1500}.get(tb.TEST_LEVEL, 600)
    inflight = {}   # slot -> remaining beats
    for _ in range(cycles):
        op = rng.choice(['push', 'push', 'pull', 'issue', 'complete', 'nop', 'nop'])
        if op == 'push' and tb.scb.occupancy() < tb.WR_CAM_DEPTH:
            L = rng.randint(1, 4)
            slot = await tb.push(axi_id=rng.randint(0, tb.MASK_ID),
                                 rank=0, bank=rng.randint(0, tb.NUM_BANKS - 1),
                                 row=rng.randint(0, tb.MASK_ROW),
                                 col=rng.randint(0, tb.MASK_COL),
                                 length=L,
                                 wptr=rng.randint(0, tb.MASK_WPW),
                                 sptr=rng.randint(0, tb.MASK_WPW))
            if slot is not None:
                inflight[slot] = L
        elif op == 'pull' and inflight:
            # Pull a beat from any slot that still has beats remaining
            candidates = [s for s, r in inflight.items() if r > 0]
            if candidates:
                slot = rng.choice(candidates)
                await tb.beat_pull(slot)
                inflight[slot] -= 1
            else:
                await tb.wait_clocks('mc_clk', 1)
        elif op == 'issue' and tb.scb.slots:
            cands = [i for i, s in enumerate(tb.scb.slots) if s.valid and not s.issued]
            if cands:
                await tb.mark_issued(rng.choice(cands))
            else:
                await tb.wait_clocks('mc_clk', 1)
        elif op == 'complete' and inflight:
            # only complete slots whose remaining-beats hit 0
            drained = [s for s, r in inflight.items() if r == 0]
            if drained:
                slot = rng.choice(drained)
                await tb.b_complete(slot)
                inflight.pop(slot)
            else:
                await tb.wait_clocks('mc_clk', 1)
        else:
            await tb.wait_clocks('mc_clk', 1)
        await tb.check_occupancy()


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = [
    "smoke",
    "fill_to_full",
    "free_slot_picker",
    "match_query",
    "match_rowhit",
    "issued_masking",
    "beat_pull_walk",
    "beat_pull_interleave",
    "b_complete_cycle",
    "snapshot",
    "occupancy",
    "random_soak",
]

# (test_type, WR_CAM_DEPTH, NUM_RANKS)
_GATE = [(t, 16, 1) for t in ["smoke", "match_query", "beat_pull_walk", "b_complete_cycle"]]
_FUNC = [(t, 16, 1) for t in _ALL_TYPES] + [
    ("match_query",   8, 1),
    ("random_soak",   8, 1),
    ("fill_to_full",  8, 1),
]
_FULL = _FUNC + [
    (t, 16, 2) for t in _ALL_TYPES
] + [
    ("random_soak", 32, 1),
    ("random_soak",  4, 1),
]
# Dedupe — otherwise pytest disambiguates colliding IDs with _0/_1 suffixes
# and parallel workers race on the same local_sim_build/ directory.
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,wr_cam_depth,num_ranks", _PARAMS,
                         ids=[f"{t[0]}-d{t[1]}-nr{t[2]}" for t in _PARAMS])
def test_wr_cmd_cam(request, test_type, wr_cam_depth, num_ranks):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "wr_cmd_cam"

    test_name = f"test_wr_cmd_cam_{test_type}_d{wr_cam_depth}_nr{num_ranks}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/fub/wr_cmd_cam.f"
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
        "WR_CAM_DEPTH":      str(wr_cam_depth),
        "NUM_RANKS":         str(num_ranks),
        "NUM_BANKS":         "8",
        "ROW_WIDTH":         "14",
        "COL_WIDTH":         "10",
        "BURST_LEN_WIDTH":   "8",
        "W_BUF_PTR_WIDTH":   "7",
        "AXI_ID_WIDTH":      "4",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
        extra_env["VERILATOR_TRACE"] = "1"
        extra_env["VERILATOR_TRACE_FST"] = "1"

    parameters = {
        "WR_CAM_DEPTH":    str(wr_cam_depth),
        "NUM_RANKS":       str(num_ranks),
        "NUM_BANKS":       "8",
        "ROW_WIDTH":       "14",
        "COL_WIDTH":       "10",
        "BURST_LEN_WIDTH": "8",
        "W_BUF_PTR_WIDTH": "7",
        "AXI_ID_WIDTH":    "4",
    }

    sim_args = []
    plus_args = []
    if enable_waves:
        sim_args += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]

    compile_args += get_coverage_compile_args()
    extra_env.update(get_coverage_env(test_name, sim_build=sim_build))

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_wr_cmd_cam",
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
