# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-18

"""
Unit-test runner for `rd_cmd_cam_fub`.

Same structure as test_wr_cmd_cam.py; covers push/free-slot, match vectors,
issued masking, beat counting + entry_complete, snapshot, occupancy and
random soak.
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

from tbclasses.rd_cmd_cam_tb import RdCmdCamTB  # noqa: E402


# ---------------------------------------------------------------------------
# CocoTB dispatch
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_rd_cmd_cam(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke")
    log = logging.getLogger("rd_cmd_cam_test")
    log.info(f"TEST_TYPE={test_type}")

    tb = RdCmdCamTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.check_occupancy()

    scenarios = {
        "smoke":            _smoke,
        "fill_to_full":     _fill_to_full,
        "free_slot_picker": _free_slot_picker,
        "match_query":      _match_query,
        "match_rowhit":     _match_rowhit,
        "issued_masking":   _issued_masking,
        "beat_walk":        _beat_walk,
        "beat_interleave":  _beat_interleave,
        "snapshot":         _snapshot,
        "occupancy":        _occupancy,
        "random_soak":      _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    await tb.wait_clocks('mc_clk', 10)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------

async def _smoke(tb: RdCmdCamTB):
    L = 4
    slot = await tb.push(axi_id=3, rank=0, bank=2, row=0x100, col=0x40, length=L)
    assert slot == 0
    await tb.verify_snapshot()
    await tb.check_occupancy()
    for _ in range(L):
        await tb.beat(slot)
    await tb.check_occupancy()


async def _fill_to_full(tb: RdCmdCamTB):
    depth = tb.RD_CAM_DEPTH
    for i in range(depth):
        slot = await tb.push(axi_id=i & tb.MASK_ID, rank=0,
                             bank=i & tb.MASK_BNK,
                             row=(0x100 + i) & tb.MASK_ROW,
                             col=(0x10 * i) & tb.MASK_COL, length=2)
        assert slot == i, f"expected slot {i}, got {slot}"
    await tb.check_occupancy()
    await tb.push(axi_id=0xF, rank=0, bank=0, row=0, col=0, length=1,
                  expect_ready=False)
    assert tb.scb.occupancy() == depth


async def _free_slot_picker(tb: RdCmdCamTB):
    for i in range(4):
        await tb.push(axi_id=i, rank=0, bank=i & tb.MASK_BNK,
                      row=i, col=0, length=1)
    # Drive last beat of slot 1 → self-clears
    await tb.beat(1)
    await tb.wait_clocks('mc_clk', 1)
    slot = await tb.push(axi_id=0xA, rank=0, bank=3, row=0xABC, col=0, length=2)
    assert slot == 1, f"expected slot 1, got {slot}"


async def _match_query(tb: RdCmdCamTB):
    items = [
        (0, 0, 0x000, 0x00),
        (0, 1, 0x100, 0x10),
        (0, 1, 0x200, 0x20),
        (0, 2, 0x300, 0x30),
        (0, 7, 0x3FF, 0x40),
    ]
    for i, (r, b, row, col) in enumerate(items):
        await tb.push(axi_id=i, rank=r, bank=b, row=row, col=col, length=1)
    for rnk in range(min(2, tb.NUM_RANKS)):
        for bnk in range(tb.NUM_BANKS):
            await tb.query(q_rank=rnk, q_bank=bnk, q_row=0)


async def _match_rowhit(tb: RdCmdCamTB):
    items = [
        (0, 1, 0x100, 0x10),
        (0, 1, 0x100, 0x20),
        (0, 1, 0x200, 0x30),
        (0, 2, 0x100, 0x40),
    ]
    for i, (r, b, row, col) in enumerate(items):
        await tb.push(axi_id=i, rank=r, bank=b, row=row, col=col, length=1)
    await tb.query(q_rank=0, q_bank=1, q_row=0x100)
    await tb.query(q_rank=0, q_bank=1, q_row=0x200)
    await tb.query(q_rank=0, q_bank=2, q_row=0x100)


async def _issued_masking(tb: RdCmdCamTB):
    sa = await tb.push(axi_id=1, rank=0, bank=2, row=0x100, col=0, length=1)
    sb = await tb.push(axi_id=2, rank=0, bank=2, row=0x100, col=8, length=1)
    pend, _ = await tb.query(q_rank=0, q_bank=2, q_row=0x100)
    assert pend == ((1 << sa) | (1 << sb))
    await tb.mark_issued(sa)
    pend, _ = await tb.query(q_rank=0, q_bank=2, q_row=0x100)
    assert pend == (1 << sb)


async def _beat_walk(tb: RdCmdCamTB):
    L = 8
    slot = await tb.push(axi_id=5, rank=0, bank=0, row=0x100, col=0, length=L)
    for beat in range(L):
        last = await tb.beat(slot)
        assert last == (beat == L - 1), \
            f"beat {beat}: last={last} expected {beat == L - 1}"
    # Slot should self-clear on the last beat
    assert not tb.scb.slots[slot].valid
    await tb.check_occupancy()


async def _beat_interleave(tb: RdCmdCamTB):
    L = 4
    sa = await tb.push(axi_id=1, rank=0, bank=0, row=0, col=0, length=L)
    sb = await tb.push(axi_id=2, rank=0, bank=1, row=0, col=0, length=L)
    order = [sa, sb, sa, sb, sa, sb, sa, sb]
    for slot in order:
        await tb.beat(slot)
    assert not tb.scb.slots[sa].valid
    assert not tb.scb.slots[sb].valid


async def _snapshot(tb: RdCmdCamTB):
    items = [
        (1, 0, 0, 0x010, 0x01, 1),
        (2, 0, 1, 0x020, 0x02, 2),
        (3, 0, 7, 0x3FF, 0x03, 3),
    ]
    slots = []
    for it in items:
        slots.append(await tb.push(*it))
    await tb.verify_snapshot()
    await tb.mark_issued(slots[1])
    await tb.verify_snapshot()


async def _occupancy(tb: RdCmdCamTB):
    rng = random.Random(tb.SEED)
    cycles = 60 if tb.TEST_LEVEL == 'gate' else 200
    live = []
    for _ in range(cycles):
        op = rng.choice(['push', 'push', 'complete', 'nop'])
        if op == 'push' and tb.scb.occupancy() < tb.RD_CAM_DEPTH:
            slot = await tb.push(axi_id=rng.randint(0, tb.MASK_ID), rank=0,
                                 bank=rng.randint(0, tb.NUM_BANKS - 1),
                                 row=rng.randint(0, tb.MASK_ROW),
                                 col=rng.randint(0, tb.MASK_COL),
                                 length=1)
            if slot is not None:
                live.append(slot)
        elif op == 'complete' and live:
            slot = rng.choice(live)
            await tb.beat(slot)   # length=1 → self-clear
            live.remove(slot)
        else:
            await tb.wait_clocks('mc_clk', 1)
        await tb.check_occupancy()


async def _random_soak(tb: RdCmdCamTB):
    rng = random.Random(tb.SEED ^ 0xDEAD)
    cycles = {'gate': 200, 'func': 600, 'full': 1500}.get(tb.TEST_LEVEL, 600)
    inflight = {}   # slot -> remaining beats
    for _ in range(cycles):
        op = rng.choice(['push', 'push', 'beat', 'issue', 'nop', 'nop'])
        if op == 'push' and tb.scb.occupancy() < tb.RD_CAM_DEPTH:
            L = rng.randint(1, 4)
            slot = await tb.push(axi_id=rng.randint(0, tb.MASK_ID), rank=0,
                                 bank=rng.randint(0, tb.NUM_BANKS - 1),
                                 row=rng.randint(0, tb.MASK_ROW),
                                 col=rng.randint(0, tb.MASK_COL), length=L)
            if slot is not None:
                inflight[slot] = L
        elif op == 'beat' and inflight:
            candidates = [s for s, r in inflight.items() if r > 0]
            if candidates:
                slot = rng.choice(candidates)
                last = await tb.beat(slot)
                inflight[slot] -= 1
                if last:
                    inflight.pop(slot)
            else:
                await tb.wait_clocks('mc_clk', 1)
        elif op == 'issue':
            cands = [i for i, s in enumerate(tb.scb.slots) if s.valid and not s.issued]
            if cands:
                await tb.mark_issued(rng.choice(cands))
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
    "beat_walk",
    "beat_interleave",
    "snapshot",
    "occupancy",
    "random_soak",
]

_GATE = [(t, 16, 1) for t in ["smoke", "match_query", "beat_walk"]]
_FUNC = [(t, 16, 1) for t in _ALL_TYPES] + [
    ("match_query",  8, 1),
    ("random_soak",  8, 1),
    ("fill_to_full", 8, 1),
]
_FULL = _FUNC + [(t, 16, 2) for t in _ALL_TYPES] + [
    ("random_soak", 32, 1),
    ("random_soak",  4, 1),
]

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,rd_cam_depth,num_ranks", _PARAMS,
                         ids=[f"{t[0]}-d{t[1]}-nr{t[2]}" for t in _PARAMS])
def test_rd_cmd_cam(request, test_type, rd_cam_depth, num_ranks):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "rd_cmd_cam_fub"

    test_name = f"test_rd_cmd_cam_{test_type}_d{rd_cam_depth}_nr{num_ranks}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/fub/rd_cmd_cam_fub.f"
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
        "RD_CAM_DEPTH":      str(rd_cam_depth),
        "NUM_RANKS":         str(num_ranks),
        "NUM_BANKS":         "8",
        "ROW_WIDTH":         "14",
        "COL_WIDTH":         "10",
        "BURST_LEN_WIDTH":   "8",
        "AXI_ID_WIDTH":      "4",
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs"]
        extra_env["VERILATOR_TRACE"] = "1"
        extra_env["VERILATOR_TRACE_FST"] = "1"

    parameters = {
        "RD_CAM_DEPTH":    str(rd_cam_depth),
        "NUM_RANKS":       str(num_ranks),
        "NUM_BANKS":       "8",
        "ROW_WIDTH":       "14",
        "COL_WIDTH":       "10",
        "BURST_LEN_WIDTH": "8",
        "AXI_ID_WIDTH":    "4",
    }

    sim_args = []
    plus_args = []
    if enable_waves:
        sim_args += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_rd_cmd_cam",
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
