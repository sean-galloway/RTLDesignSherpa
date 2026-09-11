#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# bridge_cam (Mode 2, ALLOW_DUPLICATES=1): the per-ID response tracker every
# multi-master bridge slave adapter uses (BRIDGE-015/016). Duplicate tags are
# ordered by a per-entry count; deallocate frees the count-0 entry and
# decrements the rest, so same-ID responses retire oldest-first.
#
# The directed phase reproduces the defect that stalled every full-depth
# arbitration test: an allocate and a deallocate of the SAME tag in one cycle
# gave the new entry max_count+1 computed from the pre-decrement counts, so
# the tag's counts became {0, 2} and the next-but-one deallocate found no
# count-0 entry. deallocate_valid stayed low, the crossbar never raised
# bready, and the slave's B sat unaccepted until the BFM gave up on it.

import os
import random

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path
from TBClasses.shared.test_levels import level_env, reg_level_grid

DEPTH = 8
TAG_W = 4
DATA_W = 2
_ROUNDS = {'gate': 200, 'func': 1000, 'full': 4000}


class Cam:
    def __init__(self, dut):
        self.dut = dut

    async def reset(self):
        d = self.dut
        cocotb.start_soon(Clock(d.clk, 10, units="ns").start())
        for s in ('allocate', 'allocate_tag', 'allocate_data', 'deallocate', 'deallocate_tag'):
            getattr(d, s).value = 0
        d.rst_n.value = 0
        await ClockCycles(d.clk, 5)
        d.rst_n.value = 1
        await ClockCycles(d.clk, 2)

    async def step(self, alloc=None, dealloc=None):
        """One cycle: optional (tag, data) allocate and/or tag deallocate.
        Returns (dealloc_valid, dealloc_data) as presented in that cycle."""
        d = self.dut
        if alloc is not None:
            d.allocate.value = 1
            d.allocate_tag.value = alloc[0]
            d.allocate_data.value = alloc[1]
        if dealloc is not None:
            d.deallocate_tag.value = dealloc
            d.deallocate.value = 1
        await ReadOnly()
        res = (int(d.deallocate_valid.value), int(d.deallocate_data.value))
        await RisingEdge(d.clk)
        d.allocate.value = 0
        d.deallocate.value = 0
        return res

    async def lookup(self, tag):
        d = self.dut
        d.deallocate_tag.value = tag
        await ReadOnly()
        res = (int(d.deallocate_valid.value), int(d.deallocate_data.value))
        await RisingEdge(d.clk)
        return res


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cam_same_cycle_alloc_dealloc_test(dut):
    """Allocate and deallocate the same tag in one cycle; every later
    deallocate of that tag must still find an entry."""
    cam = Cam(dut)
    await cam.reset()
    T = 5
    await cam.step(alloc=(T, 1))            # counts: {0}
    await cam.step(alloc=(T, 2))            # counts: {0, 1}
    v, data = await cam.step(alloc=(T, 3), dealloc=T)   # free count 0 (data 1), add a third
    assert v == 1 and data == 1, f"first deallocate should retire the oldest (data 1): {(v, data)}"
    # Two entries remain (data 2, then 3). Both must be retirable, in order.
    v, data = await cam.step(dealloc=T)
    assert v == 1 and data == 2, (
        f"second deallocate: {(v, data)} -- the same-cycle allocate must take the count the "
        f"retiring entry vacated, not max+1 of the pre-decrement counts")
    v, data = await cam.step(dealloc=T)
    assert v == 1 and data == 3, (
        f"third deallocate: {(v, data)} -- a count gap left this entry unreachable; on the bridge "
        f"this is bready never rising for a valid B")
    v, _ = await cam.lookup(T)
    assert v == 0, "tag still present after all three were retired"
    assert int(dut.tags_empty.value) == 1
    dut._log.info("bridge_cam: same-cycle allocate+deallocate keeps the per-tag order dense")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def cam_random_test(dut):
    """Random allocate/deallocate traffic against a per-tag FIFO model; every
    deallocate must return the oldest live entry's data for that tag, and
    full/empty must match the model."""
    cam = Cam(dut)
    await cam.reset()
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    rounds = _ROUNDS.get(level, _ROUNDS['gate'])
    rng = random.Random(int(os.environ.get('SEED', '0') or 0))
    model = {}          # tag -> [data,...] oldest first
    live = 0
    dut._log.info(f"random: level={level} rounds={rounds}")
    for r in range(rounds):
        alloc = dealloc = None
        if live < DEPTH and rng.random() < 0.6:
            alloc = (rng.randrange(1 << TAG_W), rng.randrange(1 << DATA_W))
        live_tags = [t for t, q in model.items() if q]
        if live_tags and rng.random() < 0.5:
            dealloc = rng.choice(live_tags)
        v, data = await cam.step(alloc=alloc, dealloc=dealloc)
        if dealloc is not None:
            assert v == 1, f"round {r}: deallocate {dealloc} missed; model has {model[dealloc]}"
            assert data == model[dealloc][0], f"round {r}: tag {dealloc} returned {data}, oldest is {model[dealloc][0]}"
            model[dealloc].pop(0)
            live -= 1
        if alloc is not None:
            model.setdefault(alloc[0], []).append(alloc[1])
            live += 1
        await ReadOnly()
        assert int(dut.tags_full.value) == (1 if live == DEPTH else 0), f"round {r}: full flag vs {live} live"
        assert int(dut.tags_empty.value) == (1 if live == 0 else 0), f"round {r}: empty flag vs {live} live"
        await RisingEdge(dut.clk)
    dut._log.info(f"bridge_cam random: {rounds} rounds, model matched throughout")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_cam(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../rtl',
        'rtl_amba_includes': 'rtl/amba/includes',
    })
    dut_name = "bridge_cam"
    # The CAM's own filelist, not a hand-list: filelist_registry --check owns
    # the closure, and a hand-list is a blind spot it cannot see.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists_static/bridge_cam.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}_{test_level}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cam_same_cycle_alloc_dealloc_test,cam_random_test",
        parameters={'TAG_WIDTH': TAG_W, 'DATA_WIDTH': DATA_W, 'DEPTH': DEPTH,
                    'ALLOW_DUPLICATES': 1, 'PIPELINE_EVICT': 0},
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={'COCOTB_LOG_LEVEL': 'INFO', 'LOG_PATH': log_path,
                   'COCOTB_RESULTS_FILE': results_path, **level_env(test_level), **waves['extra_env']},
    )
