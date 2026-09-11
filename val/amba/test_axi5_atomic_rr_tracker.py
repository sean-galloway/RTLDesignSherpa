#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# axi5_atomic_rr_tracker (BRIDGE-002 A5-3b): per-ID (ID -> routing tag)
# entries for read-return atomics. Allocated at the atomic's AW, looked up
# combinationally from RID, freed on the R handshake's last beat.

import os
import random

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

DEPTH = 4
ID_W = 4
DATA_W = 2

# Random rounds per level: the directed phases prove each mechanism once;
# the random phase is where allocate/release interleavings pile up.
_ROUNDS = {'gate': 20, 'func': 100, 'full': 400}


class Trk:
    """Cycle-accurate driver for the tracker's three ports."""

    def __init__(self, dut):
        self.dut = dut

    async def reset(self):
        d = self.dut
        cocotb.start_soon(Clock(d.aclk, 10, units="ns").start())
        for sig in ('alloc', 'alloc_id', 'alloc_data', 'lookup_id', 'release_beat'):
            getattr(d, sig).value = 0
        d.aresetn.value = 0
        await ClockCycles(d.aclk, 5)
        d.aresetn.value = 1
        await ClockCycles(d.aclk, 2)

    async def alloc(self, txn_id, data):
        d = self.dut
        d.alloc_id.value = txn_id
        d.alloc_data.value = data
        d.alloc.value = 1
        await RisingEdge(d.aclk)
        d.alloc.value = 0

    async def lookup(self, txn_id):
        """Combinational: returns (hit, hit_data) for this ID."""
        d = self.dut
        d.lookup_id.value = txn_id
        await ReadOnly()
        res = (int(d.hit.value), int(d.hit_data.value))
        await RisingEdge(d.aclk)
        return res

    async def release(self, txn_id):
        d = self.dut
        d.lookup_id.value = txn_id
        d.release_beat.value = 1
        await RisingEdge(d.aclk)
        d.release_beat.value = 0

    async def full(self):
        await ReadOnly()
        v = int(self.dut.full.value)
        await RisingEdge(self.dut.aclk)
        return v


async def _check_all(trk, model, label):
    """Every ID must report exactly what the model holds."""
    for txn_id in range(1 << ID_W):
        hit, data = await trk.lookup(txn_id)
        if txn_id in model:
            assert hit == 1, f"{label}: id {txn_id} allocated but lookup missed"
            assert data == model[txn_id], (
                f"{label}: id {txn_id} routes to {data}, expected {model[txn_id]}")
        else:
            assert hit == 0, f"{label}: id {txn_id} not allocated but lookup hit"


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def rr_tracker_directed_test(dut):
    """Allocate, look up, release, fill, and the same-cycle alloc+release."""
    trk = Trk(dut)
    await trk.reset()
    model = {}

    # Three entries with distinct routing tags.
    for txn_id, data in ((1, 0), (5, 1), (9, 3)):
        await trk.alloc(txn_id, data)
        model[txn_id] = data
    await _check_all(trk, model, "after 3 allocs")
    assert await trk.full() == 0

    # Release the middle one: it misses, the others still hit.
    await trk.release(5)
    del model[5]
    await _check_all(trk, model, "after releasing id 5")

    # A release for an ID that is not tracked must change nothing.
    await trk.release(2)
    await _check_all(trk, model, "after a foreign release")

    # Fill to DEPTH: full asserts, and an alloc while full is ignored
    # without corrupting the live entries.
    for txn_id, data in ((12, 2), (7, 1)):
        await trk.alloc(txn_id, data)
        model[txn_id] = data
    assert len(model) == DEPTH
    assert await trk.full() == 1, "full not asserted at DEPTH live entries"
    await trk.alloc(14, 3)          # caller's contract says don't; must be inert
    await _check_all(trk, model, "after an alloc while full")
    assert await trk.full() == 1

    # Same cycle: release id 1 and allocate id 14, with a slot free. Both
    # must land. (Allocating in the very cycle the LAST slot frees is not
    # supported: `full` is a registered view and the contract is "do not
    # allocate while full", which the adapter's awready gate enforces.)
    await trk.release(12)
    del model[12]
    d = dut
    d.lookup_id.value = 1
    d.release_beat.value = 1
    d.alloc_id.value = 14
    d.alloc_data.value = 3
    d.alloc.value = 1
    await RisingEdge(d.aclk)
    d.release_beat.value = 0
    d.alloc.value = 0
    del model[1]
    model[14] = 3
    await _check_all(trk, model, "after same-cycle release+alloc")

    dut._log.info("axi5_atomic_rr_tracker directed: alloc/lookup/release/full all correct")


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def rr_tracker_random_test(dut):
    """Random allocate/release against a dictionary model, checked every round."""
    trk = Trk(dut)
    await trk.reset()
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    rounds = _ROUNDS.get(level, _ROUNDS['gate'])
    seed = int(os.environ.get('SEED', '0') or 0)
    rng = random.Random(seed)
    dut._log.info(f"random phase: level={level} rounds={rounds} seed={seed}")

    model = {}
    allocs = releases = 0
    for r in range(rounds):
        free_ids = [i for i in range(1 << ID_W) if i not in model]
        can_alloc = len(model) < DEPTH and free_ids
        can_release = bool(model)
        action = rng.choice([a for a, ok in (('alloc', can_alloc),
                                             ('release', can_release),
                                             ('both', can_alloc and can_release))
                             if ok])
        if action in ('alloc', 'both'):
            new_id = rng.choice(free_ids)
            new_data = rng.randrange(1 << DATA_W)
        if action in ('release', 'both'):
            old_id = rng.choice(list(model))

        if action == 'alloc':
            await trk.alloc(new_id, new_data)
            model[new_id] = new_data
            allocs += 1
        elif action == 'release':
            await trk.release(old_id)
            del model[old_id]
            releases += 1
        else:
            d = dut
            d.lookup_id.value = old_id
            d.release_beat.value = 1
            d.alloc_id.value = new_id
            d.alloc_data.value = new_data
            d.alloc.value = 1
            await RisingEdge(d.aclk)
            d.release_beat.value = 0
            d.alloc.value = 0
            del model[old_id]
            model[new_id] = new_data
            allocs += 1
            releases += 1

        assert await trk.full() == (1 if len(model) == DEPTH else 0), \
            f"round {r}: full={await trk.full()} with {len(model)} live"
        await _check_all(trk, model, f"round {r} ({action})")

    dut._log.info(f"axi5_atomic_rr_tracker random: {rounds} rounds, "
                  f"{allocs} allocs / {releases} releases, model matched throughout")


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi5_atomic_rr_tracker(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi5': 'rtl/amba/axi5',
    })

    dut_name = "axi5_atomic_rr_tracker"
    # Sources come from the DUT's filelist rather than a private copy of its
    # dependency list -- a hand-list is invisible to filelist_registry --check.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'rtl/amba/filelists/{dut_name}.f')

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
        testcase="rr_tracker_directed_test,rr_tracker_random_test",
        parameters={'AXI_ID_WIDTH': ID_W, 'DATA_WIDTH': DATA_W, 'DEPTH': DEPTH},
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
    )
