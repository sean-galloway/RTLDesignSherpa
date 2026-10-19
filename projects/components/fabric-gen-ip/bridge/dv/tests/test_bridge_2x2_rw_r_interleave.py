#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): two slaves interleaving R toward two masters
# that share them, on bridge_2x2_rw.
#
# Both slaves are 32-bit, so each master's one width path carries both, and
# its R arbiter chooses between them. cpu and dma both read ddr and sram at
# once, two IDs per (master, slave) and none shared, so all eight bursts
# can be in flight together, and both slaves interleave beats for the two masters.
# With an R arbiter that held a master path through RLAST, ddr could wait
# on dma's path (held mid-burst by sram) while sram waited on cpu's (held by
# ddr): a deadlock. (bridge_4x4_rw_r_interleave covers the width converters;
# its paths have one slave each, so it cannot reach this.) Every word is
# checked, and both slaves must SEE interleaving.

import os
import random
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_rw_tb import Bridge2x2RwTB

CPU, DMA = 0, 1                     # masters, 32b
DDR, SRAM = 0, 1                    # slaves, 32b
SLAVE_PINS = {DDR: 'ddr_s_axi_', SRAM: 'sram_s_axi_'}
MBITS = {CPU: 32, DMA: 32}
ROUNDS = {'gate': 2, 'func': 6, 'full': 16}


class InterleaveCount:
    """Counts, per slave, R beats whose ID differs from the previous beat's
    while that beat's burst had not ended: beat-level interleaving."""

    def __init__(self, tb, slaves):
        self.tb = tb
        self.pins = {s: SLAVE_PINS[s] for s in slaves}
        self.count = {s: 0 for s in slaves}
        self.beats = {s: 0 for s in slaves}
        self.ars = 0
        self._open = {s: None for s in slaves}   # ID of the burst in progress
        self._task = cocotb.start_soon(self._run())

    def _sig(self, s, name):
        return getattr(self.tb.dut, f"{self.pins[s]}{name}")

    async def _run(self):
        while True:
            await RisingEdge(self.tb.clock)
            for s in self.pins:
                if int(self._sig(s, 'arvalid').value) and int(self._sig(s, 'arready').value):
                    self.ars += 1
                if int(self._sig(s, 'rvalid').value) and int(self._sig(s, 'rready').value):
                    rid = int(self._sig(s, 'rid').value)
                    self.beats[s] += 1
                    if self._open[s] is not None and rid != self._open[s]:
                        self.count[s] += 1
                    self._open[s] = None if int(self._sig(s, 'rlast').value) else rid

    def stop(self):
        self._task.cancel()


async def _wait(tb, futs, what):
    for _ in range(40000):
        if all(f.done() for f in futs):
            for f in futs:
                f.result()
            return
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"{what}: {sum(f.done() for f in futs)}/{len(futs)} reads completed "
                         f"(an R path waiting on another would hang here)")


async def _preload(tb, rng, m, s, region, beats, ids):
    """Write one burst per ID through master m, return [(addr, words, id)]."""
    size = tb._natural_arsize(m)
    mbytes = MBITS[m] // 8
    _, sbase, _, _ = tb.slave_info[s]
    plan = []
    for k, rid in enumerate(ids):
        addr = sbase + region + k * 0x100
        plan.append((addr, [rng.getrandbits(MBITS[m]) for _ in range(beats)], rid))
    futs = [cocotb.start_soon(tb.master_wr[m].write_transaction(a, d, id=rid, size=size))
            for a, d, rid in plan]
    await _wait(tb, futs, f"preload m{m}->s{s}")
    return plan


GATHER_CYCLES = 400


async def _gathered(tb, cnt, slaves, n_ar, launch):
    """Launch a case's reads and start every slave burst on one cycle, so
    the bursts are waiting together: only bursts waiting together can
    interleave. The master BFM spaces its ARs by a seeded random delay
    and does not offer one until the previous is accepted, so neither a
    fixed response delay (it counts from each AR's own arrival) nor a
    stalled AR ready (the ARs wait in the BFM, not the fabric) lines the
    bursts up; SEED=7 and 80451 saw no interleaving at all. The slave BFM
    reads response_delay_cycles when an AR arrives, so counting it down
    every cycle makes every burst start at the same release cycle."""
    jobs = launch()
    for k in range(GATHER_CYCLES):
        for s in slaves:
            tb.slave_rd[s].response_delay_cycles = GATHER_CYCLES - k
        await RisingEdge(tb.clock)
    for s in slaves:
        tb.slave_rd[s].response_delay_cycles = 1
    assert cnt.ars >= n_ar, (f"only {cnt.ars} of {n_ar} ARs reached the slaves in "
                             f"{GATHER_CYCLES} cycles; widen GATHER_CYCLES")
    return jobs


def _reads(tb, m, plan, beats):
    size = tb._natural_arsize(m)
    return [(cocotb.start_soon(tb.master_rd[m].read_transaction(a, burst_len=beats, id=rid, size=size)),
             a, d) for a, d, rid in plan]


async def _check(tb, jobs, what):
    await _wait(tb, [f for f, _a, _d in jobs], what)
    for f, a, d in jobs:
        assert list(f.result()) == d, f"{what}: read 0x{a:08X} returned other data"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_r_interleave(dut):
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    assert tb.R_INTERLEAVE, "the slave BFMs must interleave R (BRIDGE_R_INTERLEAVE=1)"
    rng = random.Random(int(os.environ.get('SEED', '1')))
    for r in range(ROUNDS[tb.level]):
        cnt = InterleaveCount(tb, [DDR, SRAM])
        plans = []
        for m in (CPU, DMA):
            for s in (DDR, SRAM):
                region = 0x800 * r + 0x200 * (2 * m + s)
                # distinct IDs per (master, slave): a same-ID read to a
                # different slave waits for the first (ar_gate_ok), which
                # would keep the two slaves' bursts from ever overlapping
                ids = (4 * m + 2 * s + 1, 4 * m + 2 * s + 2)
                plans.append((m, await _preload(tb, rng, m, s, region, 8, ids)))
        jobs = await _gathered(tb, cnt, [DDR, SRAM], 2 * len(plans), lambda: [
            j for m, plan in plans for j in _reads(tb, m, plan, 8)])
        await _check(tb, jobs, f"cross round {r}")
        cnt.stop()
        tb.log.info(f"cross round {r}: ddr {cnt.count[DDR]} / sram {cnt.count[SRAM]} interleave events")
        assert cnt.count[DDR] > 0 and cnt.count[SRAM] > 0, \
            "a slave never interleaved; the test proved nothing"
    tb.assert_compliance()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_r_interleave(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}_checkers.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_r_interleave_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"
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
        testcase="cocotb_test_bridge_2x2_rw_r_interleave",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
        plus_args=waves['sim_args'],
        keep_files=True,
    )
