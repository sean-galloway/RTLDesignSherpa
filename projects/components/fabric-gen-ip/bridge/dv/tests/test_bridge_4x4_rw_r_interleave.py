#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): read data interleaved across IDs, on
# bridge_4x4_rw.
#
# AXI4 lets a slave interleave R beats of different ARIDs (beats of one ID
# stay in order). The slave BFMs here do (interleave_r, on by default in the
# generated TB): one beat at a time, round-robin across the bursts waiting.
# Three cases, each with several bursts in flight at once:
#
#   slice  cpu 64b reads sram 128b with three IDs: the width converter cuts
#          interleaved wide beats per ID.
#   pack   gpu 256b reads ddr0 64b with three IDs: the converter folds
#          interleaved narrow beats into wide beats per ID.
#   cross  cpu and gpu both read ddr0 and periph at once. Each slave
#          interleaves beats for the two masters. With an R arbiter that held
#          a master path through RLAST, two such slaves could each wait on
#          the other's held path.
#
# Every word is checked, and each case must SEE interleaving at the slave
# pins (a beat of another ID before the current burst's RLAST): a pass with
# none would prove nothing.

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

from bridge4x4_rw_tb import Bridge4x4RwTB

CPU, GPU = 0, 3                     # master indices (64b, 256b)
PERIPH, DDR0, SRAM = 0, 1, 2        # slave indices (32b, 64b, 128b)
SLAVE_PINS = {PERIPH: 'periph_slave_axi_', DDR0: 'ddr0_slave_axi_', SRAM: 'sram_slave_axi_'}
MBITS = {CPU: 64, GPU: 256}
ROUNDS = {'gate': 1, 'func': 3, 'full': 8}


class InterleaveCount:
    """Counts, per slave, R beats whose ID differs from the previous beat's
    while that beat's burst had not ended: beat-level interleaving."""

    def __init__(self, tb, slaves):
        self.tb = tb
        self.pins = {s: SLAVE_PINS[s] for s in slaves}
        self.count = {s: 0 for s in slaves}
        self.beats = {s: 0 for s in slaves}
        self._open = {s: None for s in slaves}   # ID of the burst in progress
        self._task = cocotb.start_soon(self._run())

    def _sig(self, s, name):
        return getattr(self.tb.dut, f"{self.pins[s]}{name}")

    async def _run(self):
        while True:
            await RisingEdge(self.tb.clock)
            for s in self.pins:
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


def _slow(tb, slaves, cycles):
    """Hold each slave's first R beat back long enough that every AR of the
    case is waiting at once: only bursts waiting together can interleave."""
    for s in slaves:
        tb.slave_rd[s].response_delay_cycles = cycles


def _reads(tb, m, plan, beats):
    size = tb._natural_arsize(m)
    return [(cocotb.start_soon(tb.master_rd[m].read_transaction(a, burst_len=beats, id=rid, size=size)),
             a, d) for a, d, rid in plan]


async def _check(tb, jobs, what):
    await _wait(tb, [f for f, _a, _d in jobs], what)
    for f, a, d in jobs:
        assert list(f.result()) == d, f"{what}: read 0x{a:08X} returned other data"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_bridge_4x4_rw_r_interleave(dut):
    tb = Bridge4x4RwTB(dut)
    await tb.setup_clocks_and_reset()
    assert tb.R_INTERLEAVE, "the slave BFMs must interleave R (BRIDGE_R_INTERLEAVE=1)"
    rng = random.Random(int(os.environ.get('SEED', '1')))
    rounds = ROUNDS[tb.level]
    ids = (1, 2, 3)

    for r in range(rounds):
        region = 0x1000 * r          # the slave memory models hold 64 KB

        # slice: cpu 64b <- sram 128b, three IDs, 8 cpu beats each
        cnt = InterleaveCount(tb, [SRAM])
        plan = await _preload(tb, rng, CPU, SRAM, region, 8, ids)
        _slow(tb, [SRAM], 40)
        await _check(tb, _reads(tb, CPU, plan, 8), f"slice round {r}")
        cnt.stop()
        tb.log.info(f"slice round {r}: {cnt.count[SRAM]} interleave events in {cnt.beats[SRAM]} sram R beats")
        assert cnt.count[SRAM] > 0, "slice: the sram slave never interleaved; the test proved nothing"

        # pack: gpu 256b <- ddr0 64b, three IDs, 4 gpu beats (16 ddr0 beats) each
        cnt = InterleaveCount(tb, [DDR0])
        plan = await _preload(tb, rng, GPU, DDR0, region + 0x400, 4, ids)
        _slow(tb, [DDR0], 40)
        await _check(tb, _reads(tb, GPU, plan, 4), f"pack round {r}")
        cnt.stop()
        tb.log.info(f"pack round {r}: {cnt.count[DDR0]} interleave events in {cnt.beats[DDR0]} ddr0 R beats")
        assert cnt.count[DDR0] > 0, "pack: the ddr0 slave never interleaved; the test proved nothing"

        # cross: cpu and gpu both read ddr0 and periph at once, two IDs each
        cnt = InterleaveCount(tb, [DDR0, PERIPH])
        plans = []
        for m, beats in ((CPU, 8), (GPU, 2)):
            for s, off in ((DDR0, 0x800), (PERIPH, 0x800)):
                plans.append((m, beats, await _preload(tb, rng, m, s, region + off + 0x200 * m, beats, (4, 5))))
        _slow(tb, [DDR0, PERIPH], 40)
        jobs = [j for m, beats, plan in plans for j in _reads(tb, m, plan, beats)]
        await _check(tb, jobs, f"cross round {r}")
        cnt.stop()
        tb.log.info(f"cross round {r}: ddr0 {cnt.count[DDR0]} / periph {cnt.count[PERIPH]} interleave events")
        assert cnt.count[DDR0] > 0 and cnt.count[PERIPH] > 0, \
            "cross: a slave never interleaved; the test proved nothing"
        _slow(tb, [DDR0, PERIPH, SRAM], 1)

    tb.assert_compliance()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_4x4_rw_r_interleave(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_4x4_rw"
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
        testcase="cocotb_test_bridge_4x4_rw_r_interleave",
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
