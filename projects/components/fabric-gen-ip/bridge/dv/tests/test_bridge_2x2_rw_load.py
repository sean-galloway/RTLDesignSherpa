#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): accepted throughput and latency against
# offered load (GitHub #119 L4), on bridge_2x2_rw.
#
# Open loop: a master starts one 4-beat read every `gap` cycles, whether or
# not earlier ones have finished, for a fixed number of reads. Offered load
# is 4/gap beats per cycle per master. For each point: accepted beats per
# cycle at the ddr port over the busy window, and the per-read latency from
# the call to the last beat (so it includes queueing in the requester).
#   alone:     cpu -> ddr
#   contended: cpu and dma -> ddr, each at the same gap (offered 8/gap)
# Asserted: accepted >= 85% of min(offered, 1.0); below saturation the mean
# latency stays within 4 cycles of the lightest point (no queueing yet).

import os
import statistics
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
from bridge_perf_probe import Sampler, saturate, report

CPU, DMA = 0, 1
DDR_BASE = 0x0000_0000
BEATS = 4
GAPS = [32, 16, 8, 6, 5, 4, 3, 2]
NREADS = {'gate': 24, 'func': 48, 'full': 96}


class Clock:
    def __init__(self, tb):
        self.tb, self.now = tb, 0

    async def run(self):
        while True:
            await RisingEdge(self.tb.clock)
            self.now += 1


async def open_loop(tb, clk, masters, gap, n):
    lats, futs = [], []

    async def one(m, addr, i):
        t0 = clk.now
        await tb.master_rd[m].read_transaction(addr, burst_len=BEATS, id=i % 16, size=2)
        lats.append(clk.now - t0)

    for i in range(n):
        for m in masters:
            futs.append(cocotb.start_soon(one(m, DDR_BASE + 0x8000 * m + (i % 64) * BEATS * 4, i)))
        await ClockCycles(tb.clock, gap)
    for _ in range(20000):
        if all(f.done() for f in futs):
            break
        await ClockCycles(tb.clock, 5)
    assert all(f.done() for f in futs), f"gap {gap}: reads did not complete"
    for f in futs:
        f.result()
    return lats


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_load(dut):
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    clk = Clock(tb)
    cocotb.start_soon(clk.run())
    n = NREADS[tb.level]
    table = []
    for label, masters in (("alone", [CPU]), ("contended", [CPU, DMA])):
        base_lat = None
        for gap in GAPS:
            smp = Sampler(tb, {'r': ('ddr_s_axi', 'r')}).start()
            lats = await open_loop(tb, clk, masters, gap, n)
            beats, cycles, acc = smp.window_rate('r')
            offered = len(masters) * BEATS / gap
            mean, p95 = statistics.fmean(lats), sorted(lats)[int(0.95 * (len(lats) - 1))]
            report(tb, f"load {label} gap={gap}", offered=offered, accepted=acc,
                   mean_latency=mean, p95_latency=p95)
            table.append((label, gap, offered, acc, mean, p95))
            assert beats == n * len(masters) * BEATS, f"{label} gap {gap}: {beats} R beats at ddr"
            assert acc >= 0.85 * min(offered, 1.0), (
                f"{label} gap {gap}: accepted {acc:.3f} beats/cycle for {offered:.3f} offered")
            if base_lat is None:
                base_lat = mean
            if offered <= 0.5:
                assert mean <= base_lat + 4, (
                    f"{label} gap {gap}: mean latency {mean:.1f} at {offered:.2f} offered, "
                    f"{base_lat:.1f} at the lightest load")
            await ClockCycles(tb.clock, 50)
    tb.log.info("| traffic | gap | offered | accepted | mean latency | p95 latency |")
    for r in table:
        tb.log.info("| {} | {} | {:.3f} | {:.3f} | {:.1f} | {} |".format(*r))
    tb.assert_compliance()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_load(request, test_level):
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
    test_name_plus_params = f"test_{dut_name}_load_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_rw_load",
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
