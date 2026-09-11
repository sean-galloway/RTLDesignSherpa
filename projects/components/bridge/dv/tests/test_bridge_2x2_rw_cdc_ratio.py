#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-017 CDC slave port, across clock ratios.
#
# bridge_2x2_rw_cdc has ddr on its own clock (ddr_aclk) behind axi4_cdc_{wr,rd}
# and sram on the fabric clock. The generated tests run ddr_aclk at one
# period; this file sweeps it -- slave faster than the fabric, equal, and much
# slower -- and for each ratio streams 16-beat writes then reads from BOTH
# masters into ddr, then checks:
#
#   - every burst completes and every word lands / reads back (the crossing
#     neither drops nor reorders under load, from either master);
#   - the ddr port's handshakes happen on ddr_aclk edges, not aclk edges (a
#     sampler on ddr_aclk sees every W beat the requesters sent);
#   - the sustained W rate at the ddr port is bounded by the slower clock and
#     not by the crossing: at least 0.85 beat per ddr_aclk cycle when the slave
#     is the bottleneck, at least 0.85 beat per aclk cycle when the fabric is;
#   - the same-clock sram port is untouched by the CDC neighbour: a stream to
#     it still runs at the fabric's rate.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from projects.components.bridge.dv.tbclasses.bridge2x2_rw_cdc_tb import Bridge2x2RwCdcTB
from projects.components.bridge.dv.tbclasses.bridge_perf_probe import (
    BEATS, Sampler, saturate, hi, write_plan, stream_writes, stream_reads, report,
)

CPU, DMA = 0, 1
DDR, SRAM = 0, 1
DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000
FABRIC_NS = 10
BURSTS = {'gate': 6, 'func': 16, 'full': 48}
RATE_FLOOR = 0.85


class SlaveClockSampler:
    """Counts ddr-port W handshakes on ddr_aclk edges (the port's own clock)."""

    def __init__(self, tb):
        self.tb = tb
        self.clk = tb.dut.ddr_aclk
        self.v = tb.dut.ddr_s_axi_wvalid
        self.r = tb.dut.ddr_s_axi_wready
        self.marks = []
        self.cycle = 0

    async def run(self):
        while True:
            await RisingEdge(self.clk)
            self.cycle += 1
            if hi(self.v) and hi(self.r):
                self.marks.append(self.cycle)

    def rate(self):
        if len(self.marks) < 2:
            return len(self.marks), 0, 0.0
        cyc = self.marks[-1] - self.marks[0] + 1
        return len(self.marks), cyc, len(self.marks) / cyc


@cocotb.test(timeout_time=30000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_cdc_ratio(dut):
    tb = Bridge2x2RwCdcTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    period = tb.CDC_PERIOD_NS
    slave_is_bottleneck = period > FABRIC_NS
    tb.log.info(f"CDC ratio: aclk {FABRIC_NS} ns, ddr_aclk {period} ns ({'slave' if slave_is_bottleneck else 'fabric'} bound)")

    port = SlaveClockSampler(tb)
    cocotb.start_soon(port.run())
    # The fabric-side rate is measured where the fabric clock is the clock:
    # the two masters' W channels on aclk. Sampling the ddr port itself on
    # aclk would miss most handshakes once the port clock is faster than
    # aclk (a 3 ns handshake seen every 10 ns), and read 0.67 for a port
    # that was actually streaming.
    fab = Sampler(tb, {'cpu_w': ('cpu_m_axi', 'w'), 'dma_w': ('dma_m_axi', 'w')}).start()
    errors = []
    plan = write_plan(CPU, DDR_BASE, n, 0xCD) + write_plan(DMA, DDR_BASE, n, 0xCE)
    await stream_writes(tb, plan, errors)
    assert not errors, errors[:5]
    for m, addr, data in plan:
        for k, d in enumerate(data):
            got = tb.slave_mem_read(DDR, addr + 4 * k, byte_count=4)
            assert got == d, f"m{m} 0x{addr + 4 * k:08X}: ddr memory 0x{got:08X}, wrote 0x{d:08X}"
    await stream_reads(tb, plan, errors)
    assert not errors, errors[:5]

    beats, cyc, rate = port.rate()
    assert beats == 2 * n * BEATS, (
        f"the ddr port (sampled on ddr_aclk) saw {beats} W beats, expected {2 * n * BEATS}: "
        f"beats crossed on the wrong clock or were lost")
    fab_marks = sorted(fab.marks['cpu_w'] + fab.marks['dma_w'])
    aclk_beats = len(fab_marks)
    fab_cycles = (fab_marks[-1] - fab_marks[0] + 1) if aclk_beats > 1 else 0
    fab_rate = aclk_beats / fab_cycles if fab_cycles else 0.0
    assert aclk_beats == 2 * n * BEATS, f"the masters handed over {aclk_beats} W beats on aclk, expected {2 * n * BEATS}"
    report(tb, f"cdc ddr period={period}", beats=beats, ddr_cycles=cyc, beats_per_ddr_cycle=rate,
           beats_per_aclk_cycle=fab_rate)
    if slave_is_bottleneck:
        assert rate >= RATE_FLOOR, (
            f"slave-bound ({period} ns): {rate:.3f} W beats per ddr_aclk cycle at the port, floor {RATE_FLOOR}")
    else:
        assert fab_rate >= RATE_FLOOR, (
            f"fabric-bound ({period} ns): {fab_rate:.3f} W beats per aclk cycle at the port, floor {RATE_FLOOR}")

    # The same-clock neighbour is untouched.
    s2 = Sampler(tb, {'sram_w': ('sram_s_axi', 'w')}).start()
    plan2 = write_plan(CPU, SRAM_BASE, n, 0xCF) + write_plan(DMA, SRAM_BASE, n, 0xD0)
    await stream_writes(tb, plan2, errors)
    assert not errors, errors[:5]
    b2, c2, r2 = s2.window_rate('sram_w')
    report(tb, "same-clock sram beside the CDC port", beats=b2, cycles=c2, beats_per_cycle=r2)
    assert b2 == 2 * n * BEATS and r2 >= 0.95, f"sram: {r2:.3f} beats/cycle beside a CDC port"
    tb.log.info(f"BRIDGE-017 CDC ratio PASSED at ddr_aclk = {period} ns")


PERIODS = [3, 10, 23]   # slave faster, equal, slave much slower


@pytest.mark.parametrize("period", PERIODS)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_cdc_ratio(request, test_level, period):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_cdc"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/bridge/rtl/filelists/{dut_name}.f')
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_ratio_p{period}_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_2x2_rw_cdc_ratio",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            'BRIDGE_CDC_PERIOD_NS': str(period),
            **level_env(test_level),
            **waves['extra_env'],
        },
        plus_args=waves['sim_args'],
        keep_files=True,
    )
