#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# HAND-WRITTEN (not generated): CDC master ports (GitHub #119 L2), across clock ratios.
#
# bridge_3x2_rw_mcdc has cpu (rw) and lfsr (rd only) on their own clocks
# (cpu_aclk, lfsr_aclk) behind axi4_cdc_{wr,rd} in their master adapters, dma
# on the fabric clock, a CDC slave (ddr) and a same-clock slave (sram). The
# generated tests run the master clocks at one period; this file sweeps cpu_aclk
# -- master faster than the fabric, equal, and much slower (lfsr_aclk follows
# at +2 ns) -- and for each ratio:
#
#   - cpu and dma stream 16-beat writes then reads into ddr, so cpu's bursts
#     cross twice each way (master CDC, then slave CDC); every word lands and
#     reads back, from both;
#   - lfsr, read-only and on its own clock, reads cpu's ddr and sram data back;
#   - the cpu port's handshakes happen on cpu_aclk edges (a sampler on cpu_aclk
#     sees every W beat cpu sent; one on lfsr_aclk sees every R beat lfsr took);
#   - the sustained rate is set by the slower clock, not the crossing: cpu
#     alone into the same-clock sram moves at least 0.85 W beat per cpu_aclk
#     cycle at its port when the master is the bottleneck, and at least 0.85
#     per aclk cycle at the sram port when the fabric is;
#   - the same-clock dma master beside the CDC ports streams into sram at the
#     same rate with cpu's two-crossing traffic running as without it.

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

from bridge3x2_rw_mcdc_tb import Bridge3x2RwMcdcTB
from bridge_perf_probe import (
    BEATS, Sampler, saturate, hi, write_plan, stream_writes, stream_reads, report,
)

CPU, DMA, LFSR = 0, 1, 2
DDR, SRAM = 0, 1
DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000
FABRIC_NS = 10
BURSTS = {'gate': 6, 'func': 16, 'full': 48}
RATE_FLOOR = 0.85


class PortClockSampler:
    """Counts one channel's handshakes on the port's own clock."""

    def __init__(self, clk, valid, ready):
        self.clk, self.v, self.r = clk, valid, ready
        self.marks = []
        self.cycle = 0

    async def run(self):
        while True:
            await RisingEdge(self.clk)
            self.cycle += 1
            if hi(self.v) and hi(self.r):
                self.marks.append(self.cycle)

    def start(self):
        cocotb.start_soon(self.run())
        return self

    def rate(self):
        if len(self.marks) < 2:
            return len(self.marks), 0, 0.0
        cyc = self.marks[-1] - self.marks[0] + 1
        return len(self.marks), cyc, len(self.marks) / cyc


def check_mem(tb, slave, plan):
    for m, addr, data in plan:
        for k, d in enumerate(data):
            got = tb.slave_mem_read(slave, addr + 4 * k, byte_count=4)
            assert got == d, f"m{m} 0x{addr + 4 * k:08X}: slave {slave} memory 0x{got:08X}, wrote 0x{d:08X}"


@cocotb.test(timeout_time=30000, timeout_unit="ms")
async def cocotb_test_bridge_3x2_rw_mcdc_ratio(dut):
    tb = Bridge3x2RwMcdcTB(dut)
    await tb.setup_clocks_and_reset()
    saturate(tb)
    n = BURSTS[tb.level]
    period = tb.CDC_MASTER_PERIOD_NS
    master_is_bottleneck = period > FABRIC_NS
    tb.log.info(f"CDC master ratio: aclk {FABRIC_NS} ns, cpu_aclk {period} ns, "
                f"lfsr_aclk {period + 2} ns ({'master' if master_is_bottleneck else 'fabric'} bound)")
    errors = []

    # 1. cpu (two crossings) and dma (one, at ddr) into the CDC slave.
    cpu_w = PortClockSampler(dut.cpu_aclk, dut.cpu_m_axi_wvalid, dut.cpu_m_axi_wready).start()
    plan = write_plan(CPU, DDR_BASE, n, 0xA1) + write_plan(DMA, DDR_BASE, n, 0xA2)
    await stream_writes(tb, plan, errors)
    assert not errors, errors[:5]
    check_mem(tb, DDR, plan)
    await stream_reads(tb, plan, errors)
    assert not errors, errors[:5]
    beats, _, _ = cpu_w.rate()
    assert beats == n * BEATS, (
        f"the cpu port (sampled on cpu_aclk) saw {beats} W beats, expected {n * BEATS}: "
        f"beats crossed on the wrong clock or were lost")

    # 2. lfsr, read-only on its own clock, reads cpu's data back from both slaves.
    sram_plan = write_plan(CPU, SRAM_BASE, n, 0xA3)
    await stream_writes(tb, sram_plan, errors)
    assert not errors, errors[:5]
    check_mem(tb, SRAM, sram_plan)
    lfsr_r = PortClockSampler(dut.lfsr_aclk, dut.lfsr_m_axi_rvalid, dut.lfsr_m_axi_rready).start()
    lfsr_plan = [(LFSR, a, d) for (m, a, d) in plan if m == CPU] + \
                [(LFSR, a, d) for (_, a, d) in sram_plan]
    await stream_reads(tb, lfsr_plan, errors)
    assert not errors, errors[:5]
    r_beats, r_cyc, r_rate = lfsr_r.rate()
    assert r_beats == 2 * n * BEATS, (
        f"the lfsr port (sampled on lfsr_aclk) saw {r_beats} R beats, expected {2 * n * BEATS}")
    report(tb, f"mcdc lfsr reads period={period + 2}", beats=r_beats, lfsr_cycles=r_cyc,
           beats_per_lfsr_cycle=r_rate)

    # 3. Rate: cpu alone into the same-clock sram, measured on both clocks.
    cpu_w2 = PortClockSampler(dut.cpu_aclk, dut.cpu_m_axi_wvalid, dut.cpu_m_axi_wready).start()
    sram_w = Sampler(tb, {'sram_w': ('sram_s_axi', 'w')}).start()
    rate_plan = write_plan(CPU, SRAM_BASE, n, 0xA4)
    await stream_writes(tb, rate_plan, errors)
    assert not errors, errors[:5]
    check_mem(tb, SRAM, rate_plan)
    p_beats, p_cyc, p_rate = cpu_w2.rate()
    f_beats, f_cyc, f_rate = sram_w.window_rate('sram_w')
    assert p_beats == f_beats == n * BEATS, (
        f"cpu port saw {p_beats} W beats on cpu_aclk, sram port {f_beats} on aclk, expected {n * BEATS}")
    report(tb, f"mcdc cpu->sram period={period}", beats=p_beats, cpu_cycles=p_cyc,
           beats_per_cpu_cycle=p_rate, aclk_cycles=f_cyc, beats_per_aclk_cycle=f_rate)
    if master_is_bottleneck:
        assert p_rate >= RATE_FLOOR, (
            f"master-bound ({period} ns): {p_rate:.3f} W beats per cpu_aclk cycle, floor {RATE_FLOOR}")
    else:
        assert f_rate >= RATE_FLOOR, (
            f"fabric-bound ({period} ns): {f_rate:.3f} W beats per aclk cycle at sram, floor {RATE_FLOOR}")

    # 4. The same-clock master beside the CDC ports is untouched: dma into
    #    sram alone, then again while cpu streams into ddr through both
    #    crossings -- the rate at sram must not move. (Alone it is the
    #    single-master ceiling, 0.906 at 6 bursts, whatever the clocks: the
    #    same as cpu's own figure at 10 ns.)
    s_alone = Sampler(tb, {'sram_w': ('sram_s_axi', 'w')}).start()
    await stream_writes(tb, write_plan(DMA, SRAM_BASE, n, 0xA5), errors)
    assert not errors, errors[:5]
    b1, c1, r1 = s_alone.window_rate('sram_w')
    s_busy = Sampler(tb, {'sram_w': ('sram_s_axi', 'w')}).start()
    await stream_writes(tb, write_plan(DMA, SRAM_BASE, n, 0xA6) + write_plan(CPU, DDR_BASE, n, 0xA7),
                        errors)
    assert not errors, errors[:5]
    b2, c2, r2 = s_busy.window_rate('sram_w')
    report(tb, "same-clock dma -> sram, alone / beside cpu -> ddr", beats=b2, alone=r1, beside=r2)
    assert b1 == b2 == n * BEATS, f"dma -> sram beats: alone {b1}, beside {b2}, expected {n * BEATS}"
    assert r2 >= r1 - 0.02, f"dma -> sram: {r1:.3f} beats/cycle alone, {r2:.3f} beside CDC traffic"
    tb.assert_compliance()
    tb.log.info(f"GitHub #119 L2 CDC master ratio PASSED at cpu_aclk = {period} ns")


PERIODS = [3, 10, 23]   # master faster, equal, master much slower


@pytest.mark.parametrize("period", PERIODS)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_3x2_rw_mcdc_ratio(request, test_level, period):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_3x2_rw_mcdc"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/fabric-gen-ip/bridge/rtl/filelists/{dut_name}.f')
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
        testcase="cocotb_test_bridge_3x2_rw_mcdc_ratio",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            'BRIDGE_CDC_MASTER_PERIOD_NS': str(period),
            **level_env(test_level),
            **waves['extra_env'],
        },
        plus_args=waves['sim_args'],
        keep_files=True,
    )
