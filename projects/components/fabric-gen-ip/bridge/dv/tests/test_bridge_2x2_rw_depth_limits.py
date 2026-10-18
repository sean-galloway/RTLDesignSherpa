#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): configurable outstanding limits on
# bridge_2x2_rw_depth -- the fix for the fixed 16-deep trackers
# (bridge GitHub #119 L5).
#
# The fixture sets [bridge].max_outstanding = 4 (dma and sram inherit it),
# cpu = 64 and ddr = 32. Both directions of the change are measured on the
# trackers themselves, sampled every cycle:
#
#   master_limit -- dma offers 12 writes and 12 reads at once to a slow ddr.
#                   Its adapter must hold exactly 4 in flight per direction:
#                   reaching 4 shows the limit is not below the setting,
#                   never exceeding it shows it holds.
#   slave_deep   -- cpu offers 40 writes and 40 reads at once to a slow ddr.
#                   ddr's tracker must fill to exactly 32 -- past the old fixed
#                   16 -- and every write must land, every read return the
#                   seeded word.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, ReadOnly, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_rw_depth_tb import Bridge2x2RwDepthTB

DDR = 0
SLOW = 120  # cycles ddr holds each response, so requests pile up
# slave_deep needs the hold to outlast its issue phase: 32 AWs must reach the
# CAM before the first B frees an entry. Measured on the CAM's own handshakes
# (seed base 184276959): AW #32 lands at cycle ~130-200; at a 120-cycle hold
# the first B left at 149, before AW #32 (164), and the write CAM peaked at
# 31 -- which is how this failed in the regression. The test checks that
# precondition itself, on RTL-driven signals only: the BFMs drive their side
# on the falling edge, so a one-cycle BVALID/AWREADY pulse is invisible to a
# ReadOnly sampler.
# The ceiling is the master BFM's patience: it abandons an AW after 1000
# cycles without AWREADY, and the 33rd write waits for the first B (a
# 2000-cycle hold tripped exactly that). 900 sits well inside both bounds.
DEEP_SLOW = 900


def _int(sig):
    """Signal value as int; 0 while it still reads X (before first use)."""
    try:
        return int(sig.value)
    except ValueError:
        return 0


async def _peaks(tb, probes, peaks):
    """ONE sampler for every counter -- several ReadOnly() watchers drop
    samples (see test_bridge_2x2_rw_tracking)."""
    while True:
        await RisingEdge(tb.clock)
        await ReadOnly()
        for name, sig in probes.items():
            peaks[name] = max(peaks.get(name, 0), _int(sig))


async def _offer(tb, master, n, base, data_tag):
    """n concurrent writes then n concurrent reads of the same words from
    `master`; returns (writes, read tasks). IDs cycle 0..7 so the per-ID table
    is never what limits issue."""
    size = tb._natural_arsize(master)
    words = [(base + 4 * i, data_tag | i, i % 8) for i in range(n)]
    wr = [cocotb.start_soon(tb.master_write(master, a, d, txn_id=t)) for a, d, t in words]
    rd = [cocotb.start_soon(tb.master_rd[master].single_read(a + 0x1000, id=t, size=size))
          for a, _d, t in words]
    return words, wr, rd


async def _wait(tb, tasks, cycles):
    for _ in range(cycles // 10):
        if all(t.done() for t in tasks):
            return
        await ClockCycles(tb.clock, 10)
    raise AssertionError(f"{sum(not t.done() for t in tasks)}/{len(tasks)} operations "
                         f"never completed in {cycles} cycles")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_depth_master_limit(dut):
    tb = Bridge2x2RwDepthTB(dut)
    await tb.setup_clocks_and_reset()
    tb.set_slave_response_delay(DDR, SLOW)
    peaks = {}
    cocotb.start_soon(_peaks(tb, {
        'aw': dut.u_dma_adapter.aw_out_cnt,
        'ar': dut.u_dma_adapter.ar_out_cnt}, peaks))

    words, wr, rd = await _offer(tb, 1, 12, 0x00002000, 0xD4A00000)
    await _wait(tb, wr + rd, 400 * SLOW)

    tb.log.info(f"dma (max_outstanding 4) peak in flight: {peaks}")
    for ch in ('aw', 'ar'):
        assert peaks[ch] == 4, (
            f"dma {ch.upper()} peak in flight {peaks[ch]}, want exactly 4: "
            f"{'the limit did not hold' if peaks[ch] > 4 else 'the limit is tighter than configured'}")
    for a, d, _t in words:
        assert tb.slave_mem_read(DDR, a, master_idx=1) == d, f"write lost at 0x{a:08x}"
    tb.assert_compliance()  # a BFM that gave up on a handshake fails here


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_depth_slave_deep(dut):
    tb = Bridge2x2RwDepthTB(dut)
    await tb.setup_clocks_and_reset()
    tb.set_slave_response_delay(DDR, DEEP_SLOW)
    cam = dut.u_ddr_adapter
    peaks = {}
    # ddr tracks by ID: its outstanding counters (bridge W12; a bridge_cam
    # before 2026-10-18).
    cocotb.start_soon(_peaks(tb, {'wr': cam.wr_out_cnt,
                                  'rd': cam.rd_out_cnt}, peaks))
    # When did ddr's tracker free its first slot, and how many had it taken by then?
    # The tracker can only reach 32 if 32 AWs arrive before the first B frees one.
    timing = {'cyc': 0, 'aw': [], 'b0': None}

    async def _timing():
        # The tracker's own count / free handshakes (adapter fabric side,
        # both ends RTL-driven), not the slave pins.
        # Sampled AT the edge (no ReadOnly): the values read there are the
        # ones the edge captured. After ReadOnly they are the next cycle's,
        # and a one-cycle handshake is gone -- missed outright once ddr's
        # AWREADY came straight from the slave pin (arbitration at the pins).
        while True:
            await RisingEdge(tb.clock)
            timing['cyc'] += 1
            if _int(cam.xbar_ddr_axi_awvalid) and _int(cam.xbar_ddr_axi_awready):
                timing['aw'].append(timing['cyc'])
            if timing['b0'] is None and _int(cam.xbar_ddr_axi_bvalid) and _int(cam.xbar_ddr_axi_bready):
                timing['b0'] = timing['cyc']
    cocotb.start_soon(_timing())

    words, wr, rd = await _offer(tb, 0, 40, 0x00004000, 0xC0D00000)
    await _wait(tb, wr + rd, 400 * DEEP_SLOW)

    tb.log.info(f"ddr (max_outstanding 32) peak tracker occupancy: {peaks}")
    aw_before_b0 = sum(1 for c in timing['aw'] if c < (timing['b0'] or 1 << 30))
    tb.log.info(f"ddr: first B at cycle {timing['b0']}, {aw_before_b0} AWs accepted before it; "
                f"AW #32 at cycle {timing['aw'][31] if len(timing['aw']) > 31 else None}")
    # Stimulus check first: 32 AWs offered before any B could free a slot,
    # or the occupancy assert below would measure the stimulus, not the depth.
    assert len(timing['aw']) > 31 and timing['aw'][31] < (timing['b0'] or 1 << 30), (
        f"stimulus too weak: AW #32 did not reach ddr before its first B "
        f"(cycle {timing['b0']}); raise DEEP_SLOW")
    for ch in ('wr', 'rd'):
        assert peaks[ch] == 32, (
            f"ddr {ch} tracker peak {peaks[ch]}, want exactly 32: "
            f"{'over the configured depth' if peaks[ch] > 32 else 'the tracker never got past ' + str(peaks[ch])}")
    for a, d, _t in words:
        assert tb.slave_mem_read(DDR, a, master_idx=0) == d, f"write lost at 0x{a:08x}"
    for (a, _d, _t), t in zip(words, rd):
        want = tb.slave_mem_read(DDR, a + 0x1000, master_idx=0)
        assert t.result() == want, (
            f"read at 0x{a + 0x1000:08x} returned 0x{t.result():x}, want 0x{want:x}")
    tb.assert_compliance()  # e.g. an AW abandoned after the BFM's 1000-cycle wait


# ============================================================================
# Pytest wrappers
# ============================================================================

def _run(testcase, test_level):
    module, repo_root_, tests_dir, log_dir, _ = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_depth"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/fabric-gen-ip/bridge/rtl/filelists/bridge_2x2_rw_depth.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    short = testcase.replace("cocotb_test_bridge_2x2_rw_depth_", "")
    name = f"test_{dut_name}_{short}_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': os.path.join(log_dir, f'{name}.log'),
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_depth_master_limit(request, test_level):
    """Pytest wrapper: a master holds exactly its max_outstanding in flight"""
    _run("cocotb_test_bridge_2x2_rw_depth_master_limit", test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_depth_slave_deep(request, test_level):
    """Pytest wrapper: a slave tracker deeper than 16 fills to its depth"""
    _run("cocotb_test_bridge_2x2_rw_depth_slave_deep", test_level)


if __name__ == "__main__":
    pytest.main([__file__, '-v', '-s'])
