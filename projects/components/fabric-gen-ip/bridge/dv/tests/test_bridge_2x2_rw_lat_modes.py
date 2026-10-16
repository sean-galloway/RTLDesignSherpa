#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): per-port latency modes on bridge_2x2_rw_lat --
# the fix for the fixed, always-registered port boundary (bridge GitHub #119 L7).
#
# Ports: cpu latency="cut_none", dma "cut_ax", ddr "cut_none", sram the default
# "cut_all". Every master/slave pair therefore has its own pipeline depth, and
# each is measured as VALID-to-VALID propagation on all four channels:
#
#   pair          AW  B   AR  R     (registered stages on the path)
#   cpu -> ddr    0   0   0   0     nothing registered: the bridge is wires
#   cpu -> sram   1   1   1   1     sram's wrapper only
#   dma -> ddr    1   0   1   0     dma's AW/AR stage; W/B/R cut both ends
#   dma -> sram   2   1   2   1     dma AW/AR + sram everything
#
# dma -> sram is the fully registered case of bridge_2x2_rw minus dma's cut
# response stages, and its 2-cycle request matches test_bridge_2x2_rw_latency's
# 2/2 baseline -- so the sampler is calibrated against a figure measured
# elsewhere, not only against itself.
#
# Sampling is MID-CYCLE (falling edge). The BFMs drive 200 ps after the rising
# edge, so a ReadOnly sample at the rising edge sees the BFM's new VALID and a
# one-stage register's output in the same sample, and 1 stage reads as 0.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, FallingEdge, ReadOnly
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_rw_lat_tb import Bridge2x2RwLatTB

MASTERS = {0: 'cpu_m_axi', 1: 'dma_m_axi'}
SLAVES = {'ddr': ('ddr_s_axi', 0x00002000), 'sram': ('sram_s_axi', 0x80002000)}
EXPECT = {  # (master, slave): (AW, B, AR, R)
    (0, 'ddr'): (0, 0, 0, 0),
    (0, 'sram'): (1, 1, 1, 1),
    (1, 'ddr'): (1, 0, 1, 0),
    (1, 'sram'): (2, 1, 2, 1),
}


def _hi(sig):
    try:
        return int(sig.value) == 1
    except ValueError:
        return False


async def _first_rise(tb, sigs, cycles=60):
    """Mid-cycle sampler: the cycle index at which each signal is first 1."""
    seen = {}
    for c in range(cycles):
        await FallingEdge(tb.clock)
        await ReadOnly()
        for name, s in sigs.items():
            if name not in seen and _hi(s):
                seen[name] = c
        if len(seen) == len(sigs):
            break
    return seen


async def _measure(tb, dut, m, slave):
    mp, (sp, addr) = MASTERS[m], SLAVES[slave]
    g = lambda p, n: getattr(dut, f"{p}_{n}")

    async def one(kind):
        if kind == 'w':
            sigs = {'m_req': g(mp, 'awvalid'), 's_req': g(sp, 'awvalid'),
                    's_rsp': g(sp, 'bvalid'), 'm_rsp': g(mp, 'bvalid')}
            op = cocotb.start_soon(tb.master_write(m, addr, 0x1A700000 | m))
        else:
            sigs = {'m_req': g(mp, 'arvalid'), 's_req': g(sp, 'arvalid'),
                    's_rsp': g(sp, 'rvalid'), 'm_rsp': g(mp, 'rvalid')}
            op = cocotb.start_soon(tb.master_read(m, addr))
        seen = await _first_rise(tb, sigs)
        await op
        await ClockCycles(tb.clock, 10)   # idle between measurements
        missing = set(sigs) - set(seen)
        assert not missing, f"{mp}->{sp} {kind}: never saw {sorted(missing)}"
        return seen['s_req'] - seen['m_req'], seen['m_rsp'] - seen['s_rsp']

    aw, b = await one('w')
    ar, r = await one('r')
    return aw, b, ar, r


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_lat_modes(dut):
    tb = Bridge2x2RwLatTB(dut)
    await tb.setup_clocks_and_reset()
    tb.set_slave_response_delay(0, 1)
    tb.set_slave_response_delay(1, 1)
    got, bad = {}, []
    for (m, slave), want in EXPECT.items():
        meas = await _measure(tb, dut, m, slave)
        got[(m, slave)] = meas
        tb.log.info(f"LATENCY {MASTERS[m]} -> {slave}: AW/B/AR/R = {meas} (want {want})")
        if meas != want:
            bad.append(f"{MASTERS[m]} -> {slave}: measured AW/B/AR/R {meas}, want {want}")
    assert not bad, "per-port latency modes wrong:\n  " + "\n  ".join(bad)
    tb.assert_compliance()


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_lat_modes(request, test_level):
    """Pytest wrapper: every pair's pipeline depth matches its ports' modes"""
    module, repo_root_, tests_dir, log_dir, _ = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw_lat"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/fabric-gen-ip/bridge/rtl/filelists/bridge_2x2_rw_lat.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    name = f"test_{dut_name}_modes_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_2x2_rw_lat_modes",
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


if __name__ == "__main__":
    pytest.main([__file__, '-v', '-s'])
