#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): AXI5 sideband ACROSS A WIDTH CONVERTER.
#
# bridge_1x2_rd_axi5w: a 32b AXI5 master reads a 64b AXI4 slave (upsize
# converter; nsaid/trace/unique terminate with a generation-time warning)
# and a 32b AXI5 slave (native). Until this fixture the droppable-sideband-
# across-a-converter path was a warning nobody simulated. The AXI5 BFM
# drives the sideband per transaction:
#   - structural: the 64b AXI4 slave has no sideband pins -- that is where the
#     drop is proved;
#   - reads through the converter return the seeded data AND the echoed
#     trace=1: sideband cannot traverse the dwidth converter, but the adapter
#     echoes the request's trace at the port (BRIDGE-012), so the master's
#     promise survives a path that cannot carry the bit at all;
#   - reads into the AXI5 slave show the driven nsaid/trace/unique at its AR
#     handshake and echo trace=1 on R;
#   - the AXI5 compliance checker on the master port reports zero violations.
# Depth (TEST_LEVEL): sideband_beats reads per slave.

import os
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

from projects.components.bridge.dv.tbclasses.bridge1x2_rd_axi5w_tb import Bridge1x2RdAxi5wTB

ARNSAID = 0xC
DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000


class ArSampler:
    def __init__(self, dut, clock):
        self.dut, self.clock, self.ar = dut, clock, []

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clock)
            if int(d.sram_rd_axi_arvalid.value) and int(d.sram_rd_axi_arready.value):
                self.ar.append({'nsaid': int(d.sram_rd_axi_arnsaid.value),
                                'trace': int(d.sram_rd_axi_artrace.value),
                                'unique': int(d.sram_rd_axi_arunique.value)})


@cocotb.test(timeout_time=4000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_axi5w_sideband(dut):
    """AXI5 sideband into a width-converted AXI4 slave (drops) and a native AXI5 slave."""
    tb = Bridge1x2RdAxi5wTB(dut)
    for pin in ('ddr_rd_axi_arnsaid', 'ddr_rd_axi_artrace', 'ddr_rd_axi_arunique', 'ddr_rd_axi_rtrace'):
        assert not hasattr(dut, pin), f"64b AXI4 slave grew a sideband pin: {pin}"
    await tb.setup_clocks_and_reset()
    sampler = ArSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    n = tb.level_cfg['sideband_beats']
    tb.log.info("=" * 80)
    tb.log.info(f"AXI5 sideband across the 32->64 converter and the native path: {n} reads each (level={tb.level})")
    tb.log.info("=" * 80)

    def offsets(slave_idx):
        offs = [0x100, 0x1F4, 0x0FC]
        while len(offs) < n:
            o = tb.rng.randrange(0, tb._slave_mem_bytes(slave_idx), 4)
            if o not in offs:
                offs.append(o)
        return offs[:max(n, 3)]

    # ---- converter path: 64b AXI4 slave. Sideband terminates; data must not,
    # and neither must the port's trace promise.
    for off in offsets(0):
        addr = DDR_BASE + off
        expected = tb.slave_mem_read(0, addr, master_idx=0)
        resp = await tb.master_rd[0].read_transaction(addr, size=2, nsaid=ARNSAID, trace=1, unique=1)
        assert resp[0]['data'] == expected, (
            f"converter path read @0x{addr:08x}: 0x{resp[0]['data']:08x} != 0x{expected:08x}")
        assert resp[0].get('trace', 0) == 1, (
            f"rtrace not echoed across the converter: got {resp[0].get('trace')} "
            f"(BRIDGE-012 -- the bit cannot traverse the converter, so the adapter "
            f"echoes the request's at the port)")
    # And the echo must FOLLOW the request: an untraced read comes back untraced.
    addr = DDR_BASE + offsets(0)[0]
    resp = await tb.master_rd[0].read_transaction(addr, size=2, nsaid=ARNSAID, trace=0, unique=1)
    assert resp[0].get('trace', 1) == 0, (
        f"rtrace={resp[0].get('trace')} for an UNTRACED read -- the echo must follow "
        f"the request, not assert unconditionally")
    tb.log.info(f"  converter path OK: {n} reads, data intact, rtrace echoed (and 0 when unasked)")

    # ---- native path: 32b AXI5 slave. Sideband arrives and trace echoes.
    before = len(sampler.ar)
    for off in offsets(1):
        addr = SRAM_BASE + off
        expected = tb.slave_mem_read(1, addr, master_idx=0)
        resp = await tb.master_rd[0].read_transaction(addr, size=2, nsaid=ARNSAID, trace=1, unique=1)
        assert resp[0]['data'] == expected
        assert resp[0].get('trace', 0) == 1, f"rtrace not echoed from the AXI5 slave: {resp[0]}"
    await ClockCycles(tb.clock, 10)
    seen = sampler.ar[before:]
    assert len(seen) >= n, f"expected >= {n} sram AR handshakes, saw {len(seen)}"
    for i, s in enumerate(seen):
        assert s == {'nsaid': ARNSAID, 'trace': 1, 'unique': 1}, f"sram AR sideband sample {i}: {s}"
    tb.log.info(f"  native path OK: {len(seen)} AR handshakes carried nsaid/trace/unique, rtrace echoed")

    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("AXI5 sideband-across-converter test PASSED")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest wrapper
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rd_axi5w_sideband(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_rd_axi5w"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rd_axi5w.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_sideband_{test_level}_{reg_level}"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    extra_args = ['--assert', '--coverage'] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
        **level_env(test_level),
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_rd_axi5w_sideband",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
