#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-2 slice 2 sign-off test,
# write channel — including connectivity-gated POISON.
#
# The AXI5 master BFM drives awtrace=1 / wpoison=1 per transaction (no pin
# poking since 2026-09-09):
#   - writes to ddr_wr (AXI5, trace+poison): awtrace and wpoison must
#     arrive intact at the slave boundary, and btrace=1 comes back in the
#     master BFM's write result.
#   - writes to sram_wr (AXI5, poison only): wpoison must arrive, and there
#     must be NO awtrace/btrace pins on that port at all -- trace terminates
#     mid-fabric with a generation-time warning. The master STILL gets
#     btrace=1 back: the adapter echoes the request's trace at the boundary
#     (BRIDGE-012), so the port keeps its promise whatever the slave carries.
# This fixture also closes the slice-1 deferred item: a simulated
# wr-channel AXI5-slave path.

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

from projects.components.bridge.dv.tbclasses.bridge1x2_wr_axi5n_tb import (
    Bridge1x2WrAxi5nTB,
)

ECHO_NOTE = (
    "the adapter echoes the request's trace onto B/R at the port (BRIDGE-012), "
    "so the master sees its own trace bit back whatever the slave contributed"
)


class WrSidebandSampler:
    """Capture slave-side AW/W sideband at handshakes and the master's
    btrace at each B handshake."""

    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.ddr_aw = []
        self.ddr_w = []
        self.sram_w = []
        self.master_b = []

    async def run(self):
        d = self.dut
        while True:
            await RisingEdge(self.clock)
            if int(d.ddr_wr_axi_awvalid.value) and int(d.ddr_wr_axi_awready.value):
                self.ddr_aw.append(int(d.ddr_wr_axi_awtrace.value))
            if int(d.ddr_wr_axi_wvalid.value) and int(d.ddr_wr_axi_wready.value):
                self.ddr_w.append(int(d.ddr_wr_axi_wpoison.value))
            if int(d.sram_wr_axi_wvalid.value) and int(d.sram_wr_axi_wready.value):
                self.sram_w.append(int(d.sram_wr_axi_wpoison.value))
            if int(d.cpu_wr_axi_bvalid.value) and int(d.cpu_wr_axi_bready.value):
                self.master_b.append(int(d.cpu_wr_axi_btrace.value))


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_wr_axi5n_sideband(dut):
    """Native AXI5 wr-channel sideband (incl. poison) end-to-end."""
    tb = Bridge1x2WrAxi5nTB(dut)

    # Structural: trace is not enabled on sram_wr, so it has no trace
    # pins; poison pins exist on BOTH slaves.
    for pin in ('sram_wr_axi_awtrace', 'sram_wr_axi_btrace'):
        assert not hasattr(dut, pin), f"trace pin leaked onto sram_wr: {pin}"
    assert hasattr(dut, 'ddr_wr_axi_wpoison')
    assert hasattr(dut, 'sram_wr_axi_wpoison')

    await tb.setup_clocks_and_reset()

    async def write(addr, data):
        """One AXI5 BFM write carrying trace + poison; returns the B trace."""
        r = await tb.master_wr[0].write_transaction(addr, data, size=2, trace=1, poison=1)
        assert r.get('success'), f"write @0x{addr:08x} failed: {r}"
        return r.get('trace', 0)

    sampler = WrSidebandSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 sign-off: wr sideband + poison through the fabric")
    tb.log.info("=" * 80)

    # --- Full-native path: writes into ddr_wr (trace + poison) --------
    # Depth (TEST_LEVEL): `sideband_beats` writes (gate 3, func 8, full 24)
    # -- the three fixed offsets first, then RNG-drawn aligned seeded ones.
    n = tb.level_cfg['sideband_beats']
    offs = [0x100, 0x1F4, 0x0FC]
    while len(offs) < n:
        o = tb.rng.randrange(0, tb._slave_mem_bytes(0), 4)
        if o not in offs:
            offs.append(o)
    tb.log.info(f"  level={tb.level}: {len(offs)} native-path writes")
    b_native = []
    for i, off in enumerate(offs):
        b_native.append(await write(0x0000_0000 + off, 0xA5A5_0000 + i))

    await ClockCycles(tb.clock, 30)
    assert all(v == 1 for v in b_native), f"btrace not echoed in BFM results: {b_native}"
    assert len(sampler.ddr_aw) >= n and all(v == 1 for v in sampler.ddr_aw), (
        f"awtrace lost on native path: {sampler.ddr_aw}")
    assert len(sampler.ddr_w) >= n and all(v == 1 for v in sampler.ddr_w), (
        f"wpoison lost on native path: {sampler.ddr_w}")
    assert sampler.master_b and all(v == 1 for v in sampler.master_b), (
        f"btrace lost on return path: {sampler.master_b}")
    tb.log.info(f"  ddr path OK: awtrace x{len(sampler.ddr_aw)}, "
                f"wpoison x{len(sampler.ddr_w)}, btrace x{len(sampler.master_b)}")

    # --- Poison-only path: writes into sram_wr ------------------------
    sampler.master_b.clear()
    m = max(2, n // 2)
    offs = [0x40, 0x80]
    while len(offs) < m:
        o = tb.rng.randrange(0, tb._slave_mem_bytes(1), 4)
        if o not in offs:
            offs.append(o)
    b_sram = []
    for i, off in enumerate(offs):
        b_sram.append(await write(0x8000_0000 + off, 0x5A5A_0000 + i))

    await ClockCycles(tb.clock, 30)
    assert all(v == 1 for v in b_sram), (
        f"btrace not echoed on the trace-less slave path: {b_sram} -- " + ECHO_NOTE)
    assert len(sampler.sram_w) >= m and all(v == 1 for v in sampler.sram_w), (
        f"wpoison lost on sram path: {sampler.sram_w}")
    # sram contributes no btrace of its own -- and the master still sees 1,
    # because the adapter echoes the request's trace at the port. The DROP is
    # proved structurally above: sram_wr has no awtrace/btrace pins at all.
    assert sampler.master_b and all(v == 1 for v in sampler.master_b), (
        f"btrace not echoed on the trace-less slave path: {sampler.master_b} -- " + ECHO_NOTE)
    tb.log.info(f"  sram path OK: wpoison x{len(sampler.sram_w)}, "
                f"btrace echoed x{len(sampler.master_b)}")

    # Nothing to allow: BRIDGE-012 is fixed in the RTL, so the boundary is
    # compliant on the native path and the drop path alike.
    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 wr sideband test PASSED")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_wr_axi5n_sideband(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_wr_axi5n"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_wr_axi5n.f'
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
        testcase="cocotb_test_bridge_1x2_wr_axi5n_sideband",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
