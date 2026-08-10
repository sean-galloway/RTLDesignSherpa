#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-2 slice 2 sign-off test,
# write channel — including connectivity-gated POISON.
#
# The master port drives awtrace=1 / wpoison=1 while the AXI4 BFM
# issues writes:
#   - writes to ddr_wr (AXI5, trace+poison): awtrace and wpoison must
#     arrive intact at the slave boundary, and a driven ddr btrace=1
#     must return on the master's btrace output.
#   - writes to sram_wr (AXI5, poison only): wpoison must arrive, and
#     there must be NO awtrace/btrace pins on that port at all (trace
#     terminates mid-fabric with a generation-time warning).
# This fixture also closes the slice-1 deferred item: a simulated
# wr-channel AXI5-slave path.

import os
import sys

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from projects.components.bridge.dv.tbclasses.bridge1x2_wr_axi5n_tb import (
    Bridge1x2WrAxi5nTB,
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


@cocotb.test(timeout_time=200, timeout_unit="ms")
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

    dut.cpu_wr_axi_awtrace.value = 1
    dut.cpu_wr_axi_wpoison.value = 1
    dut.ddr_wr_axi_btrace.value = 1

    sampler = WrSidebandSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 sign-off: wr sideband + poison through the fabric")
    tb.log.info("=" * 80)

    # --- Full-native path: writes into ddr_wr (trace + poison) --------
    for i, off in enumerate((0x100, 0x1F4, 0x0FC)):
        await tb.master_write(0, 0x0000_0000 + off, 0xA5A5_0000 + i)

    await ClockCycles(tb.clock, 30)
    assert len(sampler.ddr_aw) >= 3 and all(v == 1 for v in sampler.ddr_aw), (
        f"awtrace lost on native path: {sampler.ddr_aw}")
    assert len(sampler.ddr_w) >= 3 and all(v == 1 for v in sampler.ddr_w), (
        f"wpoison lost on native path: {sampler.ddr_w}")
    assert sampler.master_b and all(v == 1 for v in sampler.master_b), (
        f"btrace lost on return path: {sampler.master_b}")
    tb.log.info(f"  ddr path OK: awtrace x{len(sampler.ddr_aw)}, "
                f"wpoison x{len(sampler.ddr_w)}, btrace x{len(sampler.master_b)}")

    # --- Poison-only path: writes into sram_wr ------------------------
    sampler.master_b.clear()
    for i, off in enumerate((0x40, 0x80)):
        await tb.master_write(0, 0x8000_0000 + off, 0x5A5A_0000 + i)

    await ClockCycles(tb.clock, 30)
    assert len(sampler.sram_w) >= 2 and all(v == 1 for v in sampler.sram_w), (
        f"wpoison lost on sram path: {sampler.sram_w}")
    # sram has no btrace source, so the master's btrace must read 0 for
    # these responses.
    assert sampler.master_b and all(v == 0 for v in sampler.master_b), (
        f"btrace nonzero from the trace-less slave: {sampler.master_b}")
    tb.log.info(f"  sram path OK: wpoison x{len(sampler.sram_w)}, "
                f"btrace=0 x{len(sampler.master_b)}")

    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 wr sideband test PASSED")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================


def test_bridge_1x2_wr_axi5n_sideband(request):
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
    test_name_plus_params = f"test_{dut_name}_sideband"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    extra_args = ['--assert', '--coverage'] + waves['extra_args']
    extra_env = {
        'COCOTB_LOG_LEVEL': 'INFO',
        'LOG_PATH': log_path,
        'COCOTB_RESULTS_FILE': results_path,
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
