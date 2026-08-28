#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-2 slice 2 sign-off test.
#
# Asserts sideband VALUES end-to-end through the fabric structs — the
# item deferred from A5-1 ("the BFM issues trace-clear transactions by
# default"). The master port's ar{nsaid,trace,unique} inputs are driven
# to known non-zero values while the AXI4 BFM issues reads:
#   - reads to sram_rd (AXI5, native path): the slave-side boundary
#     must present the SAME values at the AR handshake, and a driven
#     sram rtrace=1 must arrive back at the master's rtrace output.
#   - reads to ddr_rd (AXI4, drop path): the master's rtrace output
#     must stay 0 (an AXI4 slave contributes nothing to the R mux).
# Structural: the AXI4 slave port must not have sideband pins at all.

import os
import sys

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from projects.components.bridge.dv.tbclasses.bridge1x2_rd_axi5n_tb import (
    Bridge1x2RdAxi5nTB,
)

ARNSAID = 0xA
RTRACE_DRIVE = 1


class SidebandSampler:
    """Capture slave-side AR sideband at each AR handshake and the
    master-side rtrace at each R beat."""

    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.sram_ar_samples = []
        self.master_r_samples = []

    async def run(self):
        while True:
            await RisingEdge(self.clock)
            if (int(self.dut.sram_rd_axi_arvalid.value)
                    and int(self.dut.sram_rd_axi_arready.value)):
                self.sram_ar_samples.append({
                    'nsaid': int(self.dut.sram_rd_axi_arnsaid.value),
                    'trace': int(self.dut.sram_rd_axi_artrace.value),
                    'unique': int(self.dut.sram_rd_axi_arunique.value),
                })
            if (int(self.dut.cpu_rd_axi_rvalid.value)
                    and int(self.dut.cpu_rd_axi_rready.value)):
                self.master_r_samples.append(
                    int(self.dut.cpu_rd_axi_rtrace.value))


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_axi5n_sideband(dut):
    """Native AXI5 sideband values traverse the AMBA4 fabric structs."""
    tb = Bridge1x2RdAxi5nTB(dut)

    # Structural: the AXI4 slave has no sideband surface.
    for pin in ('ddr_rd_axi_arnsaid', 'ddr_rd_axi_artrace',
                'ddr_rd_axi_arunique', 'ddr_rd_axi_rtrace'):
        assert not hasattr(dut, pin), f"AXI4 slave grew sideband pin {pin}"

    await tb.setup_clocks_and_reset()

    # Drive constant, distinctive sideband on the AXI5 master port and
    # a live rtrace from the external AXI5 slave.
    dut.cpu_rd_axi_arnsaid.value = ARNSAID
    dut.cpu_rd_axi_artrace.value = 1
    dut.cpu_rd_axi_arunique.value = 1
    dut.sram_rd_axi_rtrace.value = RTRACE_DRIVE

    sampler = SidebandSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 sign-off: sideband VALUES through the fabric")
    tb.log.info("=" * 80)

    # --- Native path: reads into the AXI5 slave -----------------------
    for off in (0x100, 0x1F4, 0x0FC):
        addr = 0x8000_0000 + off
        expected = tb.slave_mem_read(1, addr, master_idx=0)
        actual = await tb.master_read(0, addr)
        assert actual == expected, (
            f"read mismatch @ 0x{addr:08x}: got 0x{actual:08x}, "
            f"expected 0x{expected:08x}")

    await ClockCycles(tb.clock, 20)
    assert len(sampler.sram_ar_samples) >= 3, (
        f"expected >=3 sram AR handshakes, saw {len(sampler.sram_ar_samples)}")
    for i, s in enumerate(sampler.sram_ar_samples):
        assert s == {'nsaid': ARNSAID, 'trace': 1, 'unique': 1}, (
            f"sram AR sideband sample {i} corrupted: {s}")
    assert sampler.master_r_samples, "no master R beats sampled"
    assert all(v == RTRACE_DRIVE for v in sampler.master_r_samples), (
        f"rtrace lost on native path: {sampler.master_r_samples}")
    tb.log.info(f"  native path OK: {len(sampler.sram_ar_samples)} AR "
                f"handshakes carried nsaid=0x{ARNSAID:x}/trace/unique; "
                f"{len(sampler.master_r_samples)} R beats returned rtrace=1")

    # --- Drop path: reads into the AXI4 slave --------------------------
    sampler.master_r_samples.clear()
    for off in (0x40, 0x80):
        addr = 0x0000_0000 + off
        expected = tb.slave_mem_read(0, addr, master_idx=0)
        actual = await tb.master_read(0, addr)
        assert actual == expected, (
            f"read mismatch @ 0x{addr:08x}: got 0x{actual:08x}, "
            f"expected 0x{expected:08x}")

    await ClockCycles(tb.clock, 20)
    assert sampler.master_r_samples, "no master R beats on ddr reads"
    assert all(v == 0 for v in sampler.master_r_samples), (
        f"rtrace nonzero from an AXI4 slave: {sampler.master_r_samples}")
    tb.log.info(f"  drop path OK: {len(sampler.master_r_samples)} R beats "
                f"from the AXI4 slave returned rtrace=0")

    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 rd sideband test PASSED")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================


def test_bridge_1x2_rd_axi5n_sideband(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_rd_axi5n"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rd_axi5n.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    test_name_plus_params = f"test_{dut_name}_sideband"
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
        **waves['extra_env'],
    }

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_bridge_1x2_rd_axi5n_sideband",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
