#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-2 slice 2 sign-off test.
#
# Asserts sideband VALUES end-to-end through the fabric structs. The AXI5
# master BFM drives ar{nsaid,trace,unique} per transaction (no pin poking
# since 2026-09-09) and the AXI5 slave BFM on sram_rd echoes trace on R:
#   - reads to sram_rd (AXI5, native path): the slave-side boundary must
#     present the SAME values at the AR handshake, and rtrace=1 comes back.
#   - reads to ddr_rd (AXI4, drop path): that slave contributes nothing to
#     the R mux, and rtrace=1 still comes back -- the adapter echoes the
#     request's trace at the port (BRIDGE-012).
# Structural: the AXI4 slave port must not have sideband pins at all, which
# is where the drop is proved.

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

from projects.components.bridge.dv.tbclasses.bridge1x2_rd_axi5n_tb import (
    Bridge1x2RdAxi5nTB,
)

ARNSAID = 0xA
RTRACE_DRIVE = 1   # the AXI5 slave BFM echoes AR trace on R


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


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_axi5n_sideband(dut):
    """Native AXI5 sideband values traverse the AMBA4 fabric structs."""
    tb = Bridge1x2RdAxi5nTB(dut)

    # Structural: the AXI4 slave has no sideband surface.
    for pin in ('ddr_rd_axi_arnsaid', 'ddr_rd_axi_artrace',
                'ddr_rd_axi_arunique', 'ddr_rd_axi_rtrace'):
        assert not hasattr(dut, pin), f"AXI4 slave grew sideband pin {pin}"

    await tb.setup_clocks_and_reset()

    async def read(slave_idx, addr):
        """One AXI5 BFM read carrying the distinctive sideband; returns (data, rtrace)."""
        resp = await tb.master_rd[0].read_transaction(
            addr, size=2, nsaid=ARNSAID, trace=1, unique=1)
        return resp[0]['data'], resp[0].get('trace', 0)

    sampler = SidebandSampler(dut, tb.clock)
    cocotb.start_soon(sampler.run())

    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 sign-off: sideband VALUES through the fabric")
    tb.log.info("=" * 80)

    # --- Native path: reads into the AXI5 slave -----------------------
    # Depth (TEST_LEVEL): `sideband_beats` reads (gate 3, func 8, full 24)
    # -- the three fixed offsets first, then RNG-drawn aligned seeded ones.
    n = tb.level_cfg['sideband_beats']
    offs = [0x100, 0x1F4, 0x0FC]
    while len(offs) < n:
        o = tb.rng.randrange(0, tb._slave_mem_bytes(1), 4)
        if o not in offs:
            offs.append(o)
    tb.log.info(f"  level={tb.level}: {len(offs)} native-path reads")
    r_native = []
    for off in offs:
        addr = 0x8000_0000 + off
        expected = tb.slave_mem_read(1, addr, master_idx=0)
        actual, rtrace = await read(1, addr)
        r_native.append(rtrace)
        assert actual == expected, (
            f"read mismatch @ 0x{addr:08x}: got 0x{actual:08x}, "
            f"expected 0x{expected:08x}")

    await ClockCycles(tb.clock, 20)
    assert len(sampler.sram_ar_samples) >= n, (
        f"expected >={n} sram AR handshakes, saw {len(sampler.sram_ar_samples)}")
    for i, s in enumerate(sampler.sram_ar_samples):
        assert s == {'nsaid': ARNSAID, 'trace': 1, 'unique': 1}, (
            f"sram AR sideband sample {i} corrupted: {s}")
    assert sampler.master_r_samples, "no master R beats sampled"
    assert all(v == RTRACE_DRIVE for v in sampler.master_r_samples), (
        f"rtrace lost on native path (pins): {sampler.master_r_samples}")
    assert all(v == RTRACE_DRIVE for v in r_native), (
        f"rtrace lost on native path (BFM response): {r_native}")
    tb.log.info(f"  native path OK: {len(sampler.sram_ar_samples)} AR "
                f"handshakes carried nsaid=0x{ARNSAID:x}/trace/unique; "
                f"{len(sampler.master_r_samples)} R beats returned rtrace=1")

    # --- Drop path: reads into the AXI4 slave --------------------------
    sampler.master_r_samples.clear()
    offs = [0x40, 0x80]
    while len(offs) < max(2, n // 2):
        o = tb.rng.randrange(0, tb._slave_mem_bytes(0), 4)
        if o not in offs:
            offs.append(o)
    r_drop = []
    for off in offs:
        addr = 0x0000_0000 + off
        expected = tb.slave_mem_read(0, addr, master_idx=0)
        actual, rtrace = await read(0, addr)
        r_drop.append(rtrace)
        assert actual == expected, (
            f"read mismatch @ 0x{addr:08x}: got 0x{actual:08x}, "
            f"expected 0x{expected:08x}")
    assert all(v == 1 for v in r_drop), (
        f"rtrace not echoed on the AXI4 drop path: {r_drop} -- the adapter echoes "
        f"the request's trace at the port (BRIDGE-012)")

    await ClockCycles(tb.clock, 20)
    assert sampler.master_r_samples, "no master R beats on ddr reads"
    assert all(v == 1 for v in sampler.master_r_samples), (
        f"rtrace not echoed on the AXI4 drop path: {sampler.master_r_samples}")
    tb.log.info(f"  drop path OK: {len(sampler.master_r_samples)} R beats from the "
                f"AXI4 slave returned the echoed rtrace=1")

    tb.assert_compliance()
    tb.log.info("=" * 80)
    tb.log.info("A5-2 slice 2 rd sideband test PASSED")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rd_axi5n_sideband(request, test_level):
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
        testcase="cocotb_test_bridge_1x2_rd_axi5n_sideband",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
