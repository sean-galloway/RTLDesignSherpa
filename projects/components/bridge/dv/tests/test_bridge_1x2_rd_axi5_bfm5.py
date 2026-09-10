#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): BRIDGE-002 A5-1 sign-off test.
#
# Since 2026-09-09 every generated TB drives an AXI5 port with the AXI5 BFM
# and arms an AXI5ComplianceChecker on it, so this test no longer needs its
# own subclass; it is the read-side sign-off that drives sideband VALUES
# through the BFM (trace/unique per transaction -- this fixture's master
# enables exactly those two; it has no arnsaid pin) into both AXI4
# slaves and requires the checker's verdict to be clean.

import os
import sys
import pytest
import logging

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from projects.components.bridge.dv.tbclasses.bridge1x2_rd_axi5_tb import (
    Bridge1x2RdAxi5TB,
)


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_axi5_bfm5(dut):
    """AXI5 BFM reads through the AXI5 boundary into both AXI4 slaves,
    with the AXI5 compliance checker watching the port."""
    tb = Bridge1x2RdAxi5TB(dut)
    await tb.setup_clocks_and_reset()

    tb.log.info("=" * 80)
    tb.log.info("A5-1 sign-off: AXI5 BFM + compliance checker on the AXI5 port")
    tb.log.info("=" * 80)

    # Reads against both slaves' seeded patterns, several offsets each,
    # so AR/R see back-to-back traffic (not just one transaction).
    # Depth (TEST_LEVEL): the three fixed offsets, then RNG-drawn aligned
    # seeded offsets up to `sideband_beats` per slave (gate 3, func 8,
    # full 24), with the compliance checker watching all of it.
    want = tb.level_cfg['sideband_beats']
    for slave_idx, base in ((0, 0x0000_0000), (1, 0x8000_0000)):
        offs = [0x100, 0x1F4, 0x0FC]
        while len(offs) < want:
            o = tb.rng.randrange(0, tb._slave_mem_bytes(slave_idx), 4)
            if o not in offs:
                offs.append(o)
        tb.log.info(f"  slave {slave_idx}: {len(offs)} AXI5-BFM reads (level={tb.level})")
        for i, off in enumerate(offs):
            addr = base + off
            expected = tb.slave_mem_read(slave_idx, addr, master_idx=0)
            resp = await tb.master_rd[0].read_transaction(
                addr, size=2, id=i % 8, trace=1, unique=(i & 1))
            actual = resp[0]['data']
            assert resp[0].get('trace', 0) == 1, (
                f"rtrace not echoed for slave {slave_idx}: got {resp[0].get('trace')}. "
                f"Both slaves here are AXI4 and contribute no trace of their own; the "
                f"adapter echoes the request's bit at the port (BRIDGE-012)")
            assert actual == expected, (
                f"AXI5-BFM read mismatch slave {slave_idx} @ 0x{addr:08x}: "
                f"got 0x{actual:08x}, expected 0x{expected:08x}"
            )
            tb.log.info(f"  R slave={slave_idx} addr=0x{addr:08x} "
                        f"data=0x{actual:08x} OK")

    await ClockCycles(tb.clock, 50)
    tb.assert_compliance()

    tb.log.info("=" * 80)
    tb.log.info("A5-1 sign-off test PASSED")
    tb.log.info("=" * 80)


# ============================================================================
# Pytest runner (mirrors the generated harness)
# ============================================================================



@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rd_axi5_bfm5(request, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })

    dut_name = "bridge_1x2_rd_axi5"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rd_axi5.f'
    )

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_bfm5_{test_level}_{reg_level}"
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
        testcase="cocotb_test_bridge_1x2_rd_axi5_bfm5",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env
    )
