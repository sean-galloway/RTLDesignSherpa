#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Smoke test for the REGBLOCK-cfg variant of bridge_1x2_rd_mon.
#
# Why this test exists
# --------------------
# Before this file landed, the components/bridge test suite covered the
# mon-variant bridge only via bridge_1x2_rd_mon_smoke.sv -- a wrapper
# that hard-ties every cfg_*_*_monitor_enable pin to MONITOR_ENABLE
# (default 0).  No test in the entire repo exercised the
# use_cfg_regblock=true code path, where the per-port cfg pins are
# replaced by a single AXIL slave backed by a PeakRDL-generated regblock
# whose reset defaults are monitor_enable=1 and error_enable=1.
#
# The stream_char_axil bridge was the first config to flip that switch
# (task 90.4) and immediately hung in sim -- with no minimal repro inside
# components/bridge it was impossible to tell whether the bug was in
# the generator's regblock fan-out, the harness wiring, or the
# stream_char-specific cfg routing.
#
# This test closes that hole.  bridge_1x2_rd_regblock_mon_smoke holds
# s_cfg_axil idle so the regblock keeps reset defaults; if the bridge
# elaborates and one read per slave completes, the regblock cfg path is
# functional and any remaining stream_char hang is a wiring issue.  If
# this test itself hangs, the bug lives in the generator and now has a
# 1-master / 2-slave repro at the smallest possible scale.

import os
import sys

import pytest

from TBClasses.shared.utilities import get_repo_root

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist

from projects.components.bridge.dv.tbclasses.bridge1x2_rd_tb import Bridge1x2RdTB


# ============================================================================
# CocoTB test
# ============================================================================
@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_regblock_monitor_smoke(dut):
    """Reset the regblock-cfg bridge through its smoke wrapper, then
    prove a single read transaction completes to each slave.

    s_cfg_axil is held idle by the wrapper, so the PeakRDL regblock
    retains its reset defaults -- monitor_enable=1, error_enable=1 on
    every adapter, all masks=0.  Reads should still flow through
    because the masks gate every packet type off; the monitors are
    "live but silent."
    """
    tb = Bridge1x2RdTB(dut)
    await tb.setup_clocks_and_reset()
    tb.log.info("=" * 80)
    tb.log.info("Regblock-cfg mon bridge smoke -- reset + 1 read per slave")
    tb.log.info("=" * 80)

    for slave_idx, addr in ((0, 0x00000100), (1, 0x80000100)):
        expected = tb.slave_mem_read(slave_idx, addr, master_idx=0)
        actual = await tb.master_read(0, addr)
        assert actual == expected, (
            f"Read mismatch master 0 -> slave {slave_idx} at 0x{addr:08x}: "
            f"got 0x{actual:08x}, expected 0x{expected:08x}"
        )

    await ClockCycles(tb.clock, 20)
    tb.log.info("Regblock smoke PASSED")


# ============================================================================
# Pytest wrapper
# ============================================================================
def test_bridge_1x2_rd_regblock_monitor_smoke(request):
    """Pytest wrapper for the regblock-cfg mon smoke."""
    module, repo_root_, tests_dir, log_dir, _rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba':   '../../../../rtl/amba',
    })

    dut_name = "bridge_1x2_rd_regblock_mon_smoke"
    # Wrapper lives in dv/tests/ (NOT rtl/generated/) so it survives
    # bridge regeneration -- the generator rm -rf's its own output dir.
    smoke_wrap = os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        'bridge_1x2_rd_regblock_mon_smoke.sv',
    )

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rd_regblock_mon.f',
    )
    verilog_sources = list(verilog_sources) + [smoke_wrap]

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    test_name_plus_params = f"test_{dut_name}_smoke"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    # Mirrors the existing mon-smoke flags + the silences the PeakRDL
    # regblock output requires under verilator's strict checking:
    #   -Wno-MULTIDRIVEN: peakrdl writes packed-struct fields from
    #       multiple always_comb blocks (one per packed sub-field).
    #       Verilator sees the parent struct touched by N blocks and
    #       warns; other simulators handle it fine.
    #   -Wno-WIDTHTRUNC: the regblock cpuif addr port is sized to the
    #       internal register space (8 bits for this config). The
    #       bridge top wires the full 32-bit s_cfg_axil_*addr; the
    #       upper bits are dropped (test only touches in-range
    #       addresses) -- silence the warning.
    extra_args = [
        '--assert', '--coverage',
        '-Wno-PINMISSING',
        '-Wno-WIDTHEXPAND',
        '-Wno-MULTIDRIVEN',
        '-Wno-WIDTHTRUNC',
    ] + waves['extra_args']
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
        testcase="cocotb_test_bridge_1x2_rd_regblock_monitor_smoke",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env,
    )
