#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Smoke test for the monitored variant of bridge_1x2_rd_mon.
#
# Stage-3 of bridge USE_MONITOR support adds a large monitor-side port
# surface (per-port cfg, AXIL slave, AXIL master, group cfg, IRQ) at
# the bridge top. This test points cocotb at bridge_1x2_rd_mon_smoke -- a
# thin SV wrapper that ties every monitor port to a safe default and
# re-exposes only the original AXI4 surface -- and runs the same
# basic_connectivity smoke phase as the non-monitor test, just to
# prove the monitored generator output actually elaborates and resets.

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
# CocoTB test -- minimal smoke: reset + one read transaction to each slave
# ============================================================================
@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rd_mon_monitor_smoke(dut):
    """Reset the monitored bridge (through smoke wrapper) and prove a
    single read transaction completes to each slave. Monitors are
    quiet (cfg_*_*_enable=0) so the only thing we're proving here is
    that the new generator output elaborates and that the monitor
    tie-offs don't break ordinary AXI4 traffic."""
    tb = Bridge1x2RdTB(dut)
    await tb.setup_clocks_and_reset()
    tb.log.info("=" * 80)
    tb.log.info("Monitored bridge smoke -- reset + 1 read per slave")
    tb.log.info("=" * 80)

    # ---- block_ready polarity probe -------------------------------------
    # If the upstream axi_monitor_base block_ready signal really has
    # inverted polarity vs. the wrapper's gating, then immediately
    # after reset:
    #   - active_count = 0  (no in-flight transactions yet)
    #   - block_ready  = 0  (count < MAX-2)
    #   - and the wrapper does `arready = core & block_ready` -> arready=0
    # So the AR can never fire, count never increments, deadlock from
    # cycle 0. Read the actual values from the cpu_rd master adapter's
    # u_timing_wrapper_rd, which is the axi4_slave_rd_mon instance.
    # Probe the wrapper's gated arready vs core arready, and the
    # gating signal itself. The wrapper variable names exposed at the
    # axi4_slave_rd_mon level are stable -- generate-block hierarchy
    # naming varies by simulator, so go straight to the wrapper-level
    # signals that the gating expression directly references.
    cpu_rd_wrap = dut.u_dut.u_cpu_rd_adapter.u_timing_wrapper_rd
    tb.log.info("=" * 80)
    tb.log.info("axi4_slave_rd_mon at cpu_rd master adapter, post-reset:")
    tb.log.info(f"  w_block_ready          = {int(cpu_rd_wrap.w_block_ready.value)}")
    tb.log.info(f"  w_core_s_axi_arready   = {int(cpu_rd_wrap.w_core_s_axi_arready.value)}")
    tb.log.info(f"  s_axi_arready (output) = {int(cpu_rd_wrap.s_axi_arready.value)}")
    tb.log.info(f"  MAX_TRANSACTIONS param defaults to 16 -> threshold = 14")
    tb.log.info(f"  expected (correct polarity): w_block_ready=1 -> arready=core")
    tb.log.info(f"  observed (inverted bug):    w_block_ready=0 -> arready=0 (deadlock)")
    tb.log.info("=" * 80)

    # One read into each slave's window. Same probe addresses as the
    # non-monitor basic_connectivity test (cocotb_test_bridge_1x2_rd_mon_
    # basic_connectivity in test_bridge_1x2_rd_mon.py) so the seeded slave
    # memory pattern matches.
    for slave_idx, addr in ((0, 0x00000100), (1, 0x80000100)):
        expected = tb.slave_mem_read(slave_idx, addr, master_idx=0)
        actual = await tb.master_read(0, addr)
        assert actual == expected, (
            f"Read mismatch master 0 -> slave {slave_idx} at 0x{addr:08x}: "
            f"got 0x{actual:08x}, expected 0x{expected:08x}"
        )

    await ClockCycles(tb.clock, 20)
    tb.log.info("Smoke PASSED")


# ============================================================================
# Pytest wrapper
# ============================================================================
def test_bridge_1x2_rd_mon_monitor_smoke(request):
    """Pytest wrapper for the monitored 1x2_rd smoke."""
    module, repo_root_, tests_dir, log_dir, _rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba':   '../../../../rtl/amba',
    })

    dut_name = "bridge_1x2_rd_mon_smoke"
    # Smoke wrapper lives in dv/tests/ (NOT rtl/generated/) so it
    # survives bridge regeneration -- generate_bridge() rm -rf's the
    # bridge_<name>/ output directory before each run.
    smoke_wrap = os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        'bridge_1x2_rd_mon_smoke.sv',
    )

    # The bridge filelist (regenerated with use_monitor=true) already
    # pulls in every dep the smoke wrapper needs except the wrapper
    # itself; append it after the framework returns the base source
    # list so it always appears last (the wrapper instantiates the
    # bridge top, so the bridge top must compile first).
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/bridge/rtl/filelists/bridge_1x2_rd_mon.f',
    )
    verilog_sources = list(verilog_sources) + [smoke_wrap]

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    test_name_plus_params = f"test_{dut_name}_monitor_smoke"
    sim_build_name = f"{test_name_plus_params}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    # --assert promotes any verilator warning to an error. The
    # monitored bridge pulls in axi_monitor_trans_mgr / monbus_axil_group
    # which have pre-existing benign WIDTHEXPAND warnings, and the _mon
    # wrappers expose status pins (cfg_conflict_error, *_count) that
    # we intentionally leave unconnected -- silence those classes only.
    extra_args = [
        '--assert', '--coverage',
        '-Wno-PINMISSING',
        '-Wno-WIDTHEXPAND',
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
        testcase="cocotb_test_bridge_1x2_rd_mon_monitor_smoke",
        sim_build=sim_build,
        waves=False,
        extra_args=extra_args,
        plus_args=waves['sim_args'],
        extra_env=extra_env,
    )
