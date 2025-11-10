# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil4_master_wr_mon_cg
# Purpose: AXIL4 Master Write Monitor CG Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Master Write Monitor CG Integration Test

Thin wrapper that uses the reusable AXIL4MasterMonitorTB testbench class.
Tests the clock-gated version of the AXIL4 master write monitor.
All test logic is in bin/CocoTBFramework/tbclasses/axil4/monitor/axil4_master_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.axil4.monitor.axil4_master_monitor_tb import AXIL4MasterMonitorTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axil4_master_wr_mon_cg_test(dut):
    """AXIL4 master write monitor CG integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Create testbench (is_write=True for write master)
    tb = AXIL4MasterMonitorTB(dut, is_write=True, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Configure clock gating (enable it with default settings)
    if hasattr(dut, 'cfg_cg_enable'):
        dut.cfg_cg_enable.value = 1
    if hasattr(dut, 'cfg_cg_idle_threshold'):
        dut.cfg_cg_idle_threshold.value = 4  # Lower threshold for AXIL (simpler protocol)
    if hasattr(dut, 'cfg_cg_gate_monitor'):
        dut.cfg_cg_gate_monitor.value = 1
    if hasattr(dut, 'cfg_cg_gate_reporter'):
        dut.cfg_cg_gate_reporter.value = 1
    if hasattr(dut, 'cfg_cg_gate_timers'):
        dut.cfg_cg_gate_timers.value = 1

    # Run all integration tests (same as non-CG version)
    await tb.run_integration_tests(test_level=test_level)


# ============================================================================
# PyTest Test Runner
# ============================================================================
def generate_axil4_monitor_cg_params():
    """
    Generate AXIL4 monitor CG parameter combinations based on REG_LEVEL.

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test (basic)
        FUNC: 3 tests - Functional validation (basic, medium, full)
        FULL: 3 tests - Comprehensive testing (basic, medium, full)

    Returns:
        list: Test level values for pytest.mark.parametrize
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return ['basic']
    else:  # FUNC or FULL
        return ['basic', 'medium', 'full']


@pytest.mark.parametrize("test_level", generate_axil4_monitor_cg_params())
def test_axil4_master_wr_mon_cg(test_level):
    """
    Integration test runner for CG version.

    Controlled by REG_LEVEL environment variable:
        GATE: 1 test  - Quick smoke test
        FUNC: 3 tests - Functional validation (default)
        FULL: 3 tests - Comprehensive testing
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axil4_master_wr_mon_cg"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{worker_id}_{worker_id}_{dut_name}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources (includes axil4_master_wr_mon which the CG version instantiates)
    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axil4'], "axil4_master_wr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axil4'], "axil4_master_wr_mon.sv"),  # Base monitor (instantiated by CG)
        os.path.join(rtl_dict['rtl_axil4'], f"{dut_name}.sv"),  # CG wrapper
    ]

    # Check files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (simplified for AXIL)
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': '32',
        'AXIL_DATA_WIDTH': '32',
        'UNIT_ID': '1',
        'AGENT_ID': '11',
        'MAX_TRANSACTIONS': '8',  # Reduced for AXIL
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AW': '2',
        'SKID_DEPTH_W': '2',
        'SKID_DEPTH_B': '2',
        # Clock gating parameters
        'ENABLE_CLOCK_GATING': '1',
        'CG_IDLE_CYCLES': '4',
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'TEST_LEVEL': test_level,
    }

    run(
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=module,
        simulator="verilator",
        parameters=rtl_parameters,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,  # VCD controlled by compile_args, not cocotb-test
        timescale='1ns/1ps',
        verilator_trace=False,
        compile_args=[
            "-Wno-WIDTH",
            "-Wno-SELRANGE",
            "-Wno-CASEINCOMPLETE",
            "-Wno-BLKANDNBLK",
            "--timescale", "1ns/1ps",
        ],
        includes=[rtl_dict['rtl_amba_includes']]
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
