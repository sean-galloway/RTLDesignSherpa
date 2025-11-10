# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil4_slave_wr_mon
# Purpose: AXIL4 Slave Write Monitor Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Slave Write Monitor Integration Test

Thin wrapper that uses the reusable AXIL4SlaveMonitorTB testbench class.
All test logic is in bin/CocoTBFramework/tbclasses/axil4/monitor/axil4_slave_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.axil4.monitor.axil4_slave_monitor_tb import AXIL4SlaveMonitorTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axil4_slave_wr_mon_test(dut):
    """AXIL4 slave write monitor integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Create testbench (is_write=True for write slave)
    tb = AXIL4SlaveMonitorTB(dut, is_write=True, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Run all integration tests
    await tb.run_integration_tests(test_level=test_level)


# ============================================================================
# PyTest Test Runner
# ============================================================================
def generate_axil4_monitor_params():
    """
    Generate AXIL4 monitor parameter combinations based on REG_LEVEL.

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


@pytest.mark.parametrize("test_level", generate_axil4_monitor_params())
def test_axil4_slave_wr_mon(test_level):
    """
    Integration test runner.

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

    dut_name = "axil4_slave_wr_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{worker_id}_{worker_id}_{dut_name}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources
    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axil4'], "axil4_slave_wr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axil4'], f"{dut_name}.sv"),
    ]

    # Check files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (simplified for AXIL)
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': '32',
        'AXIL_DATA_WIDTH': '32',
        'UNIT_ID': '2',
        'AGENT_ID': '21',
        'MAX_TRANSACTIONS': '8',  # Reduced for AXIL
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AW': '2',
        'SKID_DEPTH_W': '2',
        'SKID_DEPTH_B': '2',
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
