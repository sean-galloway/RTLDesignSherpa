# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_slave_rd_mon_cg
# Purpose: AXI4 Slave Read Monitor CG Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Slave Read Monitor CG Integration Test

Thin wrapper that uses the reusable AXI4SlaveMonitorTB testbench class.
Tests the clock-gated version of the AXI4 slave read monitor.
All test logic is in bin/CocoTBFramework/tbclasses/axi4/monitor/axi4_slave_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.axi4.monitor.axi4_slave_monitor_tb import AXI4SlaveMonitorTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_slave_rd_mon_cg_test(dut):
    """AXI4 slave read monitor CG integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Create testbench (is_write=False for read slave)
    tb = AXI4SlaveMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Configure clock gating (enable it with default settings)
    if hasattr(dut, 'cfg_cg_enable'):
        dut.cfg_cg_enable.value = 1
    if hasattr(dut, 'cfg_cg_idle_threshold'):
        dut.cfg_cg_idle_threshold.value = 8
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
@pytest.mark.parametrize("test_level", [
    "full",
])
def test_axi4_slave_rd_mon_cg(test_level):
    """Integration test runner for AXI4 slave read monitor CG"""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
    })

    dut_name = "axi4_slave_rd_mon_cg"
    test_name = f"test_{dut_name}_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources (includes axi4_slave_rd_mon which the CG version instantiates)
    verilog_sources = [
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi4'], "axi4_slave_rd.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axi4'], "axi4_slave_rd_mon.sv"),  # Base monitor (instantiated by CG)
        os.path.join(rtl_dict['rtl_axi4'], f"{dut_name}.sv"),  # CG wrapper
    ]

    # Check files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"Source file not found: {src}")

    # Parameters
    parameters = {
        'AXI_ID_WIDTH': 8,
        'AXI_ADDR_WIDTH': 32,
        'AXI_DATA_WIDTH': 32,
        'AXI_USER_WIDTH': 1,
        'UNIT_ID': 1,
        'AGENT_ID': 20,
        'MAX_TRANSACTIONS': 16,
        'ENABLE_FILTERING': 1,
        'SKID_DEPTH_AR': 2,
        'SKID_DEPTH_R': 4,
        # CG-specific parameters
        'ENABLE_CLOCK_GATING': 1,
        'CG_IDLE_CYCLES': 8,
        'CG_GATE_MONITOR': 1,
        'CG_GATE_REPORTER': 1,
        'CG_GATE_TIMERS': 1,
    }

    # Compile options
    compile_args = [
        '-Wall',
        '-Wno-UNUSED',
        '-Wno-DECLFILENAME',
        '-Wno-PINMISSING',
        '-Wno-UNDRIVEN',
        '-Wno-WIDTHEXPAND',
        '-Wno-WIDTHTRUNC',
        '-Wno-SELRANGE',
        '-Wno-CASEINCOMPLETE',
        '-Wno-TIMESCALEMOD',
        f'-I{rtl_dict["rtl_includes"]}',
        f'-I{rtl_dict["rtl_common"]}',
        f'-I{sim_build}',
    ]

    # Add parameter overrides
    for param, value in parameters.items():
        compile_args.append(f'-G{param}={value}')

    # Environment variables
    extra_env = {
        'TEST_LEVEL': test_level,
    }

    # Run test
    run(
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,  # Disable waves for CG tests to avoid Verilator FST issues
    )
