# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_master_rd_mon
# Purpose: AXI4 Master Read Monitor Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Master Read Monitor Integration Test

Thin wrapper that uses the reusable AXI4MasterMonitorTB testbench class.
All test logic is in bin/TBClasses/axi4/monitor/axi4_master_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.axi4.monitor.axi4_master_monitor_tb import AXI4MasterMonitorTB
from TBClasses.shared.utilities import get_paths

@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi4_master_rd_mon_test(dut):
    """AXI4 master read monitor integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    # Create testbench (is_write=False for read master)
    tb = AXI4MasterMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Run all integration tests
    await tb.run_integration_tests(test_level=test_level)

def validate_addr_width(addr_width):
    """
    Validate address width meets AXI4 specification constraints.

    Args:
        addr_width: Address width value (int or str)

    Raises:
        ValueError: If address width exceeds 64-bits
    """
    addr_w = int(addr_width)
    if addr_w > 64:
        raise ValueError(
            f"Invalid AXI4 configuration: AXI_ADDR_WIDTH={addr_w} exceeds maximum of 64-bits. "
            f"AXI4 specification limits address width to 64-bits."
        )

def generate_axi4_monitor_params():
    """
    Generate AXI4 monitor parameter combinations based on REG_LEVEL.

    Parameter tuple: (id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level)

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test
        FUNC: 3 tests - Functional validation with variations
        FULL: 9 tests - Comprehensive testing

    Returns:
        list: Parameter tuples for pytest.mark.parametrize

    Raises:
        ValueError: If generated parameters violate AXI4 constraints
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Quick smoke test - basic configuration
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'gate'),
        ]

    elif reg_level == 'FUNC':
        # Functional validation - variations in depth and test_level
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'gate'),   # Standard config
            (8, 32, 32, 1, 16, 4, 8, 'func'),  # Deeper skid buffers
            (8, 32, 32, 1, 32, 2, 4, 'func'),  # More transactions
        ]

    else:  # FULL
        # Comprehensive testing - all test_levels × configurations
        test_levels = ['gate', 'func', 'full']
        configs = [
            (8, 32, 32, 1, 16, 2, 4),  # Standard
            (8, 32, 32, 1, 16, 4, 8),  # Deep skid
            (8, 32, 32, 1, 32, 2, 4),  # Many transactions
        ]
        params = [
            (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r, level)
            for (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r) in configs
            for level in test_levels
        ]

    # Validate all parameters
    for param in params:
        _, addr_w, _, _, _, _, _, _ = param
        if addr_w > 64:
            raise ValueError(
                f"Invalid AXI4 configuration: addr_width={addr_w} exceeds maximum of 64-bits. "
                f"Full parameter set: {param}"
            )

    return params

# ============================================================================
# PyTest Test Runner
# ============================================================================
@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level",
    generate_axi4_monitor_params()
)
def test_axi4_master_rd_mon(id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level):
    """
    Integration test runner for AXI4 master read monitor.

    Controlled by REG_LEVEL environment variable:
        GATE: 1 test  - Quick smoke test
        FUNC: 3 tests - Functional validation (default)
        FULL: 9 tests - Comprehensive testing
    """

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi4_master_rd_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{dut_name}_iw{id_width}_aw{addr_width}_dw{data_width}_mt{max_trans}_sk{skid_ar}x{skid_r}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources
    verilog_sources = [
        # Monitor packages (must be compiled in order)
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi4'], "axi4_master_rd.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axi4'], f"{dut_name}.sv"),
    ]

    # Check files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (from test parameters)
    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': str(max_trans),
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AR': str(skid_ar),
        'SKID_DEPTH_R': str(skid_r),
    }

    # Validate address width meets AXI4 specification
    validate_addr_width(rtl_parameters['AXI_ADDR_WIDTH'])

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_STUB': '0',  # Not stub - real RTL
        'SEED': str(random.randint(0, 100000)),
        'TEST_CLK_PERIOD': '10',
    }

    print(f"\n{'='*80}")
    print(f"AXI4 Master Read Monitor WaveDrom Test")
    print(f"{'='*80}")

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-CASEINCOMPLETE',
        '-Wno-DECLFILENAME',
        '-Wno-PINMISSING',
        '-Wno-SELRANGE',
        '-Wno-SYNCASYNCNET',
        '-Wno-TIMESCALEMOD',
        '-Wno-UNDRIVEN',
        '-Wno-UNUSED',
        '-Wno-WIDTHEXPAND',
        '-Wno-WIDTHTRUNC',
    ]

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    sim_args = ['--trace'] if enable_waves else []

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module="test_axi4_master_rd_mon",
            testcase="axi4_master_rd_mon_wavedrom_test",  # ← Run wavedrom test specifically!
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ AXI4 Master Read Monitor WaveDrom test completed!")
        print(f"Logs: {log_path}")
        print(f"WaveJSON files: {sim_build}/axi4_*.json")
    except Exception as e:
        print(f"❌ AXI4 Master Read Monitor WaveDrom test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        raise
