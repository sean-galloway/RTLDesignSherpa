# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_monbus_axil_group
# Purpose: STREAM MonBus AXIL Group Integration Test
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19

"""
STREAM MonBus AXIL Group Integration Test

Simplified test suite for the monbus_axil_group module (STREAM version).
Tests monitor bus aggregation from data paths and provides:
- AXI-Lite slave read interface (error/interrupt FIFO)
- AXI-Lite master write interface (master write FIFO)
- AXI protocol packet filtering only (no AXIS/Network)

Simplified from RAPIDS:
- No AXIS/Network protocol filtering
- AXI packets only
- Simpler test scenarios

Test Organization:
- Basic packet flow tests (AXI protocol only)
- Error FIFO functionality tests (AXI-Lite slave read)

This test file imports the reusable MonbusAxilGroupTB class from:
  projects/components/stream/dv/tbclasses/monbus_axil_group_tb.py

STRUCTURE FOLLOWS RAPIDS/AMBA PATTERN:
  - CocoTB test functions at top (prefixed with cocotb_)
  - Parameter generation at bottom
  - Pytest wrappers at bottom with @pytest.mark.parametrize
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add dv directory to path so we can import from tbclasses/
dv_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if dv_dir not in sys.path:
    sys.path.insert(0, dv_dir)

from tbclasses.monbus_axil_group_tb import MonbusAxilGroupTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_flow(dut):
    """Test basic packet flow through monitor bus (AXI protocol only)."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.setup_interfaces()

    success, stats = await tb.test_basic_packet_flow(count=16)
    assert success, f"Basic packet flow test failed: {stats}"
    tb.log.info(f"✅ Basic flow: {stats['success_rate']:.1%} success rate")


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_error_fifo(dut):
    """Test error/interrupt FIFO via AXI-Lite slave read interface."""
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.setup_interfaces()

    success, stats = await tb.test_error_fifo_functionality(count=8)
    assert success, f"Error FIFO test failed: {stats}"
    tb.log.info(f"✅ Error FIFO: {stats['packets_read']} packets read")


# ===========================================================================
# PARAMETER GENERATION - at bottom of file
# ===========================================================================

def generate_monbus_axil_test_params():
    """Generate test parameters for STREAM monbus_axil_group tests.

    STREAM Simplifications:
    - Fixed 32-bit data width (STREAM uses 32-bit AXIL)
    - Fixed address width (32-bit)
    - Standard FIFO depths (64 for error, 32 for write)
    - NUM_PROTOCOLS fixed at 3 (AXI, AXIS, CORE) - RTL supports all 3
    """
    return [
        # (fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)
        (64, 32, 32, 32, 3),   # Standard STREAM configuration
    ]

monbus_axil_params = generate_monbus_axil_test_params()


# ===========================================================================
# HELPER FUNCTION - Common test setup
# ===========================================================================

def run_monbus_axil_test(testcase_name, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """Helper function to run monbus_axil_group tests with common setup."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_macro': '../../rtl/stream_macro',
    })

    dut_name = "monbus_axil_group"

    # Get Verilog sources and includes (following RAPIDS pattern)
    # Based on projects/components/rapids/rtl/filelists/macro/monbus_axil_group.f
    verilog_sources = [
        # Packages (MUST be first)
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        os.path.join(repo_root, 'projects', 'components', 'stream', 'rtl', 'includes', 'stream_pkg.sv'),

        # Monitor bus arbiter
        os.path.join(repo_root, 'rtl', 'amba', 'shared', 'monbus_arbiter.sv'),

        # GAXI FIFO (used for error and write FIFOs)
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'reset_defs.svh'),
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'fifo_defs.svh'),
        os.path.join(repo_root, 'rtl', 'amba', 'gaxi', 'gaxi_fifo_sync.sv'),
        os.path.join(repo_root, 'rtl', 'common', 'fifo_sync.sv'),
        os.path.join(repo_root, 'rtl', 'common', 'fifo_control.sv'),
        os.path.join(repo_root, 'rtl', 'common', 'counter_bin.sv'),

        # AXI-Lite slave and master components
        os.path.join(repo_root, 'rtl', 'amba', 'axil4', 'axil4_slave_rd.sv'),
        os.path.join(repo_root, 'rtl', 'amba', 'axil4', 'axil4_master_wr.sv'),
        os.path.join(repo_root, 'rtl', 'amba', 'gaxi', 'gaxi_skid_buffer.sv'),

        # Common utilities
        os.path.join(repo_root, 'rtl', 'common', 'arbiter_round_robin.sv'),
        os.path.join(repo_root, 'rtl', 'common', 'arbiter_priority_encoder.sv'),

        # Top-level module
        os.path.join(repo_root, 'projects', 'components', 'stream', 'rtl', 'stream_macro', f'{dut_name}.sv'),
    ]

    includes = [
        os.path.join(repo_root, 'rtl', 'amba', 'includes'),
        os.path.join(repo_root, 'projects', 'components', 'stream', 'rtl', 'includes'),
    ]

    # Format parameters for unique test name
    fde_str = TBBase.format_dec(fifo_depth_err, 3)
    fdw_str = TBBase.format_dec(fifo_depth_write, 3)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    np_str = TBBase.format_dec(num_protocols, 1)
    test_name_plus_params = f"test_{dut_name}_{testcase_name}_fde{fde_str}_fdw{fdw_str}_aw{aw_str}_dw{dw_str}_np{np_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FIFO_DEPTH_ERR': fifo_depth_err,
        'FIFO_DEPTH_WRITE': fifo_depth_write,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'NUM_PROTOCOLS': num_protocols,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TEST_FIFO_DEPTH_ERR': str(fifo_depth_err),
        'TEST_FIFO_DEPTH_WRITE': str(fifo_depth_write),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_NUM_PROTOCOLS': str(num_protocols),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_monbus_axil_group', test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module='test_monbus_axil_group',
            testcase=f"cocotb_{testcase_name}",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
                "-Wno-TIMESCALEMOD",
            ],
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plusargs=[
                "--trace",
            ]
        )
        print(f"✓ {testcase_name} completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ {testcase_name} failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - at bottom of file
# ===========================================================================

@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_basic_flow(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """STREAM MonBus AXIL Group basic flow test."""
    run_monbus_axil_test("test_basic_flow", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)


@pytest.mark.parametrize("fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_error_fifo(request, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """STREAM MonBus AXIL Group error FIFO test."""
    run_monbus_axil_test("test_error_fifo", fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)
