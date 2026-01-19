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

Test Types:
- 'basic_flow': Basic packet flow tests (AXI protocol only)
- 'error_fifo': Error FIFO functionality tests (AXI-Lite slave read)

This test file imports the reusable MonbusAxilGroupTB class from:
  projects/components/stream/dv/tbclasses/monbus_axil_group_tb.py

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import from project area
from projects.components.stream.dv.tbclasses.monbus_axil_group_tb import MonbusAxilGroupTB

# Coverage integration - optional import
try:
    from projects.components.stream.dv.stream_coverage import (
        CoverageHelper,
        get_coverage_compile_args,
        get_coverage_env
    )
    COVERAGE_AVAILABLE = True
except ImportError:
    COVERAGE_AVAILABLE = False

    def get_coverage_compile_args():
        """Stub when coverage not available."""
        return []

    def get_coverage_env(test_name, sim_build=None):
        """Stub when coverage not available."""
        return {}


# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_monbus_axil_group(dut):
    """Unified MonBus AXIL Group test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'basic_flow': Test basic packet flow through monitor bus (AXI protocol only)
    - 'error_fifo': Test error/interrupt FIFO via AXI-Lite slave read interface
    """
    test_type = os.environ.get('TEST_TYPE', 'basic_flow')
    tb = MonbusAxilGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.setup_interfaces()

    # Branch on test type
    if test_type == 'basic_flow':
        success, stats = await tb.test_basic_packet_flow(count=16)
        assert success, f"Basic packet flow test failed: {stats}"
        tb.log.info(f"✅ Basic flow: {stats['success_rate']:.1%} success rate")
    elif test_type == 'error_fifo':
        success, stats = await tb.test_error_fifo_functionality(count=8)
        assert success, f"Error FIFO test failed: {stats}"
        tb.log.info(f"✅ Error FIFO: {stats['packets_read']} packets read")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_monbus_axil_test_params():
    """Generate test parameters for STREAM monbus_axil_group tests.

    STREAM Simplifications:
    - Fixed 32-bit data width (STREAM uses 32-bit AXIL)
    - Fixed address width (32-bit)
    - Standard FIFO depths (64 for error, 32 for write)
    - NUM_PROTOCOLS fixed at 3 (AXI, AXIS, CORE) - RTL supports all 3

    Parameters: (test_type, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)

    Test Types:
        - 'basic_flow': Basic packet flow through monitor bus
        - 'error_fifo': Error/interrupt FIFO functionality
    """
    test_types = ['basic_flow', 'error_fifo']
    base_params = [
        # (fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols)
        (64, 32, 32, 32, 3),   # Standard STREAM configuration
    ]

    # Generate final params by adding test_type to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            params.append((test_type,) + base)

    return params


monbus_axil_params = generate_monbus_axil_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize("test_type, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols",
                         monbus_axil_params)
def test_monbus_axil_group(request, test_type, fifo_depth_err, fifo_depth_write, addr_width, data_width, num_protocols):
    """Pytest wrapper for MonBus AXIL Group tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_macro': '../../rtl/macro',
    })

    dut_name = "monbus_axil_group"

    # Get Verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/macro/monbus_axil_group.f'
    )

    # Format parameters for unique test name
    fde_str = TBBase.format_dec(fifo_depth_err, 3)
    fdw_str = TBBase.format_dec(fifo_depth_write, 3)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    np_str = TBBase.format_dec(num_protocols, 1)
    test_name_plus_params = f"test_{dut_name}_{test_type}_fde{fde_str}_fdw{fdw_str}_aw{aw_str}_dw{dw_str}_np{np_str}"

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
        'TEST_TYPE': test_type,  # ← Pass test type to cocotb
        'TEST_FIFO_DEPTH_ERR': str(fifo_depth_err),
        'TEST_FIFO_DEPTH_WRITE': str(fifo_depth_write),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_NUM_PROTOCOLS': str(num_protocols),
    }

    # Add coverage environment variables if coverage is enabled
    coverage_env = get_coverage_env(test_name_plus_params, sim_build=sim_build)
    extra_env.update(coverage_env)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_monbus_axil_group', test_name_plus_params)

    # Build args conditionally based on waves
    waves_enabled = False
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-SELRANGE", "-Wno-WIDTHEXPAND", "-Wno-WIDTH"]
    sim_args = []
    plusargs = []
    if waves_enabled:
        compile_args.extend(["--trace", "--trace-structs", "--trace-depth", "99"])
        sim_args.extend(["--trace", "--trace-structs", "--trace-depth", "99"])
        plusargs.append("--trace")

    # Add coverage compile args if COVERAGE=1
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module='test_monbus_axil_group',
            testcase="cocotb_test_monbus_axil_group",  # ← Single cocotb test
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator="verilator",
            waves=waves_enabled,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ MonBus AXIL {test_type} test PASSED! Logs: {log_path}")
    except Exception as e:
        print(f"✗ MonBus AXIL {test_type} test FAILED: {str(e)}")
        print(f"Logs: {log_path}")
        raise
