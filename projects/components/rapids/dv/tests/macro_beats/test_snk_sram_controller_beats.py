# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_snk_sram_controller
# Purpose: RAPIDS Sink SRAM Controller Macro Validation Test - Phase 1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_macro_beats
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Sink SRAM Controller Macro Validation Test - Phase 1

Test suite for the snk_sram_controller module:
- Multi-channel SRAM controller for SINK path
- Data flow: Network Slave (fill) -> SRAM -> AXI Write Engine (drain)

Features tested:
- Fill allocation interface
- Fill data interface
- Drain flow control interface
- Drain data interface
- Multi-channel operation

STRUCTURE FOLLOWS AMBA PATTERN:
  - CocoTB test functions at top (prefixed with cocotb_)
  - Parameter generation at bottom
  - Pytest wrappers at bottom with @pytest.mark.parametrize
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

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.rapids.dv.tbclasses.snk_sram_controller_tb import SnkSRAMControllerTB


# ===========================================================================
# BASIC FUNCTIONALITY TESTS
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_basic_fill_drain(dut):
    """Test basic fill and drain cycle on channel 0"""
    tb = SnkSRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_basic_fill_drain(channel=0, count=10)
    tb.generate_test_report()
    assert result, "Basic fill/drain test failed"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_space_tracking(dut):
    """Test space tracking accuracy"""
    tb = SnkSRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_space_tracking(channel=0)
    tb.generate_test_report()
    assert result, "Space tracking test failed"


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_multi_channel(dut):
    """Test multi-channel operation"""
    tb = SnkSRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_multi_channel(num_ops_per_channel=3)
    tb.generate_test_report()
    assert result, "Multi-channel test failed"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_snk_sram_controller_test_params():
    """Generate test parameters for snk_sram_controller tests.

    Returns list of tuples: (num_channels, data_width, sram_depth)
    """
    return [
        # Default configuration
        (8, 512, 512),
        # Fewer channels
        (4, 512, 256),
        # Smaller data width
        (8, 256, 512),
    ]


snk_sram_controller_params = generate_snk_sram_controller_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Functionality
# ===========================================================================

@pytest.mark.macro_beats
@pytest.mark.snk_sram_controller
@pytest.mark.parametrize("num_channels, data_width, sram_depth", snk_sram_controller_params)
def test_basic_fill_drain(request, num_channels, data_width, sram_depth):
    """Pytest: Test basic fill/drain cycle"""
    _run_snk_sram_controller_test(request, "cocotb_test_basic_fill_drain",
                                   num_channels, data_width, sram_depth)


@pytest.mark.macro_beats
@pytest.mark.snk_sram_controller
@pytest.mark.parametrize("num_channels, data_width, sram_depth", snk_sram_controller_params)
def test_space_tracking(request, num_channels, data_width, sram_depth):
    """Pytest: Test space tracking"""
    _run_snk_sram_controller_test(request, "cocotb_test_space_tracking",
                                   num_channels, data_width, sram_depth)


@pytest.mark.macro_beats
@pytest.mark.snk_sram_controller
@pytest.mark.parametrize("num_channels, data_width, sram_depth", snk_sram_controller_params)
def test_multi_channel(request, num_channels, data_width, sram_depth):
    """Pytest: Test multi-channel operation"""
    _run_snk_sram_controller_test(request, "cocotb_test_multi_channel",
                                   num_channels, data_width, sram_depth)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_snk_sram_controller_test(request, testcase_name, num_channels, data_width, sram_depth):
    """Helper function to run snk_sram_controller tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        num_channels: Number of channels
        data_width: Data width
        sram_depth: SRAM depth per channel
    """
    # Check if coverage collection is enabled via environment variable
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_macro_beats': '../../rtl/macro_beats'
    })

    dut_name = "snk_sram_controller_beats"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro_beats/snk_sram_controller_beats.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    sd_str = TBBase.format_dec(sram_depth, 4)

    # Extract test name from cocotb function
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_nc{nc_str}_dw{dw_str}_sd{sd_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'DATA_WIDTH': data_width,
        'SRAM_DEPTH': sram_depth,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': str(num_channels),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_SRAM_DEPTH': str(sram_depth),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Build compile args - add coverage if enabled
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT"]
    if coverage_enabled:
        compile_args.extend([
            "--coverage-line",
            "--coverage-toggle",
            "--coverage-underscore",
        ])

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase_name,
            parameters=rtl_parameters,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=os.environ.get('ENABLE_WAVEDUMP', '0') == '1',
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"Test completed! Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"  View command: {cmd_filename}")
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Run basic test when executed directly
    print("Running basic snk_sram_controller test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_snk_sram_controller_test(request, "cocotb_test_basic_fill_drain",
                                  num_channels=8, data_width=512, sram_depth=512)
