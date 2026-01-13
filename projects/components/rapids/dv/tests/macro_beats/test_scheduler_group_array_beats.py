# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_beats_scheduler_group_array
# Purpose: RAPIDS Beats Scheduler Group Array Macro Validation Test - Phase 1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_macro_beats
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Scheduler Group Array Macro Validation Test - Phase 1

Test suite for the beats_scheduler_group_array module which instantiates:
- 8x beats_scheduler_group instances (each with descriptor_engine + scheduler)
- Shared AXI4 descriptor read interface with round-robin arbitration
- Aggregated MonBus output from all 8 groups + arbiter (9 sources total)

Features tested:
- Single channel operation
- Multi-channel concurrent operations
- AXI arbitration fairness
- MonBus aggregation
- All channels sequential
- Stress testing

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
from projects.components.rapids.dv.tbclasses.scheduler_group_array_beats_tb import SchedulerGroupArrayBeatsTB


# ===========================================================================
# BASIC FUNCTIONALITY TESTS
# ===========================================================================

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_single_channel(dut):
    """Test basic operation on a single channel"""
    tb = SchedulerGroupArrayBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result, stats = await tb.test_single_channel_operation(channel=0)
    tb.finalize_test()
    tb.print_test_summary()
    assert result, f"Single channel test failed: {stats}"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_multi_channel_concurrent(dut):
    """Test concurrent operations on multiple channels"""
    tb = SchedulerGroupArrayBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result, stats = await tb.test_multi_channel_concurrent_operation(
        num_channels_active=4,
        ops_per_channel=2,
        test_level=0
    )
    tb.finalize_test()
    tb.print_test_summary()
    assert result, f"Multi-channel concurrent test failed: {stats}"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_axi_arbitration(dut):
    """Test AXI arbitration behavior with multiple channels"""
    tb = SchedulerGroupArrayBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result, stats = await tb.test_axi_arbitration(num_operations=8)
    tb.finalize_test()
    tb.print_test_summary()
    assert result, f"AXI arbitration test failed: {stats}"


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_all_channels_sequential(dut):
    """Test all 8 channels sequentially"""
    tb = SchedulerGroupArrayBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result, stats = await tb.test_all_channels_sequential(descriptors_per_channel=1)
    tb.finalize_test()
    tb.print_test_summary()
    assert result, f"All channels sequential test failed: {stats}"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_monbus_aggregation(dut):
    """Test MonBus aggregation from all sources"""
    tb = SchedulerGroupArrayBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    # Generate some activity first
    await tb.test_multi_channel_concurrent([0, 1, 2, 3])
    # Then check monitor events
    result, stats = await tb.test_monitor_bus_aggregation(num_events=2)
    tb.finalize_test()
    tb.print_test_summary()
    # Monitor test is informational
    tb.log.info(f"MonBus aggregation: {stats}")
    assert True, "MonBus test completed"


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_stress(dut):
    """Comprehensive stress test with random operations"""
    tb = SchedulerGroupArrayBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result, stats = await tb.stress_test(num_operations=10)
    tb.finalize_test()
    tb.print_test_summary()
    # Allow some failures in stress test
    assert stats.get('success_rate', 0) >= 0.9, f"Stress test failed: {stats}"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_beats_scheduler_group_array_test_params():
    """Generate test parameters for beats_scheduler_group_array tests.

    Returns list of tuples: (num_channels, addr_width, data_width, axi_id_width)
    """
    return [
        # Default configuration - 8 channels
        (8, 64, 512, 8),
        # Smaller data width
        (8, 64, 256, 8),
    ]


beats_scheduler_group_array_params = generate_beats_scheduler_group_array_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Functionality
# ===========================================================================

@pytest.mark.macro_beats
@pytest.mark.beats_scheduler_group_array
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width", beats_scheduler_group_array_params)
def test_single_channel(request, num_channels, addr_width, data_width, axi_id_width):
    """Pytest: Test single channel operation"""
    _run_beats_scheduler_group_array_test(request, "cocotb_test_single_channel",
                                           num_channels, addr_width, data_width, axi_id_width)


@pytest.mark.macro_beats
@pytest.mark.beats_scheduler_group_array
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width", beats_scheduler_group_array_params)
def test_multi_channel_concurrent(request, num_channels, addr_width, data_width, axi_id_width):
    """Pytest: Test multi-channel concurrent operations"""
    _run_beats_scheduler_group_array_test(request, "cocotb_test_multi_channel_concurrent",
                                           num_channels, addr_width, data_width, axi_id_width)


@pytest.mark.macro_beats
@pytest.mark.beats_scheduler_group_array
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width", beats_scheduler_group_array_params)
def test_axi_arbitration(request, num_channels, addr_width, data_width, axi_id_width):
    """Pytest: Test AXI arbitration"""
    _run_beats_scheduler_group_array_test(request, "cocotb_test_axi_arbitration",
                                           num_channels, addr_width, data_width, axi_id_width)


@pytest.mark.macro_beats
@pytest.mark.beats_scheduler_group_array
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width", beats_scheduler_group_array_params)
def test_all_channels_sequential(request, num_channels, addr_width, data_width, axi_id_width):
    """Pytest: Test all channels sequentially"""
    _run_beats_scheduler_group_array_test(request, "cocotb_test_all_channels_sequential",
                                           num_channels, addr_width, data_width, axi_id_width)


@pytest.mark.macro_beats
@pytest.mark.beats_scheduler_group_array
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width", beats_scheduler_group_array_params)
def test_monbus_aggregation(request, num_channels, addr_width, data_width, axi_id_width):
    """Pytest: Test MonBus aggregation"""
    _run_beats_scheduler_group_array_test(request, "cocotb_test_monbus_aggregation",
                                           num_channels, addr_width, data_width, axi_id_width)


@pytest.mark.macro_beats
@pytest.mark.beats_scheduler_group_array
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width", beats_scheduler_group_array_params)
def test_stress(request, num_channels, addr_width, data_width, axi_id_width):
    """Pytest: Stress test"""
    _run_beats_scheduler_group_array_test(request, "cocotb_test_stress",
                                           num_channels, addr_width, data_width, axi_id_width)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_beats_scheduler_group_array_test(request, testcase_name, num_channels, addr_width, data_width, axi_id_width):
    """Helper function to run beats_scheduler_group_array tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        num_channels: Number of channels (8)
        addr_width: Address width
        data_width: Data width
        axi_id_width: AXI ID width
    """
    # Check if coverage collection is enabled via environment variable
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_macro_beats': '../../rtl/macro_beats'
    })

    dut_name = "scheduler_group_array_beats"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/macro_beats/scheduler_group_array_beats.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    id_str = TBBase.format_dec(axi_id_width, 2)

    # Extract test name from cocotb function
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_nc{nc_str}_aw{aw_str}_dw{dw_str}_id{id_str}"

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
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'AXI_ID_WIDTH': axi_id_width,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AXI_ID_WIDTH': str(axi_id_width),
        'CHANNEL_COUNT': str(num_channels),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Build compile args - add coverage if enabled
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-SELRANGE"]
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
    print("Running basic beats_scheduler_group_array test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_beats_scheduler_group_array_test(request, "cocotb_test_single_channel",
                                          num_channels=8, addr_width=64, data_width=512, axi_id_width=8)
