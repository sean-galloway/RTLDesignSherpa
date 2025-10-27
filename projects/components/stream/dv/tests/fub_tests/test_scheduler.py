# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler
# Purpose: STREAM Scheduler Test Runner - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19

"""
STREAM Scheduler Test Runner - v1.0

Three-section test pattern (CocoTB functions, parameters, pytest wrappers).
"""

import os
import sys

# Setup Python path BEFORE any other imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
stream_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))

# Remove if already in path
if stream_dv_path in sys.path:
    sys.path.remove(stream_dv_path)
if repo_root in sys.path:
    sys.path.remove(repo_root)

# Add to path (stream_dv_path FIRST so tbclasses is found)
sys.path.insert(0, stream_dv_path)
sys.path.insert(0, repo_root)

import pytest
import cocotb
from cocotb_test.simulator import run

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from tbclasses.scheduler_tb import SchedulerTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# SECTION 1: COCOTB TEST FUNCTIONS - prefix with "cocotb_"
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_basic_flow(dut):
    """Test basic descriptor flow."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()  # Mandatory init
    await tb.initialize_test()
    result = await tb.test_basic_descriptor_flow(num_descriptors=5)
    tb.generate_test_report()
    assert result, "Basic descriptor flow test failed"

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_descriptor_chaining(dut):
    """Test descriptor chaining."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_descriptor_chaining(chain_length=3)
    tb.generate_test_report()
    assert result, "Descriptor chaining test failed"

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_descriptor_error(dut):
    """Test descriptor error handling."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_descriptor_error()
    tb.generate_test_report()
    assert result, "Descriptor error test failed"

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_read_engine_error(dut):
    """Test read engine error handling."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_read_engine_error()
    tb.generate_test_report()
    assert result, "Read engine error test failed"

@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_timeout_detection(dut):
    """Test timeout detection."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_timeout_detection()
    tb.generate_test_report()
    assert result, "Timeout detection test failed"

# ===========================================================================
# SECTION 2: PARAMETER GENERATION
# ===========================================================================

def generate_scheduler_test_params():
    """Generate test parameters for scheduler tests."""
    return [
        # (channel_id, num_channels, addr_width, data_width, timeout_cycles)
        (0, 8, 64, 512, 1000),  # Standard STREAM configuration
    ]

scheduler_params = generate_scheduler_test_params()

# ===========================================================================
# SECTION 3: PYTEST WRAPPER FUNCTIONS
# ===========================================================================

def run_scheduler_test(test_name, channel_id, num_channels, addr_width, data_width, timeout_cycles):
    """Common test runner for scheduler tests"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_stream_includes': '../../../../rtl/includes'
    })

    dut_name = "scheduler"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/scheduler.f'
    )

    # Format parameters for unique test name
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 4)
    tc_str = TBBase.format_dec(timeout_cycles, 5)
    test_name_plus_params = f"{test_name}_{dut_name}_cid{cid_str}_nc{nc_str}_aw{aw_str}_dw{dw_str}_tc{tc_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'TIMEOUT_CYCLES': timeout_cycles,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'STREAM_CHANNEL_ID': str(channel_id),
        'STREAM_NUM_CHANNELS': str(num_channels),
        'STREAM_ADDR_WIDTH': str(addr_width),
        'STREAM_DATA_WIDTH': str(data_width),
        'STREAM_TIMEOUT_CYCLES': str(timeout_cycles),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=dut_name,
            module=module,
            testcase=f"cocotb_{test_name}",  # ← cocotb function name
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
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, timeout_cycles", scheduler_params)
def test_basic_flow(request, channel_id, num_channels, addr_width, data_width, timeout_cycles):
    """Scheduler basic flow test."""
    run_scheduler_test("test_basic_flow", channel_id, num_channels, addr_width, data_width, timeout_cycles)

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, timeout_cycles", scheduler_params)
def test_descriptor_chaining(request, channel_id, num_channels, addr_width, data_width, timeout_cycles):
    """Scheduler descriptor chaining test."""
    run_scheduler_test("test_descriptor_chaining", channel_id, num_channels, addr_width, data_width, timeout_cycles)

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, timeout_cycles", scheduler_params)
def test_descriptor_error(request, channel_id, num_channels, addr_width, data_width, timeout_cycles):
    """Scheduler descriptor error test."""
    run_scheduler_test("test_descriptor_error", channel_id, num_channels, addr_width, data_width, timeout_cycles)

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, timeout_cycles", scheduler_params)
def test_read_engine_error(request, channel_id, num_channels, addr_width, data_width, timeout_cycles):
    """Scheduler read engine error test."""
    run_scheduler_test("test_read_engine_error", channel_id, num_channels, addr_width, data_width, timeout_cycles)

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, timeout_cycles", scheduler_params)
def test_timeout_detection(request, channel_id, num_channels, addr_width, data_width, timeout_cycles):
    """Scheduler timeout detection test."""
    run_scheduler_test("test_timeout_detection", channel_id, num_channels, addr_width, data_width, timeout_cycles)
