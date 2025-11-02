# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_descriptor_engine
# Purpose: STREAM Descriptor Engine Test Runner - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19

"""
STREAM Descriptor Engine Test Runner - v1.0

Three-section test pattern (CocoTB functions, parameters, pytest wrappers).
Tests APB→AXI→Descriptor flow only (no RDA/CDA interfaces in STREAM).
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
from tbclasses.descriptor_engine_tb import DescriptorEngineTB, DelayProfile

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# SECTION 1: COCOTB TEST FUNCTIONS - prefix with "cocotb_"
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_apb_basic(dut):
    """Test basic APB→AXI→Descriptor flow."""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()  # Mandatory init
    await tb.initialize_test()
    result = await tb.run_apb_basic_test(num_requests=5)
    report_pass = tb.generate_final_report()
    assert result and report_pass, "APB basic test failed"

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_apb_with_delays(dut):
    """Test APB with various delay profiles."""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Test with minimal delay profile
    result = await tb.run_test_with_profile(num_packets=10, profile=DelayProfile.MINIMAL_DELAY)
    report_pass = tb.generate_final_report()
    assert result and report_pass, "APB minimal delay test failed"

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_apb_fast_producer(dut):
    """Test APB with fast producer profile."""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.run_test_with_profile(num_packets=8, profile=DelayProfile.FAST_PRODUCER)
    report_pass = tb.generate_final_report()
    assert result and report_pass, "APB fast producer test failed"

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_apb_backpressure(dut):
    """Test APB with backpressure."""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.run_test_with_profile(num_packets=8, profile=DelayProfile.BACKPRESSURE)
    report_pass = tb.generate_final_report()
    assert result and report_pass, "APB backpressure test failed"

# ===========================================================================
# SECTION 2: PARAMETER GENERATION
# ===========================================================================

def generate_descriptor_engine_test_params():
    """Generate test parameters for descriptor engine tests."""
    return [
        # (channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth)
        (0, 8, 64, 512, 8, 8),  # Standard STREAM configuration
    ]

descriptor_engine_params = generate_descriptor_engine_test_params()

# ===========================================================================
# SECTION 3: PYTEST WRAPPER FUNCTIONS
# ===========================================================================

def run_descriptor_engine_test(test_name, channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth):
    """Common test runner for descriptor engine tests"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_stream_includes': '../../../../rtl/includes'
    })

    dut_name = "descriptor_engine"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/descriptor_engine.f'
    )

    # Format parameters for unique test name
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 4)
    aid_str = TBBase.format_dec(axi_id_width, 2)
    fd_str = TBBase.format_dec(fifo_depth, 2)
    test_name_plus_params = f"{test_name}_{dut_name}_cid{cid_str}_nc{nc_str}_aw{aw_str}_dw{dw_str}_aid{aid_str}_fd{fd_str}"

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
        'AXI_ID_WIDTH': axi_id_width,
        'FIFO_DEPTH': fifo_depth,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'STREAM_CHANNEL_ID': str(channel_id),
        'STREAM_NUM_CHANNELS': str(num_channels),
        'STREAM_ADDR_WIDTH': str(addr_width),
        'STREAM_DATA_WIDTH': str(data_width),
        'STREAM_AXI_ID_WIDTH': str(axi_id_width),
        'STREAM_FIFO_DEPTH': str(fifo_depth),
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

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth", descriptor_engine_params)
def test_apb_basic(request, channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth):
    """Descriptor engine APB basic test."""
    run_descriptor_engine_test("test_apb_basic", channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth)

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth", descriptor_engine_params)
def test_apb_with_delays(request, channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth):
    """Descriptor engine APB with delays test."""
    run_descriptor_engine_test("test_apb_with_delays", channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth)

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth", descriptor_engine_params)
def test_apb_fast_producer(request, channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth):
    """Descriptor engine APB fast producer test."""
    run_descriptor_engine_test("test_apb_fast_producer", channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth)

@pytest.mark.parametrize("channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth", descriptor_engine_params)
def test_apb_backpressure(request, channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth):
    """Descriptor engine APB backpressure test."""
    run_descriptor_engine_test("test_apb_backpressure", channel_id, num_channels, addr_width, data_width, axi_id_width, fifo_depth)
