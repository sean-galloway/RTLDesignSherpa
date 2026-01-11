# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_descriptor_engine
# Purpose: RAPIDS Descriptor Engine FUB Validation Test - Phase 1 (STREAM-based)
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Descriptor Engine FUB Validation Test - Phase 1 (STREAM-based)

Test suite for the RAPIDS Phase 1 descriptor engine module with autonomous chaining.

RAPIDS Phase 1 Features (tested here):
- APB programming interface → AXI read → Descriptor output
- Autonomous chaining via next_descriptor_ptr
- Two-FIFO architecture (address FIFO + descriptor FIFO)
- Address range validation (two configurable ranges)
- Channel reset support
- Monitor bus event reporting

NOT in Phase 1 (NOT tested):
- CDA packet reception (removed from descriptor_engine.sv)
- Variable data width (descriptors are fixed 256-bit)

This test file imports the reusable DescriptorEngineTB class from:
  projects/components/rapids/dv/tbclasses/descriptor_engine_tb.py (PROJECT AREA)

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
from projects.components.rapids.dv.tbclasses.descriptor_engine_tb import DescriptorEngineTB


# ===========================================================================
# BASIC DESCRIPTOR FLOW TESTS
# ===========================================================================
# NOTE: These cocotb test functions are prefixed with "cocotb_" to prevent pytest
# from collecting them directly. They are only run via the pytest wrappers below.

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_descriptor_flow(dut):
    """Test basic APB → AXI → Descriptor output flow"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_basic_descriptor_flow(num_descriptors=5)
    tb.generate_test_report()
    assert result, "Basic descriptor flow test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_descriptor_chaining(dut):
    """Test autonomous descriptor chaining via next_descriptor_ptr"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_descriptor_chaining(chain_length=3)
    tb.generate_test_report()
    assert result, "Descriptor chaining test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_address_range_validation(dut):
    """Test address range validation (two configurable ranges)"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_address_range_validation()
    tb.generate_test_report()
    assert result, "Address range validation test failed"


# ===========================================================================
# CHANNEL RESET AND ERROR HANDLING TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_channel_reset(dut):
    """Test channel reset functionality"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_channel_reset()
    tb.generate_test_report()
    assert result, "Channel reset test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_invalid_descriptor(dut):
    """Test handling of invalid descriptor (valid bit = 0)"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_invalid_descriptor()
    tb.generate_test_report()
    assert result, "Invalid descriptor test failed"


# ===========================================================================
# MONITOR BUS TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_monitor_bus_events(dut):
    """Test monitor bus event generation"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_monitor_bus_events()
    tb.generate_test_report()
    assert result, "Monitor bus events test failed"


# ===========================================================================
# STRESS TESTS
# ===========================================================================

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_rapid_descriptors(dut):
    """Test rapid back-to-back descriptor requests"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    # Test 20 rapid descriptors
    result = await tb.test_basic_descriptor_flow(num_descriptors=20)
    tb.generate_test_report()
    assert result, "Rapid descriptors test failed"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_long_chain(dut):
    """Test long descriptor chain (5 descriptors)"""
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_descriptor_chaining(chain_length=5)
    tb.generate_test_report()
    assert result, "Long chain test failed"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_descriptor_engine_test_params():
    """Generate test parameters for descriptor engine tests.

    Returns list of tuples: (channel_id, num_channels, axi_id_width)
    """
    return [
        # Standard configuration
        (0, 32, 8),
        # Fewer channels
        (0, 16, 8),
        # Minimal channels
        (0, 8, 8),
    ]


descriptor_engine_params = generate_descriptor_engine_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Flow Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_basic_flow(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test basic descriptor flow"""
    _run_descriptor_engine_test(request, "cocotb_test_basic_descriptor_flow",
                                channel_id, num_channels, axi_id_width)


@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_descriptor_chaining(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test autonomous descriptor chaining"""
    _run_descriptor_engine_test(request, "cocotb_test_descriptor_chaining",
                                channel_id, num_channels, axi_id_width)


@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_address_range_validation(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test address range validation"""
    _run_descriptor_engine_test(request, "cocotb_test_address_range_validation",
                                channel_id, num_channels, axi_id_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Reset and Error Handling
# ===========================================================================

@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_channel_reset(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test channel reset functionality"""
    _run_descriptor_engine_test(request, "cocotb_test_channel_reset",
                                channel_id, num_channels, axi_id_width)


@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.error
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_invalid_descriptor(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test invalid descriptor handling"""
    _run_descriptor_engine_test(request, "cocotb_test_invalid_descriptor",
                                channel_id, num_channels, axi_id_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Monitor Bus Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_monitor_bus_events(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test monitor bus event generation"""
    _run_descriptor_engine_test(request, "cocotb_test_monitor_bus_events",
                                channel_id, num_channels, axi_id_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Stress Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_rapid_descriptors(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test rapid back-to-back descriptors"""
    _run_descriptor_engine_test(request, "cocotb_test_rapid_descriptors",
                                channel_id, num_channels, axi_id_width)


@pytest.mark.fub
@pytest.mark.descriptor_engine
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, axi_id_width", descriptor_engine_params)
def test_long_chain(request, channel_id, num_channels, axi_id_width):
    """Pytest: Test long descriptor chain"""
    _run_descriptor_engine_test(request, "cocotb_test_long_chain",
                                channel_id, num_channels, axi_id_width)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_descriptor_engine_test(request, testcase_name, channel_id, num_channels, axi_id_width):
    """Helper function to run descriptor engine tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        channel_id: Channel ID for this test
        num_channels: Total number of channels
        axi_id_width: AXI ID width
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub_beats': '../../rtl/fub_beats'
    })

    dut_name = "descriptor_engine_beats"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub_beats/descriptor_engine_beats.f'
    )

    # Format parameters for unique test name (AMBA pattern with TBBase.format_dec())
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    iw_str = TBBase.format_dec(axi_id_width, 2)

    # Extract test name from cocotb function (remove "cocotb_test_" prefix)
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_cid{cid_str}_nc{nc_str}_iw{iw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Calculate CHAN_WIDTH
    chan_width = (num_channels - 1).bit_length() if num_channels > 1 else 1

    # RTL parameters for Phase 1 descriptor engine
    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'CHAN_WIDTH': chan_width,
        'ADDR_WIDTH': 64,
        'AXI_ID_WIDTH': axi_id_width,
        'FIFO_DEPTH': 8,
        'DESC_ADDR_FIFO_DEPTH': 2,
        'TIMEOUT_CYCLES': 1000,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345),
        'TEST_NUM_CHANNELS': str(num_channels),
        'TEST_ADDR_WIDTH': '64',
        'TEST_AXI_ID_WIDTH': str(axi_id_width),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

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
            compile_args=["-Wno-TIMESCALEMOD"],
        )
        print(f"✓ Test completed! Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"  View command: {cmd_filename}")
    except Exception as e:
        print(f"✗ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Run basic flow test when executed directly
    print("Running basic descriptor flow test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_descriptor_engine_test(request, "cocotb_test_basic_descriptor_flow",
                               channel_id=0, num_channels=32, axi_id_width=8)
