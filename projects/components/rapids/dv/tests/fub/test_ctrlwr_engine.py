# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ctrlwr_engine
# Purpose: RAPIDS Control Write Engine FUB Validation Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Control Write Engine FUB Validation Test

Test suite for the RAPIDS ctrlwr_engine module which handles post-descriptor
control write operations.

Features Tested:
- Basic control write operation
- Null address handling (skip operation)
- Address alignment validation
- AXI response error handling
- Back-to-back operations

This test file imports the reusable CtrlwrEngineTB class from:
  projects/components/rapids/dv/tbclasses/ctrlwr_engine_tb.py

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

# Import TB class from PROJECT AREA (not framework!)
from projects.components.rapids.dv.tbclasses.ctrlwr_engine_tb import CtrlwrEngineTB, DelayProfile, TestScenario


# ===========================================================================
# BASIC OPERATION TESTS
# ===========================================================================
# NOTE: These cocotb test functions are prefixed with "cocotb_" to prevent pytest
# from collecting them directly. They are only run via the pytest wrappers below.

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_write(dut):
    """Test basic control write operation"""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_basic_write(DelayProfile.FIXED_DELAY)
    assert result, "Basic write test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_null_address(dut):
    """Test null address handling (skip operation)"""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_null_address(DelayProfile.FIXED_DELAY)
    assert result, "Null address test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_back_to_back(dut):
    """Test back-to-back control write operations"""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_back_to_back(DelayProfile.FIXED_DELAY, num_operations=5)
    assert result, "Back-to-back test failed"


# ===========================================================================
# ERROR HANDLING TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_axi_error(dut):
    """Test AXI error response handling"""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_axi_error(DelayProfile.FIXED_DELAY)
    assert result, "AXI error test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_channel_reset(dut):
    """Test channel reset functionality"""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_channel_reset(DelayProfile.FIXED_DELAY)
    assert result, "Channel reset test failed"


# ===========================================================================
# MIXED SCENARIO TESTS
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_mixed_scenarios(dut):
    """Test mixed scenarios with various timing profiles"""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()
    result = await tb.test_mixed_scenarios()
    assert result, "Mixed scenarios test failed"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_ctrlwr_test_params():
    """Generate test parameters for ctrlwr_engine tests.

    Returns list of tuples: (channel_id, num_channels, addr_width)
    """
    return [
        # Standard configuration
        (0, 8, 64),
    ]


ctrlwr_params = generate_ctrlwr_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Operation Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.ctrlwr
@pytest.mark.parametrize("channel_id, num_channels, addr_width", ctrlwr_params)
def test_ctrlwr_basic_write(request, channel_id, num_channels, addr_width):
    """Pytest: Test basic control write operation"""
    _run_ctrlwr_test(request, "cocotb_test_basic_write",
                     channel_id, num_channels, addr_width)


@pytest.mark.fub
@pytest.mark.ctrlwr
@pytest.mark.parametrize("channel_id, num_channels, addr_width", ctrlwr_params)
def test_ctrlwr_null_address(request, channel_id, num_channels, addr_width):
    """Pytest: Test null address handling"""
    _run_ctrlwr_test(request, "cocotb_test_null_address",
                     channel_id, num_channels, addr_width)


@pytest.mark.fub
@pytest.mark.ctrlwr
@pytest.mark.parametrize("channel_id, num_channels, addr_width", ctrlwr_params)
def test_ctrlwr_back_to_back(request, channel_id, num_channels, addr_width):
    """Pytest: Test back-to-back operations"""
    _run_ctrlwr_test(request, "cocotb_test_back_to_back",
                     channel_id, num_channels, addr_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Error Handling
# ===========================================================================

@pytest.mark.fub
@pytest.mark.ctrlwr
@pytest.mark.error
@pytest.mark.xfail(reason="RTL bug: w_axi_response_error checks r_write_resp (old value) before b_resp is latched")
@pytest.mark.parametrize("channel_id, num_channels, addr_width", ctrlwr_params)
def test_ctrlwr_axi_error(request, channel_id, num_channels, addr_width):
    """Pytest: Test AXI error handling"""
    _run_ctrlwr_test(request, "cocotb_test_axi_error",
                     channel_id, num_channels, addr_width)


@pytest.mark.fub
@pytest.mark.ctrlwr
@pytest.mark.parametrize("channel_id, num_channels, addr_width", ctrlwr_params)
def test_ctrlwr_channel_reset(request, channel_id, num_channels, addr_width):
    """Pytest: Test channel reset functionality"""
    _run_ctrlwr_test(request, "cocotb_test_channel_reset",
                     channel_id, num_channels, addr_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Mixed Scenarios
# ===========================================================================

@pytest.mark.fub
@pytest.mark.ctrlwr
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, addr_width", ctrlwr_params)
def test_ctrlwr_mixed_scenarios(request, channel_id, num_channels, addr_width):
    """Pytest: Test mixed scenarios"""
    _run_ctrlwr_test(request, "cocotb_test_mixed_scenarios",
                     channel_id, num_channels, addr_width)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_ctrlwr_test(request, testcase_name, channel_id, num_channels, addr_width):
    """Helper function to run ctrlwr_engine tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        channel_id: Channel ID for this test
        num_channels: Total number of channels
        addr_width: Address width in bits
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub': '../../rtl/fub'
    })

    dut_name = "ctrlwr_engine"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub/ctrlwr_engine.f'
    )

    # Format parameters for unique test name (AMBA pattern with TBBase.format_dec())
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 2)

    # Extract test name from cocotb function (remove "cocotb_test_" prefix)
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_cid{cid_str}_nc{nc_str}_aw{aw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    chan_width = (num_channels - 1).bit_length() if num_channels > 1 else 1
    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'CHAN_WIDTH': chan_width,
        'ADDR_WIDTH': addr_width,
        'AXI_ID_WIDTH': 8,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345),
        'CHANNEL_ID': str(channel_id),
        'NUM_CHANNELS': str(num_channels),
        'ADDR_WIDTH': str(addr_width),
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
            waves=os.environ.get('WAVES', '0') == '1',
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
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
    # Run basic write test when executed directly
    print("Running basic write test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_ctrlwr_test(request, "cocotb_test_basic_write",
                     channel_id=0, num_channels=8, addr_width=64)
