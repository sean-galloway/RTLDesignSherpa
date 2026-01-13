# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_beats_drain_ctrl
# Purpose: RAPIDS Beats Drain Control FUB Validation Test - Phase 1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Drain Control FUB Validation Test - Phase 1

Test suite for the beats_drain_ctrl module (Virtual FIFO for data availability tracking).

Features tested:
- Data write tracking (single-beat entries)
- Drain requests (variable-size requests)
- Full/empty detection
- Data availability tracking

This test file imports the reusable DrainCtrlBeatsTB class from:
  projects/components/rapids/dv/tbclasses/drain_ctrl_beats_tb.py

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
from projects.components.rapids.dv.tbclasses.drain_ctrl_beats_tb import DrainCtrlBeatsTB


# ===========================================================================
# BASIC FUNCTIONALITY TESTS
# ===========================================================================
# NOTE: These cocotb test functions are prefixed with "cocotb_" to prevent pytest
# from collecting them directly. They are only run via the pytest wrappers below.

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_write_drain(dut):
    """Test basic write and drain cycle"""
    tb = DrainCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_basic_write_drain(num_ops=10)
    tb.generate_test_report()
    assert result, "Basic write/drain test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_full_detection(dut):
    """Test full flag detection"""
    tb = DrainCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_full_detection()
    tb.generate_test_report()
    assert result, "Full detection test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_empty_detection(dut):
    """Test empty flag detection"""
    tb = DrainCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_empty_detection()
    tb.generate_test_report()
    assert result, "Empty detection test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_variable_size_drain(dut):
    """Test variable-size drains"""
    tb = DrainCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_variable_size_drain()
    tb.generate_test_report()
    assert result, "Variable size drain test failed"


# ===========================================================================
# STRESS TESTS
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_stress_rapid_operations(dut):
    """Stress test with rapid operations"""
    tb = DrainCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_stress_rapid_operations(num_ops=100)
    tb.generate_test_report()
    assert result, "Stress test failed"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_beats_drain_ctrl_test_params():
    """Generate test parameters for beats_drain_ctrl tests.

    Returns list of tuples: (depth, almost_wr_margin, almost_rd_margin)
    """
    return [
        # Standard configuration
        (512, 1, 1),
        # Smaller depth
        (128, 1, 1),
        # Larger margins
        (256, 4, 4),
    ]


beats_drain_ctrl_params = generate_beats_drain_ctrl_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Functionality
# ===========================================================================

@pytest.mark.fub
@pytest.mark.beats_drain_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin", beats_drain_ctrl_params)
def test_basic_write_drain(request, depth, almost_wr_margin, almost_rd_margin):
    """Pytest: Test basic write and drain cycle"""
    _run_beats_drain_ctrl_test(request, "cocotb_test_basic_write_drain",
                                depth, almost_wr_margin, almost_rd_margin)


@pytest.mark.fub
@pytest.mark.beats_drain_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin", beats_drain_ctrl_params)
def test_full_detection(request, depth, almost_wr_margin, almost_rd_margin):
    """Pytest: Test full flag detection"""
    _run_beats_drain_ctrl_test(request, "cocotb_test_full_detection",
                                depth, almost_wr_margin, almost_rd_margin)


@pytest.mark.fub
@pytest.mark.beats_drain_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin", beats_drain_ctrl_params)
def test_empty_detection(request, depth, almost_wr_margin, almost_rd_margin):
    """Pytest: Test empty flag detection"""
    _run_beats_drain_ctrl_test(request, "cocotb_test_empty_detection",
                                depth, almost_wr_margin, almost_rd_margin)


@pytest.mark.fub
@pytest.mark.beats_drain_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin", beats_drain_ctrl_params)
def test_variable_size(request, depth, almost_wr_margin, almost_rd_margin):
    """Pytest: Test variable-size drains"""
    _run_beats_drain_ctrl_test(request, "cocotb_test_variable_size_drain",
                                depth, almost_wr_margin, almost_rd_margin)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Stress Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.beats_drain_ctrl
@pytest.mark.stress
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin", beats_drain_ctrl_params)
def test_stress(request, depth, almost_wr_margin, almost_rd_margin):
    """Pytest: Stress test with rapid operations"""
    _run_beats_drain_ctrl_test(request, "cocotb_test_stress_rapid_operations",
                                depth, almost_wr_margin, almost_rd_margin)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_beats_drain_ctrl_test(request, testcase_name, depth, almost_wr_margin, almost_rd_margin):
    """Helper function to run beats_drain_ctrl tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        depth: FIFO depth
        almost_wr_margin: Almost full margin
        almost_rd_margin: Almost empty margin
    """
    # Check if coverage collection is enabled via environment variable
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub_beats': '../../rtl/fub_beats'
    })

    dut_name = "drain_ctrl_beats"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub_beats/drain_ctrl_beats.f'
    )

    # Format parameters for unique test name (AMBA pattern with TBBase.format_dec())
    depth_str = TBBase.format_dec(depth, 4)
    aw_str = TBBase.format_dec(almost_wr_margin, 2)
    ar_str = TBBase.format_dec(almost_rd_margin, 2)

    # Extract test name from cocotb function (remove "cocotb_test_" prefix)
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_d{depth_str}_aw{aw_str}_ar{ar_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Calculate address width
    addr_width = (depth - 1).bit_length()

    # RTL parameters
    rtl_parameters = {
        'DEPTH': depth,
        'ALMOST_WR_MARGIN': almost_wr_margin,
        'ALMOST_RD_MARGIN': almost_rd_margin,
        'REGISTERED': 1,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345),
        'TEST_DEPTH': str(depth),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Build compile args - add coverage if enabled
    compile_args = ["-Wno-TIMESCALEMOD"]
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
    print("Running basic beats_drain_ctrl test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_beats_drain_ctrl_test(request, "cocotb_test_basic_write_drain",
                               depth=512, almost_wr_margin=1, almost_rd_margin=1)
