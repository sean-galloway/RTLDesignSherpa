# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_beats_alloc_ctrl
# Purpose: RAPIDS Beats Allocation Control FUB Validation Test - Phase 1
#
# Documentation: projects/components/dmas/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Allocation Control FUB Validation Test - Phase 1

Test suite for the beats_alloc_ctrl module (Virtual FIFO for space tracking).

Features tested:
- Space allocation (variable-size requests)
- Data write acknowledgment (single-beat releases)
- Full/empty detection
- Space tracking accuracy

This test file imports the reusable AllocCtrlBeatsTB class from:
  projects/components/dmas/rapids/dv/tbclasses/alloc_ctrl_beats_tb.py

STRUCTURE FOLLOWS AMBA PATTERN:
  - CocoTB test functions at top (prefixed with cocotb_)
  - Parameter generation at bottom
  - Pytest wrappers at bottom with @pytest.mark.parametrize
"""

import os
import random
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from projects.components.dmas.rapids.dv.tbclasses.rapids_levels import depth as _profile_depth

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import TB class from PROJECT AREA (not framework!)
from projects.components.dmas.rapids.dv.tbclasses.alloc_ctrl_beats_tb import AllocCtrlBeatsTB


# ===========================================================================
# BASIC FUNCTIONALITY TESTS
# ===========================================================================
# NOTE: These cocotb test functions are prefixed with "cocotb_" to prevent pytest
# from collecting them directly. They are only run via the pytest wrappers below.

def _depth():
    """(basic ops, stress ops) by TEST_LEVEL."""
    return (_profile_depth('alloc_basic_ops'), _profile_depth('alloc_stress_ops'))


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_alloc_drain(dut):
    """Test basic allocation and drain cycle"""
    tb = AllocCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_basic_alloc_drain(num_ops=_depth()[0])
    tb.generate_test_report()
    assert result, "Basic alloc/drain test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_full_detection(dut):
    """Test full flag detection"""
    tb = AllocCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_full_detection()
    tb.generate_test_report()
    assert result, "Full detection test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_empty_detection(dut):
    """Test empty flag detection"""
    tb = AllocCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_empty_detection()
    tb.generate_test_report()
    assert result, "Empty detection test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_variable_size_alloc(dut):
    """Test variable-size allocations"""
    tb = AllocCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_variable_size_alloc()
    tb.generate_test_report()
    assert result, "Variable size allocation test failed"


# ===========================================================================
# STRESS TESTS
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_stress_rapid_operations(dut):
    """Stress test with rapid operations"""
    tb = AllocCtrlBeatsTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_stress_rapid_operations(num_ops=_depth()[1])
    tb.generate_test_report()
    assert result, "Stress test failed"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_beats_alloc_ctrl_test_params():
    """(depth, almost_wr_margin, almost_rd_margin, timing_profile) by REG_LEVEL.

    GATE: the primary config, back-to-back timing
    FUNC: three configs + two GAXI delay profiles on the primary config
    FULL: three configs + the full five-profile sweep on the primary config
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    configs = [(512, 1, 1), (128, 1, 1), (256, 4, 4)]
    if reg_level == 'GATE':
        configs = configs[:1]
        profiles = []
    elif reg_level == 'FUNC':
        profiles = ['slow_producer', 'gaxi_backpressure']
    else:
        profiles = ['constrained', 'slow_producer', 'gaxi_backpressure', 'gaxi_stress', 'gaxi_realistic']
    params = [cfg + ('default',) for cfg in configs]
    params += [configs[0] + (p,) for p in profiles]
    return params


beats_alloc_ctrl_params = generate_beats_alloc_ctrl_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Functionality
# ===========================================================================

@pytest.mark.fub
@pytest.mark.beats_alloc_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin, timing_profile", beats_alloc_ctrl_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alloc_ctrl_beats_basic_alloc_drain(request, depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level):
    """Pytest: Test basic allocation and drain cycle"""
    _run_beats_alloc_ctrl_test(request, "cocotb_test_basic_alloc_drain",
                                depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level=test_level)


@pytest.mark.fub
@pytest.mark.beats_alloc_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin, timing_profile", beats_alloc_ctrl_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alloc_ctrl_beats_full_detection(request, depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level):
    """Pytest: Test full flag detection"""
    _run_beats_alloc_ctrl_test(request, "cocotb_test_full_detection",
                                depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level=test_level)


@pytest.mark.fub
@pytest.mark.beats_alloc_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin, timing_profile", beats_alloc_ctrl_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alloc_ctrl_beats_empty_detection(request, depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level):
    """Pytest: Test empty flag detection"""
    _run_beats_alloc_ctrl_test(request, "cocotb_test_empty_detection",
                                depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level=test_level)


@pytest.mark.fub
@pytest.mark.beats_alloc_ctrl
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin, timing_profile", beats_alloc_ctrl_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alloc_ctrl_beats_variable_size(request, depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level):
    """Pytest: Test variable-size allocations"""
    _run_beats_alloc_ctrl_test(request, "cocotb_test_variable_size_alloc",
                                depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level=test_level)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Stress Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.beats_alloc_ctrl
@pytest.mark.stress
@pytest.mark.parametrize("depth, almost_wr_margin, almost_rd_margin, timing_profile", beats_alloc_ctrl_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_alloc_ctrl_beats_stress(request, depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level):
    """Pytest: Stress test with rapid operations"""
    _run_beats_alloc_ctrl_test(request, "cocotb_test_stress_rapid_operations",
                                depth, almost_wr_margin, almost_rd_margin, timing_profile, test_level=test_level)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_beats_alloc_ctrl_test(request, testcase_name, depth, almost_wr_margin, almost_rd_margin, timing_profile='default', test_level='gate'):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Helper function to run beats_alloc_ctrl tests with AMBA pattern.

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

    # DV wrapper, not the bare module: the rd side is a payload-less
    # handshake and a GAXI producer must bind one payload field, so the
    # wrapper supplies an unused rd_pad for the BFM to drive.
    dut_name = "alloc_ctrl_beats_tb_top"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dmas/rapids/dv/tb/alloc_ctrl_beats_tb_top.f'
    )

    # Format parameters for unique test name (AMBA pattern with TBBase.format_dec())
    depth_str = TBBase.format_dec(depth, 4)
    aw_str = TBBase.format_dec(almost_wr_margin, 2)
    ar_str = TBBase.format_dec(almost_rd_margin, 2)

    # Extract test name from cocotb function (remove "cocotb_test_" prefix)
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_d{depth_str}_aw{aw_str}_ar{ar_str}_{timing_profile}_{test_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
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
        **level_env(test_level),
        'TEST_DEPTH': str(depth),
    }

    # GAXI BFM delay-profile sweep ('default' leaves the TB default 'backtoback').
    if timing_profile != 'default':
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

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
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            plus_args=['--trace'] if enable_waves else [],
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
    print("Running basic beats_alloc_ctrl test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_beats_alloc_ctrl_test(request, "cocotb_test_basic_alloc_drain",
                               depth=512, almost_wr_margin=1, almost_rd_margin=1)
