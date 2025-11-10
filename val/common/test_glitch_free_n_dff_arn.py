# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_glitch_free_n_dff_arn
# Purpose: Test runner for glitch_free_n_dff_arn module
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test runner for glitch_free_n_dff_arn module

The glitch_free_n_dff_arn is a parameterized N-stage synchronizer for safe
clock domain crossing. It reduces metastability risk by passing signals
through multiple flip-flop stages.

Test Configurations:
- FLOP_COUNT=2, WIDTH=1: Minimal synchronizer (2-FF sync for single bit)
- FLOP_COUNT=3, WIDTH=4: Standard 3-stage sync for nibble
- FLOP_COUNT=4, WIDTH=8: Conservative 4-stage sync for byte
- FLOP_COUNT=3, WIDTH=16: Standard sync for word
- FLOP_COUNT=5, WIDTH=32: Extra-safe 5-stage sync for double-word

Each test verifies:
- Propagation delay matches FLOP_COUNT parameter
- Continuous data stream handling
- Reset behavior (clears all stages)
- All bit patterns (small widths)
- Data stability (stable input → stable output)

Author: RTL Design Sherpa Project
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.glitch_free_n_dff_arn_tb import GlitchFreeNDffArnTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_glitch_free_n_dff_test(dut):
    """Main glitch_free_n_dff_arn test function"""
    tb = GlitchFreeNDffArnTB(dut)
    await tb.setup_clocks_and_reset()
    passed = await tb.run_all_tests()
    assert passed, "glitch_free_n_dff_arn test failed"

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_test_params():
    """Generate test parameter combinations"""
    return [
        # (FLOP_COUNT, WIDTH, test_mode)
        (2, 1, 'minimal'),      # Minimal 2-FF sync for single bit
        (3, 4, 'standard'),     # Standard 3-stage for nibble
        (4, 8, 'conservative'), # Conservative 4-stage for byte
        (3, 16, 'word'),        # Standard sync for word
        (5, 32, 'safe'),        # Extra-safe 5-stage for double-word
    ]

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("flop_count, width, test_mode", generate_test_params())
def test_glitch_free_n_dff_arn(request, flop_count, width, test_mode):
    """
    Glitch-free N-DFF synchronizer test runner

    Tests parameterized N-stage synchronizer:
    - Propagation delay verification
    - Continuous data stream
    - Reset behavior
    - Data stability
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "glitch_free_n_dff_arn"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/glitch_free_n_dff_arn.f'
    )

    # Format parameters for unique test name
    fc_str = TBBase.format_dec(flop_count, 1)
    w_str = TBBase.format_dec(width, 2)
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_{dut_name}_fc{fc_str}_w{w_str}_{test_mode}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'FLOP_COUNT': flop_count,
        'WIDTH': width,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'PARAM_FLOP_COUNT': str(flop_count),
        'PARAM_WIDTH': str(width),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_glitch_free_n_dff_test",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
            sim_args=[],
            plusargs=[],
            includes=includes,  # From filelist via get_sources_from_filelist()
        )
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
