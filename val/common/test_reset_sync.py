# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_reset_sync
# Purpose: Reset Synchronizer Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Reset Synchronizer Test Runner

Tests the reset_sync module with various synchronization depths.
"""

import os
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.reset_sync_tb import ResetSyncTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=100, timeout_unit="us")
async def reset_sync_test(dut):
    """Main test function"""
    tb = ResetSyncTB(dut)
    await tb.start_clock('clk', 10, 'ns')

    # Run comprehensive test suite
    passed = await tb.run_all_tests()

    assert passed, "reset_sync test failed"


def generate_test_params():
    """Generate test parameter combinations"""
    # Test with different synchronization depths
    return [
        (2, 'min'),      # Minimum practical depth
        (3, 'typical'),  # Standard depth
        (4, 'safe'),     # Conservative depth
        (5, 'max'),      # Maximum tested depth
    ]


@pytest.mark.parametrize("n, test_mode", generate_test_params())
def test_reset_sync(n, test_mode):
    """
    Reset synchronizer test runner

    Args:
        n: Number of synchronization stages
        test_mode: Test configuration name
    """

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common',
    })

    dut_name = "reset_sync"
    test_name = f"test_reset_sync_n{n}_{test_mode}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources = [
        os.path.join(rtl_dict['rtl_common'], "reset_sync.sv"),
    ]

    rtl_parameters = {
        'N': str(n),
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'PARAM_N': str(n),
    }

    compile_args = [
        "-Wall", "-Wno-UNUSED", "-Wno-DECLFILENAME",
    ]

    print(f"\n{'='*80}")
    print(f"Reset Sync Test: {test_mode} (N={n})")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ PASSED: {test_name}")
    except Exception as e:
        print(f"✗ FAILED: {test_name}")
        print(f"Error: {str(e)}")
        print(f"Log: {log_path}")
        raise


if __name__ == "__main__":
    # Run with pytest
    pytest.main([__file__, "-v"])
