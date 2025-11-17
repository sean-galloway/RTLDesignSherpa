# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_pit_8254
# Purpose: PIT 8254 Test Runner
#
# Documentation: projects/components/retro_legacy_blocks/rtl/pit_8254/README.md
# Subsystem: retro_legacy_blocks/pit_8254
#
# Created: 2025-11-06

"""
PIT 8254 Test Runner

Test runner for the APB 8254 PIT module with basic functionality testing.

Features:
- Parametrized testing with pytest
- Basic test level (mode 0 only for now)
- Environment variable configuration
- Integration with CocoTB framework
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
import sys
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.retro_legacy_blocks.dv.tbclasses.pit_8254.pit_tb import PITTB, PITRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.pit_8254.pit_tests_basic import PITBasicTests


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_pit_basic(dut):
    """Main test function for PIT module - basic tests"""
    tb = PITTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'PIT test with seed: {seed}')

    # Get test level from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Setup clocks and reset
    await tb.setup_clocks_and_reset()

    # Setup components after reset (SAME AS HPET)
    await tb.setup_components()

    tb.log.info(f"Starting {test_level.upper()} PIT test...")
    tb.log.info(f"Configuration: {tb.num_counters} counters")

    # Create test suite
    basic_tests = PITBasicTests(tb)

    # Run all tests
    results = []
    test_methods = [
        ('Register Access', basic_tests.test_register_access),
        ('PIT Enable/Disable', basic_tests.test_pit_enable_disable),
        ('Control Word Programming', basic_tests.test_control_word_programming),
        ('Counter Mode 0 Simple', basic_tests.test_counter_mode0_simple),
        ('Multiple Counters', basic_tests.test_multiple_counters),
        ('Status Register', basic_tests.test_status_register),
    ]

    for test_name, test_method in test_methods:
        tb.log.info(f"\n{'=' * 80}")
        tb.log.info(f"Running: {test_name}")
        tb.log.info(f"{'=' * 80}")
        result = await test_method()
        results.append((test_name, result))

    # Print summary
    tb.log.info("\n" + "=" * 80)
    tb.log.info("TEST SUMMARY")
    tb.log.info("=" * 80)

    passed_count = sum(1 for _, result in results if result)
    total_count = len(results)

    for test_name, result in results:
        status = "✓ PASSED" if result else "✗ FAILED"
        tb.log.info(f"{test_name:40s} {status}")

    tb.log.info(f"\nPassed: {passed_count}/{total_count}")

    # Overall result
    all_passed = all(result for _, result in results)

    if all_passed:
        tb.log.info("\n🎉 All PIT tests PASSED! 🎉")
    else:
        tb.log.error("\n❌ Some PIT tests FAILED ❌")

    assert all_passed, f"PIT test failed: {passed_count}/{total_count} tests passed"


def run_pit_test(testcase_name, num_counters, cdc_enable):
    """Helper function to run PIT 8254 tests with common setup."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_pit_8254"

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/pit_8254/filelists/apb_pit_8254.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_counters, 1)
    cdc_str = "cdc" if cdc_enable else "nocdc"
    test_name_plus_params = f"test_{dut_name}_{testcase_name}_nc{nc_str}_{cdc_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'NUM_COUNTERS': num_counters,
        'CDC_ENABLE': cdc_enable,
    }

    extra_env = {
        'SEED': str(random.randint(0, 2**32 - 1)),
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'basic'),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{test_name_plus_params}.xml'),
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
    }

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_apb_pit_8254', test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module='test_apb_pit_8254',
            testcase=f"cocotb_{testcase_name}",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
                "--timescale", "1ns/1ps",
                "-Wno-WIDTHTRUNC",
                "-Wno-WIDTHEXPAND",
                "-Wno-CASEINCOMPLETE",
                "-Wno-BLKANDNBLK",
                "-Wno-MULTIDRIVEN",
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
        print(f"✓ {testcase_name} completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ {testcase_name} failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise


@pytest.mark.parametrize("num_counters, cdc_enable", [
    (3, 0),  # Standard 8254 PIT, no CDC
    (3, 1),  # Standard 8254 PIT, with CDC
])
def test_pit_basic(request, num_counters, cdc_enable):
    """PIT 8254 basic test."""
    run_pit_test("test_pit_basic", num_counters, cdc_enable)


if __name__ == "__main__":
    # Run pytest
    pytest.main([__file__, "-v", "-s"])
