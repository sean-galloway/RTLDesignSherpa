# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_rtc
# Purpose: RTC Test Runner - Updated Scalable Version
#
# Documentation: projects/components/retro_legacy_blocks/rtl/rtc/README.md
# Subsystem: retro_legacy_blocks/rtc
#
# Created: 2025-11-15

"""
RTC Test Runner - Updated Scalable Version

Test runner for the APB RTC module with support for multiple test levels.
Follows the same methodology as HPET for consistency.

Features:
- Parametrized testing with pytest
- Multiple test levels (basic, medium, full)
- Environment variable configuration
- Proper file and directory management
- Integration with CocoTB framework
- Modular test structure
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
from projects.components.retro_legacy_blocks.dv.tbclasses.rtc.rtc_tb import RTCTB, RTCRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.rtc.rtc_tests_basic import RTCBasicTests


@cocotb.test(timeout_time=800, timeout_unit="us")
async def rtc_test(dut):
    """Main test function for RTC module with modular test structure"""
    tb = RTCTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'RTC test with seed: {seed}')

    # Get test level from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Setup clocks and reset
    await tb.setup_clocks_and_reset()

    # Setup components after reset
    await tb.setup_components()

    tb.log.info(f"Starting {test_level.upper()} RTC test...")
    tb.log.info("Configuration: Time-of-day tracking with alarm")

    # Create test suite
    basic_tests = RTCBasicTests(tb)

    # Run all tests - test list varies by test level
    results = []

    # Basic tests (always run)
    basic_test_methods = [
        ('Register Access', basic_tests.test_register_access),
        ('RTC Enable/Disable', basic_tests.test_rtc_enable_disable),
        ('Time Setting', basic_tests.test_time_setting),
        ('Time Counting', basic_tests.test_time_counting),
        ('Alarm Basic', basic_tests.test_alarm_basic),
        ('Status Flags', basic_tests.test_status_flags),
    ]

    # Medium tests (medium and full levels)
    medium_test_methods = [
        ('BCD Mode', basic_tests.test_bcd_mode),
        ('12-Hour Mode', basic_tests.test_12_hour_mode),
    ]

    # Full tests (full level only)
    full_test_methods = [
        ('Date Rollover', basic_tests.test_date_rollover),
        ('Alarm Matching', basic_tests.test_alarm_matching),
        ('RTC Stress Test', basic_tests.test_rtc_stress),
        # Enhanced calendar edge cases
        ('Leap Year Feb 29', basic_tests.test_leap_year_feb29),
        ('Century Leap Year', basic_tests.test_century_leap_year),
        ('Month Day Limits', basic_tests.test_month_day_limits),
        ('Year Rollover 99 to 00', basic_tests.test_year_rollover_99_to_00),
        # Enhanced alarm and interrupt tests
        ('Alarm All Fields Match', basic_tests.test_alarm_all_fields_match),
        ('Periodic Second Interrupt', basic_tests.test_periodic_second_interrupt),
        ('Binary Time Format', basic_tests.test_time_format_binary),
        ('Update In Progress', basic_tests.test_update_in_progress),
        # Rollover tests
        ('Minute Rollover', basic_tests.test_minute_rollover),
        ('Hour Rollover', basic_tests.test_hour_rollover),
        ('Day of Week', basic_tests.test_day_of_week),
        ('Alarm Interrupt Output', basic_tests.test_alarm_interrupt_output),
        ('Time Registers Readback', basic_tests.test_time_registers_readback),
    ]

    # Select test methods based on level
    if test_level == 'basic':
        test_methods = basic_test_methods
    elif test_level == 'medium':
        test_methods = basic_test_methods + medium_test_methods
    else:  # full
        test_methods = basic_test_methods + medium_test_methods + full_test_methods

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
        status = "PASSED" if result else "FAILED"
        tb.log.info(f"{test_name:40s} {status}")

    tb.log.info(f"\nPassed: {passed_count}/{total_count}")

    # Overall result
    all_passed = all(result for _, result in results)

    if all_passed:
        tb.log.info("\nAll RTC tests PASSED!")
    else:
        tb.log.error("\nSome RTC tests FAILED")
        assert False, f"RTC test failed: {passed_count}/{total_count} tests passed"


def generate_test_params():
    """Generate test parameter combinations for RTC configurations"""

    return [
        # (test_level, description)
        # RTC has no RTL parameters to vary, so test levels provide coverage
        ('basic', "RTC basic test"),
        ('medium', "RTC medium test"),
        ('full', "RTC full test"),
    ]


@pytest.mark.parametrize("test_level, description",
                        generate_test_params())
def test_rtc(request, test_level, description):
    """Test RTC with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_rtc"

    # Create human-readable test identifier
    test_name_plus_params = f"test_rtc_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/rtc/filelists/apb_rtc.f'
    )

    # No RTL parameters for RTC (fixed configuration)
    rtl_parameters = {}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
    }

    # WAVES support
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    # Simulation settings
    compile_args = [
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
    ]
    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} RTC test: {description}")
    print(f"Configuration: Time-of-day tracking with alarm")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"RTC test PASSED: {description}")

    except Exception as e:
        print(f"RTC test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for RTC:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check RTC enable bit")
        print("- Verify time register programming")
        print("- Check alarm configuration")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple RTC test...")
    pytest.main([__file__, "-v", "-s"])
