# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_pit_8254
# Purpose: PIT 8254 Test Runner - Updated Scalable Version
#
# Documentation: projects/components/retro_legacy_blocks/rtl/pit_8254/README.md
# Subsystem: retro_legacy_blocks/pit_8254
#
# Created: 2025-11-06

"""
PIT 8254 Test Runner - Updated Scalable Version

Test runner for the APB 8254 PIT module with support for multiple configurations.
Follows the same methodology as HPET for consistency.

Features:
- Parametrized testing with pytest
- Support for CDC and non-CDC configurations
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
from projects.components.retro_legacy_blocks.dv.tbclasses.pit_8254.pit_tb import PITTB, PITRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.pit_8254.pit_tests_basic import PITBasicTests


@cocotb.test(timeout_time=200, timeout_unit="us")
async def pit_test(dut):
    """Main test function for PIT module with modular test structure"""
    tb = PITTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'PIT test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} PIT test...")
    tb.log.info(f"Configuration: {tb.num_counters} counters")

    # Create test suite
    basic_tests = PITBasicTests(tb)

    # Run all tests - test list varies by test level
    results = []

    # Basic tests (always run)
    basic_test_methods = [
        ('Register Access', basic_tests.test_register_access),
        ('PIT Enable/Disable', basic_tests.test_pit_enable_disable),
        ('Control Word Programming', basic_tests.test_control_word_programming),
        ('Counter Mode 0 Simple', basic_tests.test_counter_mode0_simple),
        ('Multiple Counters', basic_tests.test_multiple_counters),
        ('Status Register', basic_tests.test_status_register),
    ]

    # Medium tests (medium and full levels)
    medium_test_methods = [
        ('Counter Mode 2 Rate Generator', basic_tests.test_counter_mode2_rate_generator),
        ('Counter Mode 3 Square Wave', basic_tests.test_counter_mode3_square_wave),
    ]

    # Full tests (full level only)
    full_test_methods = [
        ('All Counter Modes', basic_tests.test_all_counter_modes),
        ('Counter Stress Test', basic_tests.test_counter_stress),
        # Enhanced mode tests (modes 1, 4, 5)
        ('Mode 1 - HW Retriggerable One-Shot', basic_tests.test_counter_mode1_hw_retriggerable),
        ('Mode 4 - SW Triggered Strobe', basic_tests.test_counter_mode4_sw_triggered_strobe),
        ('Mode 5 - HW Triggered Strobe', basic_tests.test_counter_mode5_hw_triggered_strobe),
        # Gate and control tests
        ('Gate Control Mode 0', basic_tests.test_gate_control_mode0),
        ('BCD Counting Mode', basic_tests.test_bcd_counting),
        ('RW Mode LSB Only', basic_tests.test_rw_mode_lsb_only),
        ('RW Mode MSB Only', basic_tests.test_rw_mode_msb_only),
        ('Counter Latch Command', basic_tests.test_counter_latch_command),
        ('Read-Back Command', basic_tests.test_read_back_command),
        ('Mode Transition', basic_tests.test_mode_transition),
        ('All Counters Independent', basic_tests.test_all_counters_independent),
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
        tb.log.info("\nAll PIT tests PASSED!")
    else:
        tb.log.error("\nSome PIT tests FAILED")
        assert False, f"PIT test failed: {passed_count}/{total_count} tests passed"


def generate_test_params():
    """Generate test parameter combinations for different PIT configurations

    Note: PIT RTL has fixed 3-counter architecture (like original 8254).
    NUM_COUNTERS parameter is not supported in current RTL.
    """

    return [
        # (cdc_enable, test_level, description)
        # Standard 3-counter configurations (like original 8254)
        (0, 'basic', "3-counter standard PIT basic"),
        (0, 'medium', "3-counter standard PIT medium"),
        (0, 'full', "3-counter standard PIT full"),

        # CDC configurations (async clock domains)
        (1, 'basic', "3-counter PIT with CDC basic"),
        (1, 'medium', "3-counter PIT with CDC medium"),
        (1, 'full', "3-counter PIT with CDC full"),
    ]


@pytest.mark.parametrize("cdc_enable, test_level, description",
                        generate_test_params())
def test_pit(request, cdc_enable, test_level, description):
    """Test PIT 8254 with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_pit_8254"

    # Create human-readable test identifier
    # PIT has fixed 3 counters, only CDC is parameterized
    cdc_str = "cdc" if cdc_enable else ""

    test_name_plus_params = (f"test_pit_{test_level}"
                            f"{('_' + cdc_str) if cdc_str else ''}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/pit_8254/filelists/apb_pit_8254.f'
    )

    # RTL parameters - only CDC_ENABLE is parameterized
    # NUM_COUNTERS is fixed at 3 in the RTL (like original 8254)
    rtl_parameters = {
        'CDC_ENABLE': str(cdc_enable),
    }

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

    cdc_mode = "CDC enabled (async clocks)" if cdc_enable else "No CDC (same clock)"
    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} PIT test: {description}")
    print(f"Configuration: 3 counters (fixed, like original 8254)")
    print(f"Clock domain: {cdc_mode}")
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
        print(f"PIT test PASSED: {description}")

    except Exception as e:
        print(f"PIT test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for PIT:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check counter programming sequence")
        print("- Verify gate signal handling")
        print(f"- Configuration: 3 counters, CDC={cdc_enable}")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple PIT test...")
    pytest.main([__file__, "-v", "-s"])
