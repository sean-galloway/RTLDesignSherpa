# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_pic_8259
# Purpose: PIC 8259 Test Runner - Updated Scalable Version
#
# Documentation: projects/components/retro_legacy_blocks/rtl/pic_8259/README.md
# Subsystem: retro_legacy_blocks/pic_8259
#
# Created: 2025-11-16

"""
PIC 8259 Test Runner - Updated Scalable Version

Test runner for the APB PIC 8259 module with support for multiple test levels.
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
from projects.components.retro_legacy_blocks.dv.tbclasses.pic_8259.pic_8259_tb import PIC8259TB, PIC8259RegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.pic_8259.pic_8259_tests_basic import PIC8259BasicTests


@cocotb.test(timeout_time=500, timeout_unit="us")
async def pic_8259_test(dut):
    """Main test function for PIC 8259 module with modular test structure"""
    tb = PIC8259TB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'PIC 8259 test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} PIC 8259 test...")
    tb.log.info("Configuration: 8 IRQs, edge/level triggered, priority control")

    # Create test suite
    basic_tests = PIC8259BasicTests(tb)

    # Run all tests - test list varies by test level
    results = []

    # Basic tests (always run)
    basic_test_methods = [
        ('Register Access', basic_tests.test_register_access),
        ('PIC Initialization', basic_tests.test_initialization),
        ('Single IRQ Handling', basic_tests.test_single_irq),
        ('IRQ Masking', basic_tests.test_irq_masking),
        ('Multiple IRQ Priority', basic_tests.test_multiple_irqs),
        ('EOI Handling', basic_tests.test_eoi_handling),
    ]

    # Medium tests (medium and full levels)
    medium_test_methods = [
        ('Level-Triggered Mode', basic_tests.test_level_triggered_mode),
        ('Priority Rotation', basic_tests.test_priority_rotation),
    ]

    # Full tests (full level only)
    full_test_methods = [
        ('All IRQ Lines', basic_tests.test_all_irq_lines),
        ('IRQ Stress Test', basic_tests.test_irq_stress),
        # Enhanced cascade and nested interrupt tests
        ('Special Mask Mode', basic_tests.test_special_mask_mode),
        ('Automatic EOI Mode', basic_tests.test_auto_eoi_mode),
        ('Nested Interrupt Handling', basic_tests.test_nested_interrupt_handling),
        ('Poll Command', basic_tests.test_poll_command),
        ('Rotate on Specific EOI', basic_tests.test_rotate_on_specific_eoi),
        ('ICW1-4 Initialization Sequence', basic_tests.test_initialization_words_sequence),
        ('Edge vs Level Sensitivity', basic_tests.test_irq_edge_vs_level_sensitivity),
        ('Read Register Commands', basic_tests.test_read_register_commands),
        ('Simultaneous IRQs Priority', basic_tests.test_simultaneous_irqs_priority),
        ('IMR Protection', basic_tests.test_imr_protection),
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
        tb.log.info("\nAll PIC 8259 tests PASSED!")
    else:
        tb.log.error("\nSome PIC 8259 tests FAILED")
        assert False, f"PIC 8259 test failed: {passed_count}/{total_count} tests passed"


def generate_test_params():
    """Generate test parameter combinations for PIC 8259 configurations"""

    return [
        # (test_level, description)
        # PIC 8259 has no RTL parameters to vary, so test levels provide coverage
        ('basic', "PIC 8259 basic test"),
        ('medium', "PIC 8259 medium test"),
        ('full', "PIC 8259 full test"),
    ]


@pytest.mark.parametrize("test_level, description",
                        generate_test_params())
def test_pic_8259(request, test_level, description):
    """Test PIC 8259 with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_pic_8259"

    # Create human-readable test identifier
    test_name_plus_params = f"test_pic_8259_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/pic_8259/filelists/apb_pic_8259.f'
    )

    # No RTL parameters for PIC 8259 (fixed configuration)
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
    print(f"Running {test_level.upper()} PIC 8259 test: {description}")
    print(f"Configuration: 8 IRQs, edge/level triggered, priority control")
    print(f"{'='*80}")

    try:
        run(
            simulator="verilator",
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
        print(f"PIC 8259 test PASSED: {description}")

    except Exception as e:
        print(f"PIC 8259 test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for PIC 8259:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check ICW initialization sequence")
        print("- Verify IRQ handling and priority")
        print("- Check EOI handling")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple PIC 8259 test...")
    pytest.main([__file__, "-v", "-s"])
