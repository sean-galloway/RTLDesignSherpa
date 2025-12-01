# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_ioapic
# Purpose: IOAPIC Test Runner - Updated Scalable Version
#
# Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2025-11-16

"""
IOAPIC Test Runner - Updated Scalable Version

Test runner for the APB IOAPIC module with support for multiple configurations.
Follows the same methodology as HPET for consistency.

Features:
- Parametrized testing with pytest
- Support for different IRQ counts and CDC configurations
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
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import IOAPICTB, IOAPICRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tests_basic import IOAPICBasicTests


@cocotb.test(timeout_time=500, timeout_unit="us")
async def ioapic_test(dut):
    """Main test function for IOAPIC module with modular test structure"""
    tb = IOAPICTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'IOAPIC test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} IOAPIC test...")
    tb.log.info(f"Configuration: {tb.num_irqs} IRQs with redirection table")

    # Create test suite
    basic_tests = IOAPICBasicTests(tb)

    # Run all tests - test list varies by test level
    results = []

    # Basic tests (always run)
    basic_test_methods = [
        ('Indirect Register Access', basic_tests.test_register_access),
        ('Identification Registers', basic_tests.test_identification_registers),
        ('Redirection Table Access', basic_tests.test_redirection_table_access),
        ('Edge-Triggered Interrupt', basic_tests.test_edge_triggered_interrupt),
        ('Interrupt Masking', basic_tests.test_interrupt_masking),
        ('Multiple IRQ Priority', basic_tests.test_multiple_irqs_priority),
    ]

    # Medium tests (medium and full levels)
    medium_test_methods = [
        ('Level-Triggered Interrupt', basic_tests.test_level_triggered_interrupt),
        ('Polarity Inversion', basic_tests.test_polarity_inversion),
    ]

    # Full tests (full level only)
    full_test_methods = [
        ('All IRQ Lines', basic_tests.test_all_irq_lines),
        ('IRQ Stress Test', basic_tests.test_irq_stress),
        # Enhanced delivery mode tests
        ('Fixed Delivery Mode', basic_tests.test_delivery_mode_fixed),
        ('Lowest Priority Delivery Mode', basic_tests.test_delivery_mode_lowest_priority),
        ('SMI Delivery Mode', basic_tests.test_delivery_mode_smi),
        ('NMI Delivery Mode', basic_tests.test_delivery_mode_nmi),
        ('INIT Delivery Mode', basic_tests.test_delivery_mode_init),
        ('ExtINT Delivery Mode', basic_tests.test_delivery_mode_extint),
        # Destination mode tests
        ('Physical Destination Mode', basic_tests.test_destination_mode_physical),
        ('Logical Destination Mode', basic_tests.test_destination_mode_logical),
        # Status and field tests
        ('Remote IRR Status', basic_tests.test_remote_irr_status),
        ('Delivery Status Read', basic_tests.test_delivery_status_read),
        ('Vector Range Validation', basic_tests.test_vector_range_validation),
        ('Full Redirection Table', basic_tests.test_full_redirection_table),
        ('Mask All IRQs', basic_tests.test_mask_all_irqs),
        ('EOI Broadcast Behavior', basic_tests.test_eoi_broadcast),
        ('IOAPIC ID Programming', basic_tests.test_ioapic_id_programming),
        ('Arbitration ID Read', basic_tests.test_arbitration_id_read),
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
        tb.log.info("\nAll IOAPIC tests PASSED!")
    else:
        tb.log.error("\nSome IOAPIC tests FAILED")
        assert False, f"IOAPIC test failed: {passed_count}/{total_count} tests passed"


def generate_test_params():
    """Generate test parameter combinations for IOAPIC configurations

    Note: IOAPIC RTL has fixed 24-IRQ architecture (like Intel 82093AA).
    NUM_IRQS parameter is not fully supported in current RTL.
    """

    return [
        # (cdc_enable, test_level, description)
        # Standard 24-IRQ IOAPIC configurations
        (0, 'basic', "24-IRQ IOAPIC basic"),
        (0, 'medium', "24-IRQ IOAPIC medium"),
        (0, 'full', "24-IRQ IOAPIC full"),

        # CDC configurations (async clock domains)
        (1, 'basic', "24-IRQ IOAPIC with CDC basic"),
        (1, 'medium', "24-IRQ IOAPIC with CDC medium"),
        (1, 'full', "24-IRQ IOAPIC with CDC full"),
    ]


@pytest.mark.parametrize("cdc_enable, test_level, description",
                        generate_test_params())
def test_ioapic(request, cdc_enable, test_level, description):
    """Test IOAPIC with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_ioapic"

    # Create human-readable test identifier
    # IOAPIC has fixed 24 IRQs, only CDC is parameterized
    cdc_str = "cdc" if cdc_enable else ""

    test_name_plus_params = (f"test_ioapic_{test_level}"
                            f"{('_' + cdc_str) if cdc_str else ''}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/ioapic/filelists/apb_ioapic.f'
    )

    # RTL parameters - only CDC_ENABLE is parameterized
    # NUM_IRQS is fixed at 24 in the RTL (like Intel 82093AA)
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
    print(f"Running {test_level.upper()} IOAPIC test: {description}")
    print(f"Configuration: 24 IRQs with redirection table (fixed, like Intel 82093AA)")
    print(f"Clock domain: {cdc_mode}")
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
        print(f"IOAPIC test PASSED: {description}")

    except Exception as e:
        print(f"IOAPIC test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for IOAPIC:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check indirect register access via IOREGSEL/IOWIN")
        print("- Verify redirection table configuration")
        print("- Check interrupt delivery and EOI handling")
        print(f"- Configuration: 24 IRQs, CDC={cdc_enable}")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple IOAPIC test...")
    pytest.main([__file__, "-v", "-s"])
