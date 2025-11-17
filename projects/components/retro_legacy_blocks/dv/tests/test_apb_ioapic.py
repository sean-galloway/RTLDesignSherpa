# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_ioapic
# Purpose: IOAPIC Test Runner
#
# Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
# Subsystem: retro_legacy_blocks/ioapic
#
# Created: 2025-11-16

"""
IOAPIC Test Runner

Test runner for the APB IOAPIC module with basic functionality testing.

Features:
- Parametrized testing with pytest
- Basic test level (register access, interrupts, masking, priority)
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
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tb import IOAPICTB, IOAPICRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.ioapic.ioapic_tests_basic import IOAPICBasicTests


@cocotb.test(timeout_time=500, timeout_unit="us")
async def cocotb_test_ioapic_basic(dut):
    """Main test function for IOAPIC module - basic tests"""
    tb = IOAPICTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'IOAPIC test with seed: {seed}')

    # Get test level from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Setup clocks and reset
    await tb.setup_clocks_and_reset()

    # Setup components after reset (SAME AS HPET/PIT/RTC)
    await tb.setup_components()

    tb.log.info(f"Starting {test_level.upper()} IOAPIC test...")
    tb.log.info("Configuration: 24 IRQs with redirection table")

    # Create test suite
    basic_tests = IOAPICBasicTests(tb)

    # Run all tests
    results = []
    test_methods = [
        ('Indirect Register Access', basic_tests.test_register_access),
        ('Identification Registers', basic_tests.test_identification_registers),
        ('Redirection Table Access', basic_tests.test_redirection_table_access),
        ('Edge-Triggered Interrupt', basic_tests.test_edge_triggered_interrupt),
        ('Interrupt Masking', basic_tests.test_interrupt_masking),
        ('Multiple IRQ Priority', basic_tests.test_multiple_irqs_priority),
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
        status = "PASSED" if result else "FAILED"
        tb.log.info(f"{test_name:40s} {status}")

    tb.log.info(f"\nPassed: {passed_count}/{total_count}")

    # Overall result
    all_passed = all(result for _, result in results)

    if all_passed:
        tb.log.info("\nAll IOAPIC tests PASSED!")
    else:
        tb.log.error("\nSome IOAPIC tests FAILED")

    assert all_passed, f"IOAPIC test failed: {passed_count}/{total_count} tests passed"


def run_ioapic_test(testcase_name):
    """Helper function to run IOAPIC tests with common setup."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_ioapic"

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/ioapic/filelists/apb_ioapic.f'
    )

    # Format test name
    test_name_plus_params = f"test_{dut_name}_{testcase_name}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # No RTL parameters for IOAPIC (fixed configuration: 24 IRQs)
    rtl_parameters = {}

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

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, 'test_apb_ioapic', test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module='test_apb_ioapic',
            testcase=f"cocotb_{testcase_name}",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            simulator="verilator",  # Explicitly specify verilator
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


@pytest.mark.parametrize("test_level", ["basic"])
def test_ioapic_basic(test_level):
    """Run IOAPIC basic tests"""
    os.environ['TEST_LEVEL'] = test_level
    run_ioapic_test('test_ioapic_basic')
