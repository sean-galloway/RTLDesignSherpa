# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_uart_16550
# Purpose: UART 16550 Test Runner - Scalable Version with CDC Variations
#
# Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
# Subsystem: retro_legacy_blocks/uart_16550
#
# Created: 2025-11-30

"""
UART 16550 Test Runner - Scalable Version with CDC Variations

Test runner for the APB UART 16550 module with support for multiple test levels
and CDC configurations. Tests UART functionality including TX/RX, FIFOs,
interrupts, modem control, and loopback mode.

Features:
- Parametrized testing with pytest
- Multiple test levels (basic, medium, full)
- CDC_ENABLE parameter variations (sync and async clock domains)
- UART BFM integration for external TX/RX testing
- Environment variable configuration
- Proper file and directory management
- Integration with CocoTB framework
- Modular test structure with separate test classes
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
from projects.components.retro_legacy_blocks.dv.tbclasses.uart_16550.uart_16550_tb import (
    UART16550TB, UART16550RegisterMap
)
from projects.components.retro_legacy_blocks.dv.tbclasses.uart_16550.uart_16550_tests_basic import (
    UART16550BasicTests
)
from projects.components.retro_legacy_blocks.dv.tbclasses.uart_16550.uart_16550_tests_medium import (
    UART16550MediumTests
)
from projects.components.retro_legacy_blocks.dv.tbclasses.uart_16550.uart_16550_tests_full import (
    UART16550FullTests
)


@cocotb.test(timeout_time=60000, timeout_unit="us")
async def uart_16550_test(dut):
    """Main test function for UART 16550 module with modular test structure"""
    tb = UART16550TB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'UART 16550 test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} UART 16550 test...")
    tb.log.info("Configuration: NS16550-compatible UART with 16-byte FIFOs")

    # Create test suites based on level
    passed = False

    if test_level == 'basic':
        basic_tests = UART16550BasicTests(tb)
        passed = await basic_tests.run_all_basic_tests()

    elif test_level == 'medium':
        # Run basic tests first
        basic_tests = UART16550BasicTests(tb)
        basic_passed = await basic_tests.run_all_basic_tests()

        if basic_passed:
            # Run medium tests
            medium_tests = UART16550MediumTests(tb)
            medium_passed = await medium_tests.run_all_medium_tests()
            passed = basic_passed and medium_passed
        else:
            tb.log.error("Basic tests failed, skipping medium tests")
            passed = False

    else:  # full
        # Run all test levels
        basic_tests = UART16550BasicTests(tb)
        basic_passed = await basic_tests.run_all_basic_tests()

        medium_passed = False
        if basic_passed:
            medium_tests = UART16550MediumTests(tb)
            medium_passed = await medium_tests.run_all_medium_tests()

        full_passed = False
        if basic_passed and medium_passed:
            full_tests = UART16550FullTests(tb)
            full_passed = await full_tests.run_all_full_tests()

        passed = basic_passed and medium_passed and full_passed

        if not basic_passed:
            tb.log.error("Basic tests failed")
        if not medium_passed:
            tb.log.error("Medium tests failed")
        if not full_passed:
            tb.log.error("Full tests failed")

    # Overall result
    if passed:
        tb.log.info("All UART 16550 tests PASSED!")
    else:
        tb.log.error("Some UART 16550 tests FAILED")
        assert False, "UART 16550 test failed"


def generate_test_params():
    """Generate test parameter combinations for UART 16550 configurations.

    UART 16550 has CDC_ENABLE parameter to test both synchronous and
    asynchronous clock domain configurations.
    """

    return [
        # (cdc_enable, test_level, description)
        # Non-CDC configurations (CDC_ENABLE=0, same clock domain)
        (0, 'basic', "UART 16550 basic (no CDC)"),
        (0, 'medium', "UART 16550 medium (no CDC)"),
        (0, 'full', "UART 16550 full (no CDC)"),

        # CDC configurations (CDC_ENABLE=1, async clock domains)
        (1, 'basic', "UART 16550 basic CDC"),
        (1, 'medium', "UART 16550 medium CDC"),
        (1, 'full', "UART 16550 full CDC"),
    ]


@pytest.mark.parametrize("cdc_enable, test_level, description",
                        generate_test_params())
def test_uart_16550(request, cdc_enable, test_level, description):
    """Test UART 16550 with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_uart_16550"

    # Create human-readable test identifier
    cdc_str = "cdc" if cdc_enable else "nocdc"
    test_name_plus_params = f"test_uart_16550_{cdc_str}_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/uart_16550/filelists/apb_uart_16550.f'
    )

    # RTL parameters - CDC_ENABLE is parameterized
    rtl_parameters = {
        'CDC_ENABLE': str(cdc_enable),
    }

    # Calculate timeout based on test complexity
    # UART tests take longer due to serial timing
    timeout_multipliers = {'basic': 2, 'medium': 5, 'full': 15}
    complexity_factor = timeout_multipliers.get(test_level, 2)
    # CDC adds some complexity due to synchronization delays
    cdc_factor = 1.5 if cdc_enable else 1.0
    timeout_s = int(60 * complexity_factor * cdc_factor)

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

        # DUT-specific parameters
        'TEST_CDC_ENABLE': str(cdc_enable),

        # Test configuration
        'TEST_MAX_TIME': '1000000',  # Increased for UART timing
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
        "-Wno-SYNCASYNCNET",
        "-Wno-UNOPTFLAT",
        "-Wno-INITIALDLY",
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
    print(f"Running {test_level.upper()} UART 16550 test: {description}")
    print(f"Configuration: NS16550-compatible UART with 16-byte FIFOs")
    print(f"Clock domain: {cdc_mode}")
    print(f"Expected duration: {timeout_s}s")
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
            simulator="verilator",
        )
        print(f"{test_level.upper()} UART 16550 test PASSED: {description}")

    except Exception as e:
        print(f"{test_level.upper()} UART 16550 test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for UART 16550:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check baud rate divisor settings")
        print("- Verify FIFO enable (FCR[0])")
        print("- Check loopback mode (MCR[4])")
        print("- Verify interrupt enable and OUT2 gate")
        print(f"- Configuration: CDC_ENABLE={cdc_enable}")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple UART 16550 test...")
    pytest.main([__file__, "-v", "-s", "-k", "nocdc_basic"])
