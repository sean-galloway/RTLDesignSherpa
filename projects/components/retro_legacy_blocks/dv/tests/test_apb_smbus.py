# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_smbus
# Purpose: SMBus 2.0 Controller Test Runner
#
# Documentation: projects/components/retro_legacy_blocks/rtl/smbus/README.md
# Subsystem: retro_legacy_blocks/smbus
#
# Created: 2025-11-29

"""
SMBus 2.0 Controller Test Runner

Test runner for the APB SMBus module with support for multiple configurations.
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
from projects.components.retro_legacy_blocks.dv.tbclasses.smbus.smbus_tb import SMBusTB, SMBusRegisterMap
from projects.components.retro_legacy_blocks.dv.tbclasses.smbus.smbus_tests_basic import SMBusBasicTests


@cocotb.test(timeout_time=500, timeout_unit="us")
async def smbus_test(dut):
    """Main test function for SMBus module with modular test structure"""
    tb = SMBusTB(dut)

    # Use seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'SMBus test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} SMBus test...")
    tb.log.info("Configuration: SMBus 2.0 Master/Slave with PEC and FIFOs")

    # Create test suite
    basic_tests = SMBusBasicTests(tb)

    # Run all tests - test list varies by test level
    results = []

    # Basic tests (always run)
    basic_test_methods = [
        ('Register Access', basic_tests.test_register_access),
        ('Master Enable/Disable', basic_tests.test_master_enable_disable),
        ('Clock Configuration', basic_tests.test_clock_configuration),
        ('Timeout Configuration', basic_tests.test_timeout_configuration),
        ('Status Register', basic_tests.test_status_register),
        ('FIFO Status', basic_tests.test_fifo_status),
        ('FIFO Write', basic_tests.test_fifo_write),
        ('Interrupt Enable', basic_tests.test_interrupt_enable),
    ]

    # Medium tests (medium and full levels)
    medium_test_methods = [
        ('PEC Enable', basic_tests.test_pec_enable),
        ('Fast Mode Enable', basic_tests.test_fast_mode_enable),
        ('Slave Mode Config', basic_tests.test_slave_mode_config),
        ('Command Register', basic_tests.test_command_register),
    ]

    # Full tests (full level only)
    full_test_methods = [
        ('Full Register Sweep', basic_tests.test_full_register_sweep),
        ('FIFO Stress', basic_tests.test_fifo_stress),
        ('Config Stress', basic_tests.test_config_stress),
        # Protocol transaction type tests
        ('Transaction Type - Quick Command', basic_tests.test_transaction_type_quick_cmd),
        ('Transaction Type - Send Byte', basic_tests.test_transaction_type_send_byte),
        ('Transaction Type - Receive Byte', basic_tests.test_transaction_type_recv_byte),
        ('Transaction Type - Write Byte', basic_tests.test_transaction_type_write_byte),
        ('Transaction Type - Read Byte', basic_tests.test_transaction_type_read_byte),
        ('Transaction Type - Write Word', basic_tests.test_transaction_type_write_word),
        ('Transaction Type - Read Word', basic_tests.test_transaction_type_read_word),
        ('Transaction Type - Block Write', basic_tests.test_transaction_type_block_write),
        ('Transaction Type - Block Read', basic_tests.test_transaction_type_block_read),
        ('Transaction Type - Block Process Call', basic_tests.test_transaction_type_block_proc),
        # Additional protocol tests
        ('PEC Calculation', basic_tests.test_pec_calculation),
        ('Interrupt Status W1C', basic_tests.test_interrupt_status_w1c),
        ('All Transaction Types', basic_tests.test_all_transaction_types),
        ('FIFO Full Detection', basic_tests.test_fifo_full_detection),
        ('Clock Configuration Values', basic_tests.test_clock_configuration_values),
        ('Timeout Configuration Values', basic_tests.test_timeout_configuration_values),
        ('Slave Address Range', basic_tests.test_slave_address_range),
        ('Own Address Configuration', basic_tests.test_own_address_configuration),
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
        tb.log.info("\nAll SMBus tests PASSED!")
    else:
        tb.log.error("\nSome SMBus tests FAILED")
        assert False, f"SMBus test failed: {passed_count}/{total_count} tests passed"


def generate_test_params():
    """Generate test parameter combinations for different SMBus configurations

    Note: SMBus RTL supports CDC_ENABLE parameter for clock domain crossing.
    """

    return [
        # (cdc_enable, test_level, description)
        # Standard configurations (no CDC)
        (0, 'basic', "SMBus standard basic"),
        (0, 'medium', "SMBus standard medium"),
        (0, 'full', "SMBus standard full"),

        # CDC configurations (async clock domains)
        (1, 'basic', "SMBus with CDC basic"),
        (1, 'medium', "SMBus with CDC medium"),
        (1, 'full', "SMBus with CDC full"),
    ]


@pytest.mark.parametrize("cdc_enable, test_level, description",
                        generate_test_params())
def test_smbus(request, cdc_enable, test_level, description):
    """Test SMBus 2.0 Controller with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({})

    dut_name = "apb_smbus"

    # Create human-readable test identifier
    cdc_str = "cdc" if cdc_enable else ""

    test_name_plus_params = (f"test_smbus_{test_level}"
                            f"{('_' + cdc_str) if cdc_str else ''}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/retro_legacy_blocks/rtl/smbus/filelists/apb_smbus.f'
    )

    # RTL parameters
    rtl_parameters = {
        'CDC_ENABLE': str(cdc_enable),
        'FIFO_DEPTH': '32',  # 32 bytes per SMBus 2.0 spec
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
    print(f"Running {test_level.upper()} SMBus test: {description}")
    print(f"Configuration: 32-byte FIFOs, PEC support")
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
        print(f"SMBus test PASSED: {description}")

    except Exception as e:
        print(f"SMBus test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for SMBus:")
        print("- Check that pclk is running")
        print("- Verify reset sequence")
        print("- Check master enable configuration")
        print("- Verify clock divider settings")
        print("- Check FIFO operations")
        print(f"- Configuration: CDC={cdc_enable}, FIFO_DEPTH=32")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple SMBus test...")
    pytest.main([__file__, "-v", "-s"])
