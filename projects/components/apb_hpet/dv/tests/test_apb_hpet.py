# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_hpet
# Purpose: HPET Test Runner - Updated Scalable Version
#
# Documentation: projects/components/apb_hpet/PRD.md
# Subsystem: apb_hpet
#
# Author: sean galloway
# Created: 2025-10-18

"""
HPET Test Runner - Updated Scalable Version

Test runner for the APB HPET module with support for 2, 3, and 8 timers.
Automatically calculates address width requirements and supports modular testing.

Features:
- Parametrized testing with pytest
- Automatic address width calculation
- Support for 2, 3, 8 timer configurations
- Multiple test levels (basic, medium, full)
- Environment variable configuration
- Proper file and directory management
- Integration with CocoTB framework
- Modular test structure
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Add repo root to Python path
# From test file: tests -> dv -> apb_hpet -> components -> projects -> repo_root
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
import sys
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.apb_hpet.dv.tbclasses.hpet_tb import HPETTB, HPETRegisterMap
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_basic import HPETBasicTests
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_medium import HPETMediumTests
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_full import HPETFullTests


@cocotb.test(timeout_time=400, timeout_unit="us")
async def hpet_test(dut):
    """Main test function for HPET module with modular test structure"""
    tb = HPETTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'HPET test with seed: {seed}')

    # Get test parameters from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Setup clocks and reset (dual domain)
    await tb.setup_clocks_and_reset()

    # Setup components after reset
    await tb.setup_components()

    tb.log.info(f"Starting {test_level.upper()} HPET test...")
    tb.log.info(f"Configuration: {tb.NUM_TIMERS} timers, {tb.ADDR_WIDTH}-bit addressing")
    tb.log.info(f"Parameters: AW={tb.ADDR_WIDTH}, DW={tb.DATA_WIDTH}")
    tb.log.info(f"Counter Width: {tb.COUNTER_WIDTH}, Address Space: {1 << tb.ADDR_WIDTH} bytes")
    tb.log.info(f"Clock Periods: APB={tb.APB_CLOCK_PERIOD}ns, HPET={tb.HPET_CLOCK_PERIOD}ns")

    # Create test suite based on level
    passed = False

    if test_level == 'basic':
        basic_tests = HPETBasicTests(tb)
        passed = await basic_tests.run_all_basic_tests()

    elif test_level == 'medium':
        # Run basic tests first
        basic_tests = HPETBasicTests(tb)
        basic_passed = await basic_tests.run_all_basic_tests()

        if basic_passed:
            # Run medium tests
            medium_tests = HPETMediumTests(tb)
            medium_passed = await medium_tests.run_all_medium_tests()
            passed = basic_passed and medium_passed
        else:
            tb.log.error("Basic tests failed, skipping medium tests")
            passed = False

    else:  # full
        # Run all test levels
        basic_tests = HPETBasicTests(tb)
        basic_passed = await basic_tests.run_all_basic_tests()

        medium_passed = False
        if basic_passed:
            medium_tests = HPETMediumTests(tb)
            medium_passed = await medium_tests.run_all_medium_tests()

        full_passed = False
        if basic_passed and medium_passed:
            full_tests = HPETFullTests(tb)
            full_passed = await full_tests.run_all_full_tests()

        passed = basic_passed and medium_passed and full_passed

        if not basic_passed:
            tb.log.error("Basic tests failed")
        if not medium_passed:
            tb.log.error("Medium tests failed")
        if not full_passed:
            tb.log.error("Full tests failed")

    # Generate test report
    report = tb.generate_test_report()
    tb.log.info("=== HPET TEST REPORT ===")
    for section, data in report.items():
        tb.log.info(f"{section}: {data}")

    # Verify scoreboard
    register_verified = tb.scoreboard.verify_register_access()
    interrupt_verified = tb.scoreboard.verify_interrupt_behavior()

    final_passed = passed and register_verified and interrupt_verified

    if final_passed:
        tb.log.info("🎉 HPET test PASSED! 🎉")
    else:
        tb.log.error("❌ HPET test FAILED ❌")
        errors = tb.scoreboard.errors
        if errors:
            tb.log.error("Verification errors:")
            for error in errors:
                tb.log.error(f"  - {error}")
        assert False, "HPET test failed"


def generate_test_params():
    """Generate test parameter combinations for different timer configurations"""

    return [
        # (num_timers, vendor_id, revision_id, cdc_enable, test_level, description)
        # Non-CDC configurations (CDC_ENABLE=0, same clock domain)
        (2, 0x8086, 0x01, 0, 'full', "2-timer Intel-like"),
        (3, 0x1022, 0x02, 0, 'full', "3-timer AMD-like"),
        (8, 0xABCD, 0x10, 0, 'full', "8-timer custom"),

        # CDC configurations (CDC_ENABLE=1, async clock domains)
        (2, 0x8086, 0x01, 1, 'full', "2-timer Intel-like CDC"),
        (3, 0x1022, 0x02, 1, 'full', "3-timer AMD-like CDC"),
        (8, 0xABCD, 0x10, 1, 'full', "8-timer custom CDC"),
    ]


@pytest.mark.parametrize("num_timers, vendor_id, revision_id, cdc_enable, test_level, description",
                        generate_test_params())
def test_hpet(request, num_timers, vendor_id, revision_id, cdc_enable, test_level, description):
    """Test HPET with parametrized configurations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_gaxi':          'rtl/amba/gaxi',
        'rtl_apb':           'rtl/amba/apb',
        'rtl_amba_shared':   'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_hpet':          'projects/components/apb_hpet/rtl',
    })

    # Set up test names and directories
    dut_name = "apb_hpet"

    # Fixed parameters
    aw = 12  # Fixed 12-bit addressing
    dw = 32  # Fixed 32-bit data
    counter_width = 64  # Fixed 64-bit counter

    # Create human-readable test identifier
    nt_str = TBBase.format_dec(num_timers, 1)
    vid_str = f"{vendor_id:04X}"
    rid_str = f"{revision_id:02X}"
    cdc_str = "cdc" if cdc_enable else ""

    test_name_plus_params = (f"test_hpet_"
                            f"t{nt_str}_"
                            f"v{vid_str}_r{rid_str}_{test_level}"
                            f"{('_' + cdc_str) if cdc_str else ''}")

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Validate configuration
    if num_timers < 2 or num_timers > 8:
        raise ValueError(f"Number of timers {num_timers} out of supported range (2-8)")

    # Get verilog sources - HPET hierarchy
    verilog_sources = [
        # Common modules
        os.path.join(rtl_dict['rtl_cmn'],           "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],           "fifo_control.sv"),

        # GAXI modules for CDC
        os.path.join(rtl_dict['rtl_gaxi'],          "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_gaxi'],          "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'],   "cdc_handshake.sv"),

        # APB modules
        os.path.join(rtl_dict['rtl_apb'],           "apb_slave.sv"),
        os.path.join(rtl_dict['rtl_apb'],           "apb_slave_cdc.sv"),

        # PeakRDL adapter (from shims component)
        os.path.join(repo_root, "projects/components/shims/rtl/peakrdl_to_cmdrsp.sv"),

        # HPET modules (PeakRDL-based configuration registers)
        os.path.join(rtl_dict.get('rtl_hpet', 'rtl/hpet'), "hpet_regs_pkg.sv"),    # PeakRDL package
        os.path.join(rtl_dict.get('rtl_hpet', 'rtl/hpet'), "hpet_regs.sv"),        # PeakRDL generated
        os.path.join(rtl_dict.get('rtl_hpet', 'rtl/hpet'), "hpet_core.sv"),
        os.path.join(rtl_dict.get('rtl_hpet', 'rtl/hpet'), "hpet_config_regs.sv"), # Wrapper
        os.path.join(rtl_dict.get('rtl_hpet', 'rtl/hpet'), f"{dut_name}.sv")
    ]

    # RTL parameters - NUM_TIMERS, VENDOR_ID, REVISION_ID, CDC_ENABLE are parameterized
    rtl_parameters = {
        'NUM_TIMERS': str(num_timers),
        'VENDOR_ID': str(vendor_id),
        'REVISION_ID': str(revision_id),
        'CDC_ENABLE': str(cdc_enable),
    }

    # Calculate timeout based on test complexity and timer count
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 8}
    complexity_factor = timeout_multipliers.get(test_level, 1)
    data_complexity = max(1.0, dw / 32.0)
    timer_complexity = max(1.0, num_timers / 2.0)  # Scale with timer count
    # Fixed clock periods: APB=20ns, HPET=10ns
    clock_complexity = 2.0  # APB period / HPET period = 20/10 = 2

    total_complexity = complexity_factor * data_complexity * timer_complexity * clock_complexity
    timeout_s = int(30 * total_complexity)

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
        'TEST_NUM_TIMERS': str(num_timers),
        # Fixed parameters are no longer passed - they're hardcoded in the TB

        # Clock configuration (fixed values)
        'TEST_APB_CLOCK_PERIOD': '20',  # Fixed APB clock period
        'TEST_HPET_CLOCK_PERIOD': '10', # Fixed HPET clock period

        # Test configuration
        'TEST_MAX_TIME': '200000',  # Increased for full tests
        'TEST_INTERRUPT_TIMEOUT': '25000',  # Increased to allow for HPET disabled during config + APB delays
    }

    # Simulation settings
    includes = [rtl_dict.get('rtl_amba_includes', 'rtl/amba/includes')]
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "-Wall",
        # Waive warnings from PeakRDL-generated code
        "-Wno-GENUNNAMED",      # Unnamed generate blocks in PeakRDL output
        "-Wno-MULTIDRIVEN",     # Multiple drivers in PeakRDL field_combo
        "-Wno-UNUSEDPARAM",     # Unused parameters in package
    ]
    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99"
    ]
    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    cdc_mode = "CDC enabled (async clocks)" if cdc_enable else "No CDC (same clock)"
    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} HPET test: {description}")
    print(f"Configuration: {num_timers} timers, Vendor ID=0x{vendor_id:04X}, Revision ID=0x{revision_id:02X}")
    print(f"Clock domain: {cdc_mode}")
    print(f"Fixed parameters: 12-bit addressing (4KB), 32-bit data, 64-bit counter")
    print(f"Clock Periods: APB=20ns, HPET=10ns (fixed)")
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
        )
        print(f"✅ {test_level.upper()} HPET test PASSED: {description}")

    except Exception as e:
        print(f"❌ {test_level.upper()} HPET test FAILED: {description}")
        print(f"Error: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run this command: {cmd_filename}")
        print("\nTroubleshooting hints for HPET:")
        print("- Check that both pclk and hpet_clk are running")
        print("- Verify dual reset sequence (presetn and hpet_resetn)")
        print("- Look for CDC crossing issues between APB and HPET domains")
        print("- Check HPET enable bit in configuration register")
        print("- Verify timer configuration and comparator values")
        print("- Monitor interrupt assertion and clearing")
        print(f"- Configuration: {num_timers} timers, Vendor ID=0x{vendor_id:04X}, Revision ID=0x{revision_id:02X}")
        raise


if __name__ == "__main__":
    """Run a simple test when called directly"""
    print("Running simple HPET test...")

    # Choose configuration based on environment
    test_config = os.environ.get('HPET_TEST_CONFIG', '2timer').lower()

    config_map = {
        '2timer': (2, 0x8086, 0x01, 'basic'),  # Intel-like
        '3timer': (3, 0x1022, 0x02, 'basic'),  # AMD-like
        '8timer': (8, 0xABCD, 0x10, 'basic'),  # Custom
    }

    if test_config not in config_map:
        print(f"Unknown test config '{test_config}', using '2timer'")
        test_config = '2timer'

    num_timers, vendor_id, revision_id, test_level = config_map[test_config]

    # Set environment for test
    os.environ.update({
        'SEED': '12345',
        'TEST_LEVEL': test_level,
        'TEST_NUM_TIMERS': str(num_timers),
        'TEST_APB_CLOCK_PERIOD': '20',  # Fixed
        'TEST_HPET_CLOCK_PERIOD': '10',  # Fixed
        'HPET_DEBUG_MODE': 'true'
    })

    description = f"{num_timers}-timer {test_level} (Vendor={vendor_id:04X}, Rev={revision_id:02X})"
    print(f"Running {description} configuration...")

    # Run test
    test_hpet(None, num_timers, vendor_id, revision_id, test_level, description)
