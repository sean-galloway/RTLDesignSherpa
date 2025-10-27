# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_fifo_buffer_multi_sigmap
# Purpose: FIFO Buffer Multi-Signal Test with Parameterized Test Levels
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
FIFO Buffer Multi-Signal Test with Parameterized Test Levels

This test uses test_level as a parameter for maximum flexibility:

TEST LEVELS:
    basic (4-6 min):   Quick verification during development
    medium (10-15 min): Integration testing for CI/branches
    full (25-35 min):  Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - addr_width: [4, 6, 8]
    - ctrl_width: [3, 5, 7]
    - data_width: [8]
    - depth: [2, 4, 8]
    - clk_periods: [10]
    - registered: [0=mux, 1=flop]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.fifo.fifo_buffer_multi_sigmap import FifoMultiSigMapBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=5, timeout_unit="ms")  # Increased timeout for multi-signal testing
async def fifo_multi_test(dut):
    '''Test the FIFO Buffer Multi-Signal comprehensively with FlexConfigGen randomizers'''
    tb = FifoMultiSigMapBufferTB(dut, dut.clk, dut.rst_n, super_debug=False)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Get test level from environment (default: basic)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    tb.log.info(f"Running multi-signal test level: {test_level.upper()}")

    await tb.start_clock('clk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('clk', 5)
    tb.log.info(f"Starting {test_level.upper()} FIFO multi-signal test...")

    # Get available randomizer configurations from FlexConfigGen
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available multi-signal randomizer configs: {config_names}")

    # Define test configurations based on test level
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_configs = ['backtoback', 'fast', 'constrained', 'multi_realistic']
        packet_counts = {
            'simple_loops': 3 * tb.TEST_DEPTH,
            'sequence_test': 8,
            'isolation_test': 12,
            'back_to_back': 15
        }
        run_comprehensive_sweep = False
        run_sequence_tests = ['burst']
        run_isolation_test = False
        run_protocol_error_test = False

    elif test_level == 'medium':
        # Moderate testing for development
        test_configs = [
            'backtoback', 'fast', 'constrained', 'bursty',
            'multi_stress', 'multi_realistic', 'multi_pipeline',
            'moderate', 'balanced', 'pipeline'
        ]
        packet_counts = {
            'simple_loops': 6 * tb.TEST_DEPTH,
            'sequence_test': 12,
            'isolation_test': 16,
            'back_to_back': 25
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 4 * tb.TEST_DEPTH
        run_sequence_tests = ['burst', 'stress']
        run_isolation_test = True
        run_protocol_error_test = True

    else:  # test_level == 'full'
        # Comprehensive testing for validation
        essential_configs = [
            'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
            'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
            'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
            'multi_stress', 'multi_pipeline', 'multi_burst', 'multi_realistic',
            'multi_fine_grain', 'multi_signal_aware'
        ]
        test_configs = [config for config in essential_configs if config in config_names]
        packet_counts = {
            'simple_loops': 10 * tb.TEST_DEPTH,
            'sequence_test': 20,
            'isolation_test': 20,
            'back_to_back': 35
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 8 * tb.TEST_DEPTH
        run_sequence_tests = ['burst', 'stress', 'comprehensive', 'capacity']
        run_isolation_test = True
        run_protocol_error_test = True

    # Filter to only test configs that exist
    test_configs = [config for config in test_configs if config in config_names]

    tb.log.info(f"Testing multi-signal with {len(test_configs)} configs: {test_configs}")
    tb.log.info(f"Multi-signal packet counts: {packet_counts}")

    # Run core multi-signal tests with different randomizer configurations
    for i, delay_key in enumerate(test_configs):
        tb.log.info(f"[{i+1}/{len(test_configs)}] Testing multi-signal with '{delay_key}' randomizer configuration")
        await tb.simple_incremental_loops(
            count=packet_counts['simple_loops'],
            delay_key=delay_key,
            delay_clks_after=10
        )
        tb.log.info(f"✓ Completed multi-signal '{delay_key}' configuration")

    # Run comprehensive sweep for medium and full levels
    if run_comprehensive_sweep:
        tb.log.info("Running comprehensive multi-signal randomizer sweep...")
        await tb.comprehensive_randomizer_sweep(packets_per_config=comprehensive_packets)
        tb.log.info("✓ Completed comprehensive multi-signal sweep")

    # Run sequence tests
    for sequence_type in run_sequence_tests:
        tb.log.info(f"Running multi-signal sequence test: {sequence_type}...")
        await tb.run_sequence_test(
            sequence_type=sequence_type,
            count=packet_counts['sequence_test']
        )
        tb.log.info(f"✓ Completed multi-signal sequence test: {sequence_type}")

    # Run signal isolation test for medium and full levels
    if run_isolation_test:
        tb.log.info("Running multi-signal isolation test...")
        await tb.signal_isolation_test(count=packet_counts['isolation_test'])
        tb.log.info("✓ Completed multi-signal isolation test")

    # Always run back-to-back test (essential for multi-signal validation)
    tb.log.info("Running back-to-back multi-signal test...")
    await tb.back_to_back_multi_signal_test(count=packet_counts['back_to_back'])
    tb.log.info("✓ Completed back-to-back multi-signal test")

    tb.log.info(f"✓ ALL {test_level.upper()} MULTI-SIGNAL TESTS PASSED!")


def generate_params():
    """
    Generate test parameters for multi-signal testing. Modify this function to limit test scope for debugging.
    
    Examples for quick debugging:
        # Single test case:
        return [(4, 5, 8, 4, 10, 10, 0, 'basic')]
        
        # Just test one mode:
        return [(4, 5, 8, 4, 10, 10, 0, 'basic'), (4, 5, 8, 4, 10, 10, 1, 'basic')]
        
        # Test only basic level:
        addr_widths = [4]
        ctrl_widths = [5]
        data_widths = [8]
        depths = [2, 4]
        wr_clk_periods = [10]
        rd_clk_periods = [10]
        registered = [0, 1]
        test_levels = ['basic']  # Only basic
        return list(product(addr_widths, ctrl_widths, data_widths, depths, wr_clk_periods, rd_clk_periods, registered, test_levels))
    """
    addr_widths = [4, 6, 8]
    ctrl_widths = [3, 5, 7]
    data_widths = [8]
    depths = [2, 4, 6, 8]  # Test multiple depths for multi-signal testing
    # depths = [4]  # For debugging
    wr_clk_periods = [10]
    rd_clk_periods = [10]
    registered = [0, 1]
    # test_levels = ['basic', 'medium', 'full']  # All test levels
    test_levels = ['full']  # For initial testing
    return [(4, 5, 8, 4, 10, 10, 0, 'full'), (4, 5, 8, 4, 10, 10, 1, 'full')]
    # return list(product(addr_widths, ctrl_widths, data_widths, depths, wr_clk_periods, rd_clk_periods, registered, test_levels))

params = generate_params()

@pytest.mark.parametrize("addr_width, ctrl_width, data_width, depth, wr_clk_period, rd_clk_period, registered, test_level", params)
def test_fifo_buffer_multi_sigmap(request, addr_width, ctrl_width, data_width, depth, wr_clk_period, rd_clk_period, registered, test_level):
    """
    Parameterized FIFO buffer multi-signal test with configurable test levels.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (4-6 min)
    - medium: Integration testing (10-15 min)
    - full: Comprehensive validation (25-35 min)

    For quick debugging: Modify generate_params() function to return only specific combinations
    """
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':      'rtl/common',
        'rtl_cmn_test': 'rtl/common/testcode',
        'rtl_amba_includes': 'rtl/amba/includes',
    })
    mode_list = ['fifo_mux', 'fifo_flop']
    mode = mode_list[registered]

    # set up all of the test names
    dut_name = "fifo_sync_multi_sigmap"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_cmn_test'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier with test level
    aw_str = TBBase.format_dec(addr_width, 3)
    cw_str = TBBase.format_dec(ctrl_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wcl_str = TBBase.format_dec(wr_clk_period, 3)
    rcl_str = TBBase.format_dec(rd_clk_period, 3)
    # Updated test name format: includes test level in the main name
    test_name_plus_params = f"test_fifo_multi_sigmap_aw{aw_str}_cw{cw_str}_dw{dw_str}_d{d_str}_wcl{wcl_str}_rcl{rcl_str}_{mode}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes=[rtl_dict['rtl_amba_includes']]

    # RTL parameters - Handle string parameters specially for Verilator
    rtl_parameters = {}

    # Add numeric parameters normally
    rtl_parameters['ADDR_WIDTH'] = str(addr_width)
    rtl_parameters['CTRL_WIDTH'] = str(ctrl_width)
    rtl_parameters['DATA_WIDTH'] = str(data_width)
    rtl_parameters['DEPTH'] = str(depth)
    rtl_parameters['REGISTERED'] = str(registered)

    # Add string parameter with quotes for Verilator
    rtl_parameters['INSTANCE_NAME'] = f'"multi_{mode}_{test_level}"'  # Include test level in instance name

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 2, 'medium': 4, 'full': 8}
    base_timeout = 4000  # 4 seconds base for multi-signal testing
    timeout_ms = base_timeout * timeout_multipliers.get(test_level, 1)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        # 'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)  # Dynamic timeout
    }

    # Add test parameters; these are passed to the environment, but not the RTL
    extra_env['TEST_ADDR_WIDTH'] = str(addr_width)
    extra_env['TEST_CTRL_WIDTH'] = str(ctrl_width)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_CLK_WR'] = str(wr_clk_period)
    extra_env['TEST_CLK_RD'] = str(rd_clk_period)
    extra_env['TEST_MODE'] = mode
    extra_env['TEST_KIND'] = 'sync'

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace",  # Tell Verilator to use VCD
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} multi-signal test: {mode} mode, depth={depth}")
    print(f"Signal widths: addr={addr_width}, ctrl={ctrl_width}, data={data_width}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} multi-signal test PASSED: {mode} mode")
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"✗ {test_level.upper()} multi-signal test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
