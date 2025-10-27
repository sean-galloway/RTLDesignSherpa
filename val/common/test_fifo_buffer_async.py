# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_fifo_buffer_async
# Purpose: Asynchronous FIFO Buffer Test with Parameterized Test Levels
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Asynchronous FIFO Buffer Test with Parameterized Test Levels

This test uses test_level as a parameter for maximum flexibility, matching the sync version:

TEST LEVELS:
    basic (2-3 min):   Quick verification during development
    medium (5-8 min):  Integration testing for CI/branches
    full (15-25 min):  Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - data_width: [8]
    - depth: [4, 8, 16] (async FIFOs need power-of-2 depths for standard gray counters)
    - wr_clk_periods: [10]
    - rd_clk_periods: [8, 12] (different to test async behavior)
    - registered: [0=mux, 1=flop] (ADDED - matches sync version)
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
"""

import os
import sys
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=4, timeout_unit="ms")  # Increased timeout for async complexity
async def fifo_async_test(dut):
    '''Test the Asynchronous FIFO Buffer comprehensively with FlexConfigGen randomizers'''
    # Create testbench with separate write and read clocks and reset signals
    tb = FifoBufferTB(
        dut,
        wr_clk=dut.wr_clk,
        wr_rstn=dut.wr_rst_n,
        rd_clk=dut.rd_clk,
        rd_rstn=dut.rd_rst_n
    )

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

    tb.log.info(f"Running async test level: {test_level.upper()}")

    # Start both clocks with possibly different periods - ASYNC SPECIFIC
    await tb.start_clock('wr_clk', tb.TEST_CLK_WR, 'ns')
    await tb.start_clock('rd_clk', tb.TEST_CLK_RD, 'ns')

    # Reset sequence - ASYNC SPECIFIC (both clock domains)
    await tb.assert_reset()
    await tb.wait_clocks('wr_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('wr_clk', 5)
    tb.log.info(f"Starting {test_level.upper()} ASYNC FIFO test...")

    # Get available randomizer configurations from FlexConfigGen
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available randomizer configs: {config_names}")

    # Define test configurations based on test level - SAME AS SYNC
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_configs = ['backtoback', 'fast', 'constrained']
        packet_counts = {
            'simple_loops': 4 * tb.TEST_DEPTH,
            'back_to_back': 15,
            'stress_test': 20
        }
        run_comprehensive_sweep = False
        run_stress_test = False

    elif test_level == 'medium':
        # Moderate testing for development
        test_configs = [
            'backtoback', 'fast', 'constrained', 'bursty',
            'fifo_stress', 'fifo_realistic', 'moderate'
        ]
        packet_counts = {
            'simple_loops': 8 * tb.TEST_DEPTH,
            'back_to_back': 30,
            'stress_test': 50
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 6 * tb.TEST_DEPTH
        run_stress_test = True

    else:  # test_level == 'full'
        # Comprehensive testing for validation
        essential_configs = [
            'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
            'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
            'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
            'fifo_stress', 'fifo_pipeline', 'fifo_overflow', 'fifo_underflow',
            'fifo_realistic', 'fifo_burst_heavy', 'fifo_fine_grain'
        ]
        test_configs = [config for config in essential_configs if config in config_names]
        packet_counts = {
            'simple_loops': 12 * tb.TEST_DEPTH,
            'back_to_back': 50,
            'stress_test': 100
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 10 * tb.TEST_DEPTH
        run_stress_test = True

    # Filter to only test configs that exist
    test_configs = [config for config in test_configs if config in config_names]

    tb.log.info(f"Testing with {len(test_configs)} configs: {test_configs}")
    tb.log.info(f"Packet counts: {packet_counts}")

    # Run core tests with different randomizer configurations - SAME AS SYNC
    for i, delay_key in enumerate(test_configs):
        tb.log.info(f"[{i+1}/{len(test_configs)}] Testing with '{delay_key}' randomizer configuration")
        await tb.simple_incremental_loops(
            count=packet_counts['simple_loops'],
            delay_key=delay_key,
            delay_clks_after=30  # ASYNC SPECIFIC - longer delay for clock domain crossing
        )
        tb.log.info(f"✓ Completed '{delay_key}' configuration")

    # Run comprehensive sweep for medium and full levels
    if run_comprehensive_sweep:
        tb.log.info("Running comprehensive randomizer sweep...")
        await tb.comprehensive_randomizer_sweep(packets_per_config=comprehensive_packets)
        tb.log.info("✓ Completed comprehensive sweep")

    # Always run back-to-back test (essential for FIFO validation)
    tb.log.info("Running back-to-back test...")
    await tb.back_to_back_test(count=packet_counts['back_to_back'])
    tb.log.info("✓ Completed back-to-back test")

    # Run stress test for medium and full levels
    if run_stress_test:
        tb.log.info("Running stress test...")
        stress_config = 'fifo_stress' if 'fifo_stress' in config_names else 'stress'
        await tb.stress_test_with_random_patterns(
            count=packet_counts['stress_test'],
            delay_key=stress_config
        )
        tb.log.info("✓ Completed stress test")

    tb.log.info(f"✓ ALL {test_level.upper()} ASYNC TESTS PASSED!")


def generate_params():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (depth 4, both clocks, both modes, basic)
    REG_LEVEL=FUNC: ~8 tests (depths 4, 8, both clocks, both modes, basic+medium) - default
    REG_LEVEL=FULL: ~36 tests (depths 4, 8, 16, both clocks, both modes, all levels)

    Examples for quick debugging:
        # Single test case:
        return [(8, 4, 10, 8, 0, 'basic')]
    """
    import os
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    widths = [8]
    wr_clk_periods = [10]

    if reg_level == 'GATE':
        # Quick smoke test
        depths = [4]  # Power of 2
        rd_clk_periods = [8, 12]  # Different clocks to test async
        registered = [0, 1]
        test_levels = ['basic']
    elif reg_level == 'FUNC':
        # Functional coverage (default)
        depths = [4, 8]  # Power of 2 depths for Gray counters
        rd_clk_periods = [8, 12]
        registered = [0, 1]
        test_levels = ['basic', 'medium']
    else:  # FULL
        # Comprehensive validation
        depths = [4, 8, 16]  # Power of 2 depths for standard async FIFOs
        rd_clk_periods = [8, 12]
        registered = [0, 1]
        test_levels = ['basic', 'medium', 'full']

    return list(product(widths, depths, wr_clk_periods, rd_clk_periods, registered, test_levels))

params = generate_params()

@pytest.mark.parametrize("data_width, depth, wr_clk_period, rd_clk_period, registered, test_level", params)
def test_fifo_async(request, data_width, depth, wr_clk_period, rd_clk_period, registered, test_level):
    """
    Parameterized asynchronous FIFO buffer test with configurable test levels.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (2-3 min)
    - medium: Integration testing (5-8 min)  
    - full: Comprehensive validation (15-25 min)

    For quick debugging: Modify generate_params() function to return only specific combinations
    """
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })
    
    # Generate mode string from registered parameter (matches sync version exactly)
    mode_list = ['fifo_mux', 'fifo_flop']
    mode = mode_list[registered]

    # set up all of the test names
    dut_name = "fifo_async"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/fifo_async.f'
    )

    # create a human readable test identifier with test level (matches sync version exactly)
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wcl_str = TBBase.format_dec(wr_clk_period, 3)
    rcl_str = TBBase.format_dec(rd_clk_period, 3)
    # Updated test name format: includes test level in the main name (matches sync version)
    test_name_plus_params = f"test_fifo_async_w{w_str}_d{d_str}_wcl{wcl_str}_rcl{rcl_str}_{mode}_{test_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters - Handle string parameters specially for Verilator (matches sync version)
    rtl_parameters = {}

    # Add numeric parameters normally (ADDED registered parameter)
    for param_name in ['registered', 'data_width', 'depth']:
        if param_name in locals():
            rtl_parameters[param_name.upper()] = str(locals()[param_name])

    # Add string parameter with quotes for Verilator (matches sync version)
    rtl_parameters['INSTANCE_NAME'] = f'"{mode}_{test_level}"'  # Include test level in instance name

    # Adjust timeout based on test level (slightly longer than sync due to async complexity)
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    base_timeout = 3000  # 3 seconds base for async (longer than sync's 2 seconds)
    timeout_ms = base_timeout * timeout_multipliers.get(test_level, 1)

    # Environment variables (matches sync version exactly, except TEST_KIND)
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

    # Add test parameters; these are passed to the environment, but not the RTL (matches sync version)
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_CLK_WR'] = str(wr_clk_period)
    extra_env['TEST_CLK_RD'] = str(rd_clk_period)
    extra_env['TEST_MODE'] = mode  # ADDED - matches sync version
    extra_env['TEST_KIND'] = 'async'  # CHANGED from sync version

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} async test: {mode} mode, depth={depth}, width={data_width}")
    print(f"Write CLK: {wr_clk_period}ns, Read CLK: {rd_clk_period}ns")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")


    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

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
        print(f"✓ {test_level.upper()} async test PASSED: {mode} mode")
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"✗ {test_level.upper()} async test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
