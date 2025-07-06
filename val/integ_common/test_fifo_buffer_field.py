"""
FIFO Buffer Field Test with Parameterized Test Levels

This test uses test_level as a parameter for maximum flexibility:

TEST LEVELS:
    basic (3-5 min):   Quick verification during development
    medium (8-12 min): Integration testing for CI/branches
    full (20-30 min):  Comprehensive validation for regression

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
from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.fifo.fifo_buffer_field import FifoFieldBufferTB
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=4, timeout_unit="ms")  # Increased timeout for field testing
async def fifo_field_test(dut):
    '''Test the FIFO Buffer Field comprehensively with FlexConfigGen randomizers'''
    tb = FifoFieldBufferTB(dut, dut.i_clk, dut.i_rst_n, super_debug=False)

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

    tb.log.info(f"Running field test level: {test_level.upper()}")

    await tb.start_clock('i_clk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('i_clk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_clk', 5)
    tb.log.info(f"Starting {test_level.upper()} FIFO field test...")

    # Get available randomizer configurations from FlexConfigGen
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available field randomizer configs: {config_names}")

    # Define test configurations based on test level
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_configs = ['backtoback', 'fast', 'constrained', 'field_realistic']
        packet_counts = {
            'simple_loops': 3 * tb.TEST_DEPTH,
            'dependency_test': 6,
            'field_pattern_test': 10
        }
        run_comprehensive_sweep = False
        run_dependency_test = False
        run_field_pattern_tests = ['incremental']

    elif test_level == 'medium':
        # Moderate testing for development
        test_configs = [
            'backtoback', 'fast', 'constrained', 'bursty',
            'field_stress', 'field_realistic', 'field_pipeline',
            'moderate', 'balanced'
        ]
        packet_counts = {
            'simple_loops': 6 * tb.TEST_DEPTH,
            'dependency_test': 12,
            'field_pattern_test': 20
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 4 * tb.TEST_DEPTH
        run_dependency_test = True
        run_field_pattern_tests = ['incremental', 'alternating']

    else:  # test_level == 'full'
        # Comprehensive testing for validation
        essential_configs = [
            'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
            'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
            'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
            'field_stress', 'field_pipeline', 'field_burst', 'field_realistic',
            'field_fine_grain', 'field_depth_aware'
        ]
        test_configs = [config for config in essential_configs if config in config_names]
        packet_counts = {
            'simple_loops': 10 * tb.TEST_DEPTH,
            'dependency_test': 15,
            'field_pattern_test': 25
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 8 * tb.TEST_DEPTH
        run_dependency_test = True
        run_field_pattern_tests = ['incremental', 'alternating', 'comprehensive']

    # Filter to only test configs that exist
    test_configs = [config for config in test_configs if config in config_names]

    tb.log.info(f"Testing field configs with {len(test_configs)} configs: {test_configs}")
    tb.log.info(f"Field packet counts: {packet_counts}")

    # Run core field tests with different randomizer configurations
    for i, delay_key in enumerate(test_configs):
        tb.log.info(f"[{i+1}/{len(test_configs)}] Testing field with '{delay_key}' randomizer configuration")
        await tb.simple_incremental_loops(
            count=packet_counts['simple_loops'],
            delay_key=delay_key,
            delay_clks_after=12
        )
        tb.log.info(f"✓ Completed field '{delay_key}' configuration")

    # Run comprehensive sweep for medium and full levels
    if run_comprehensive_sweep:
        tb.log.info("Running comprehensive field randomizer sweep...")
        await tb.comprehensive_randomizer_sweep(packets_per_config=comprehensive_packets)
        tb.log.info("✓ Completed comprehensive field sweep")

    # Run dependency test for medium and full levels
    if run_dependency_test:
        tb.log.info("Running field dependency test...")
        dependency_config = 'field_stress' if 'field_stress' in config_names else 'stress'
        await tb.dependency_test(
            count=packet_counts['dependency_test'],
            delay_key=dependency_config
        )
        tb.log.info("✓ Completed field dependency test")

    # Run field pattern tests
    for pattern_type in run_field_pattern_tests:
        tb.log.info(f"Running field pattern test: {pattern_type}...")
        await tb.field_pattern_test(
            pattern_type=pattern_type,
            count=packet_counts['field_pattern_test']
        )
        tb.log.info(f"✓ Completed field pattern test: {pattern_type}")

    tb.log.info(f"✓ ALL {test_level.upper()} FIELD TESTS PASSED!")


def generate_params():
    """
    Generate test parameters for field testing. Modify this function to limit test scope for debugging.
    
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
    depths = [2, 4, 6, 8]  # Test multiple depths for field testing
    # depths = [4]  # For debugging
    wr_clk_periods = [10]
    rd_clk_periods = [10]
    registered = [0, 1]
    # test_levels = ['basic', 'medium', 'full']  # All test levels
    test_levels = ['full']  # For initial testing
    return [(4, 5, 8, 4, 10, 10, 0, 'full')]
    # return list(product(addr_widths, ctrl_widths, data_widths, depths, wr_clk_periods, rd_clk_periods, registered, test_levels))

params = generate_params()

@pytest.mark.parametrize("addr_width, ctrl_width, data_width, depth, wr_clk_period, rd_clk_period, registered, test_level", params)
def test_fifo_buffer_field(request, addr_width, ctrl_width, data_width, depth, wr_clk_period, rd_clk_period, registered, test_level):
    """
    Parameterized FIFO buffer field test with configurable test levels.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (3-5 min)
    - medium: Integration testing (8-12 min)
    - full: Comprehensive validation (20-30 min)

    For quick debugging: Modify generate_params() function to return only specific combinations
    """
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })
    mode_list = ['fifo_mux', 'fifo_flop']
    mode = mode_list[registered]

    # set up all of the test names
    dut_name = "fifo_sync"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier with test level
    aw_str = TBBase.format_dec(addr_width, 3)
    cw_str = TBBase.format_dec(ctrl_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wcl_str = TBBase.format_dec(wr_clk_period, 3)
    rcl_str = TBBase.format_dec(rd_clk_period, 3)
    # Updated test name format: includes test level in the main name
    test_name_plus_params = f"test_fifo_field_aw{aw_str}_cw{cw_str}_dw{dw_str}_d{d_str}_wcl{wcl_str}_rcl{rcl_str}_{mode}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters - Handle string parameters specially for Verilator
    rtl_parameters = {}

    # Calculate total data width for field configuration
    total_data_width = addr_width + ctrl_width + data_width + data_width  # addr + ctrl + data0 + data1

    # Add numeric parameters normally
    rtl_parameters['DATA_WIDTH'] = str(total_data_width)
    rtl_parameters['DEPTH'] = str(depth)
    rtl_parameters['REGISTERED'] = str(registered)

    # Add string parameter with quotes for Verilator
    rtl_parameters['INSTANCE_NAME'] = f'"field_{mode}_{test_level}"'  # Include test level in instance name

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 1.5, 'medium': 3, 'full': 6}
    base_timeout = 3000  # 3 seconds base for field testing
    timeout_ms = base_timeout * timeout_multipliers.get(test_level, 1)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
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

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace-fst",  # Tell Verilator to use FST
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "+trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} field test: {mode} mode, depth={depth}")
    print(f"Field widths: addr={addr_width}, ctrl={ctrl_width}, data={data_width}")
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
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} field test PASSED: {mode} mode")
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"✗ {test_level.upper()} field test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
