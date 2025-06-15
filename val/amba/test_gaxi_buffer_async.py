"""
GAXI Async Buffer Test with Parameterized Test Levels

This test uses test_level as a parameter for maximum flexibility:

TEST LEVELS:
    basic (3-5 min):   Quick verification during development
    medium (8-12 min): Integration testing for CI/branches
    full (20-35 min):  Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - data_width: [8, 16, 32]
    - depth: [2, 4, 8]
    - wr_clk: [8, 10, 12, 20] (write clock periods in ns)
    - rd_clk: [8, 10, 12, 20] (read clock periods in ns)
    - mode: [skid, fifo_mux, fifo_flop]
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
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=5, timeout_unit="ms")  # Increased timeout for async testing
async def gaxi_async_test(dut):
    '''Test the GAXI Async Buffer comprehensively with FlexConfigGen randomizers'''
    # For async, we need to pass both clock signals
    tb = GaxiBufferTB(
        dut, 
        wr_clk=dut.i_axi_wr_aclk, 
        wr_rstn=dut.i_axi_wr_aresetn,
        rd_clk=dut.i_axi_rd_aclk, 
        rd_rstn=dut.i_axi_rd_aresetn
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

    tb.log.info(f"Running ASYNC test level: {test_level.upper()}")

    # Start both clocks with different periods
    wr_clk_period = int(os.environ.get('TEST_CLK_WR', '10'))
    rd_clk_period = int(os.environ.get('TEST_CLK_RD', '10'))
    
    tb.log.info(f"Starting clocks: WR={wr_clk_period}ns, RD={rd_clk_period}ns")
    await tb.start_clock('i_axi_wr_aclk', wr_clk_period, 'ns')
    await tb.start_clock('i_axi_rd_aclk', rd_clk_period, 'ns')
    
    # Reset sequence for async
    await tb.assert_reset()
    await tb.wait_clocks('i_axi_wr_aclk', 5)
    await tb.wait_clocks('i_axi_rd_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('i_axi_wr_aclk', 5)
    await tb.wait_clocks('i_axi_rd_aclk', 5)
    
    tb.log.info(f"Starting {test_level.upper()} GAXI ASYNC test...")

    # Get available randomizer configurations from FlexConfigGen
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available randomizer configs: {config_names}")

    # Define test configurations based on test level
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_configs = ['backtoback', 'fast', 'constrained']
        packet_counts = {
            'simple_loops': 6 * tb.TEST_DEPTH,  # Slightly more for async
            'back_to_back': 20,
            'stress_test': 30
        }
        run_comprehensive_sweep = False
        run_stress_test = False

    elif test_level == 'medium':
        # Moderate testing for development
        test_configs = [
            'backtoback', 'fast', 'constrained', 'bursty',
            'gaxi_stress', 'gaxi_realistic', 'moderate', 'chaotic'
        ]
        packet_counts = {
            'simple_loops': 10 * tb.TEST_DEPTH,
            'back_to_back': 40,
            'stress_test': 75
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 8 * tb.TEST_DEPTH
        run_stress_test = True

    else:  # test_level == 'full'
        # Comprehensive testing for validation
        essential_configs = [
            'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
            'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
            'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
            'gaxi_stress', 'gaxi_pipeline', 'gaxi_backpressure',
            'gaxi_realistic', 'gaxi_burst_heavy', 'gaxi_fine_grain'
        ]
        test_configs = [config for config in essential_configs if config in config_names]
        packet_counts = {
            'simple_loops': 15 * tb.TEST_DEPTH,
            'back_to_back': 60,
            'stress_test': 120
        }
        run_comprehensive_sweep = True
        comprehensive_packets = 12 * tb.TEST_DEPTH
        run_stress_test = True

    # Filter to only test configs that exist
    test_configs = [config for config in test_configs if config in config_names]

    tb.log.info(f"Testing with {len(test_configs)} configs: {test_configs}")
    tb.log.info(f"Packet counts: {packet_counts}")

    # Calculate additional wait time based on clock ratio for async operations
    clk_ratio = max(wr_clk_period, rd_clk_period) / min(wr_clk_period, rd_clk_period)
    async_wait_multiplier = max(2, int(clk_ratio * 1.5))
    
    tb.log.info(f"Clock ratio: {clk_ratio:.2f}, async wait multiplier: {async_wait_multiplier}")

    # Run core tests with different randomizer configurations
    for i, delay_key in enumerate(test_configs):
        tb.log.info(f"[{i+1}/{len(test_configs)}] Testing with '{delay_key}' randomizer configuration")
        await tb.simple_incremental_loops(
            count=packet_counts['simple_loops'],
            delay_key=delay_key,
            delay_clks_after=20 * async_wait_multiplier  # More time for async
        )
        tb.log.info(f"✓ Completed '{delay_key}' configuration")

    # Run comprehensive sweep for medium and full levels
    if run_comprehensive_sweep:
        tb.log.info("Running comprehensive randomizer sweep...")
        await tb.comprehensive_randomizer_sweep(packets_per_config=comprehensive_packets)
        tb.log.info("✓ Completed comprehensive sweep")

    # Always run back-to-back test (essential for GAXI validation)
    tb.log.info("Running back-to-back test...")
    await tb.back_to_back_test(count=packet_counts['back_to_back'])
    tb.log.info("✓ Completed back-to-back test")

    # Run stress test for medium and full levels
    if run_stress_test:
        tb.log.info("Running stress test...")
        stress_config = 'gaxi_stress' if 'gaxi_stress' in config_names else 'stress'
        await tb.stress_test_with_random_patterns(
            count=packet_counts['stress_test'],
            delay_key=stress_config
        )
        tb.log.info("✓ Completed stress test")

    # Async-specific test: Clock domain crossing stress test
    if test_level in ['medium', 'full']:
        tb.log.info("Running async clock domain crossing test...")
        await tb.stress_test_with_random_patterns(
            count=packet_counts['stress_test'] // 2,
            delay_key='chaotic'  # Use chaotic timing for CDC stress
        )
        tb.log.info("✓ Completed CDC stress test")

    tb.log.info(f"✓ ALL {test_level.upper()} ASYNC TESTS PASSED!")


def generate_params():
    """
    Generate test parameters for async testing with independent clock configurations.
    
    Examples for quick debugging:
        # Single test case:
        return [(8, 4, 10, 12, 'skid', 'basic')]
        
        # Test specific clock ratios:
        return [(8, 4, 8, 10, 'fifo_mux', 'basic'),   # 1.25x ratio
                (8, 4, 10, 20, 'fifo_mux', 'basic')]  # 2x ratio
        
        # Test only basic level:
        wr_clk = [10]
        rd_clk = [12] 
        return list(product([8], [4], wr_clk, rd_clk, ['skid'], ['basic']))
    """
    widths = [8]
    depths = [4, 6, 8]  # Focus on moderate depths for async
    
    # Independent clock configurations - test various ratios
    wr_clk = [8, 10, 12, 20]  # Write clock periods
    rd_clk = [8, 10, 12, 20]  # Read clock periods
    
    modes = ['skid', 'fifo_mux', 'fifo_flop']
    # test_levels = ['basic', 'medium', 'full']
    test_levels = ['full']
    # Generate all combinations
    all_params = list(product(widths, depths, wr_clk, rd_clk, modes, test_levels))
    
    # Filter out some combinations to keep test time reasonable
    filtered_params = []
    for width, depth, wr_period, rd_period, mode, level in all_params:
        # For basic level, test fewer clock combinations
        if level == 'basic':
            # Only test same clocks and a couple different ratios
            if wr_period == rd_period or (wr_period, rd_period) in [(8, 12), (12, 8), (10, 20)]:
                filtered_params.append((width, depth, wr_period, rd_period, mode, level))
        
        # For medium level, test more combinations but not all
        elif level == 'medium':
            # Test ratios up to 2.5x
            ratio = max(wr_period, rd_period) / min(wr_period, rd_period)
            if ratio <= 2.5:
                filtered_params.append((width, depth, wr_period, rd_period, mode, level))
        
        # For full level, test all combinations
        else:
            filtered_params.append((width, depth, wr_period, rd_period, mode, level))
    
    return [(8, 4, 10, 12, 'skid', 'basic'), (8, 4, 10, 12, 'fifo_mux', 'basic'), (8, 4, 10, 12, 'fifo_flop', 'basic')]
    # return filtered_params


params = generate_params()

@pytest.mark.parametrize("data_width, depth, wr_clk_period, rd_clk_period, mode, test_level", params)
def test_gaxi_buffer_async(request, data_width, depth, wr_clk_period, rd_clk_period, mode, test_level):
    """
    Parameterized GAXI async buffer test with configurable test levels and independent clock domains.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (3-5 min)
    - medium: Integration testing (8-12 min)
    - full: Comprehensive validation (20-35 min)

    Clock configurations test various CDC scenarios:
    - Same clocks: wr_clk = rd_clk (basic CDC validation)
    - Slow write/fast read: wr_clk > rd_clk (backpressure scenarios)
    - Fast write/slow read: wr_clk < rd_clk (buffering scenarios)
    - Extreme ratios: up to 2.5x difference (stress testing)

    For quick debugging: Modify generate_params() function to return only specific combinations
    """
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba': 'rtl/amba'
    })

    # set up all of the test names based on async modules
    if mode == 'skid':
        dut_name = "gaxi_skid_buffer_async"
    else:
        dut_name = "gaxi_fifo_async"
    toplevel = dut_name

    # Get verilog sources based on mode for async versions
    # 
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "find_first_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "find_last_set.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "leading_one_trailing_one.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_johnson.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "grayj2bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi_fifo_async.sv"),
    ]

    if mode == 'skid':
        verilog_sources.append(os.path.join(rtl_dict['rtl_amba'], "gaxi_skid_buffer.sv"))
        verilog_sources.append(os.path.join(rtl_dict['rtl_amba'], "gaxi_skid_buffer_async.sv"))

    # create a human readable test identifier with clock information
    w_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    wr_str = TBBase.format_dec(wr_clk_period, 3)
    rd_str = TBBase.format_dec(rd_clk_period, 3)
    
    # Calculate clock ratio for test name
    clk_ratio = max(wr_clk_period, rd_clk_period) / min(wr_clk_period, rd_clk_period)
    ratio_str = f"r{clk_ratio:.1f}".replace('.', 'p')  # r2p0 for 2.0x ratio
    
    test_name_plus_params = f"test_gaxi_async_{mode}_w{w_str}_d{d_str}_wr{wr_str}_rd{rd_str}_{ratio_str}_{test_level}"
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

    # Add numeric parameters normally
    for param_name in ['data_width', 'depth']:
        if param_name in locals():
            rtl_parameters[param_name.upper()] = str(locals()[param_name])

    # Add async-specific parameters
    rtl_parameters['N_FLOP_CROSS'] = '3'  # Standard 3-flop synchronizer

    # Add string parameter with quotes for Verilator
    rtl_parameters['INSTANCE_NAME'] = f'"{mode}_async_{test_level}"'
    if 'fifo' in mode:
        rtl_parameters['REGISTERED'] = str(1) if mode == 'fifo_flop' else str(0)

    # Adjust timeout based on test level and clock ratio
    timeout_multipliers = {'basic': 1.5, 'medium': 3, 'full': 6}  # Higher for async
    base_timeout = 3000  # 3 seconds base for async
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * clk_ratio)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)  # Dynamic timeout
    }

    # Add test parameters for async testing
    extra_env['TEST_DATA_WIDTH'] = str(data_width)
    extra_env['TEST_DEPTH'] = str(depth)
    extra_env['TEST_CLK_WR'] = str(wr_clk_period)  # Write clock period
    extra_env['TEST_CLK_RD'] = str(rd_clk_period)  # Read clock period
    extra_env['TEST_MODE'] = mode
    extra_env['TEST_KIND'] = 'async'  # Important: tells TB this is async

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace-fst",
        "--trace-structs", 
        "--trace-depth", "99",
    ]

    plusargs = [
        "+trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} ASYNC test: {mode} mode")
    print(f"Config: depth={depth}, width={data_width}")
    print(f"Clocks: WR={wr_clk_period}ns, RD={rd_clk_period}ns (ratio: {clk_ratio:.1f}x)")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*80}")

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
        print(f"✓ {test_level.upper()} ASYNC test PASSED: {mode} mode (WR:{wr_clk_period}ns/RD:{rd_clk_period}ns)")
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"✗ {test_level.upper()} ASYNC test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
