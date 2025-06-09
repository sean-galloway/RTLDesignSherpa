"""
Updated test file for fifo_data_collect module with modern framework and FlexConfigGen
"""
import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.fifo.fifo_data_collect_tb import DataCollectTB


@cocotb.test(timeout_time=10, timeout_unit="ms")  # Increased timeout for comprehensive testing
async def fifo_data_collect_test(dut):
    """Test the FIFO Data Collect module comprehensively with FlexConfigGen randomizers"""
    tb = DataCollectTB(dut)

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

    tb.log.info(f"Running data collect test level: {test_level.upper()}")

    # Start clock
    await tb.start_clock('i_clk', 10, 'ns')

    # Get available randomizer configurations from FlexConfigGen
    config_names = tb.get_randomizer_config_names()
    tb.log.info(f"Available data collect randomizer configs: {config_names}")

    # Define test configurations based on test level
    if test_level == 'basic':
        # Minimal testing for quick verification
        packet_counts = {
            'simple_test': 8,
            'randomizer_sweep': 12,
            'weighted_arbiter': 16
        }
        run_randomizer_sweep = False
        run_weighted_arbiter_test = False
        run_stress_test = False

    elif test_level == 'medium':
        # Moderate testing for development
        packet_counts = {
            'simple_test': 20,
            'randomizer_sweep': 16,
            'weighted_arbiter': 24
        }
        run_randomizer_sweep = True
        run_weighted_arbiter_test = True
        run_stress_test = False

    else:  # test_level == 'full'
        # Comprehensive testing for validation
        packet_counts = {
            'simple_test': 40,
            'randomizer_sweep': 24,
            'weighted_arbiter': 32
        }
        run_randomizer_sweep = True
        run_weighted_arbiter_test = True
        run_stress_test = True

    tb.log.info(f"Data collect packet counts: {packet_counts}")

    # Run simple test with equal weights on all channels
    tb.log.info("Running simple test with equal weights and arbiter monitoring...")
    result = await tb.run_simple_test(
        packets_per_channel=packet_counts['simple_test'], 
        expected_outputs=packet_counts['simple_test'] * len(tb.channels) // tb.CHUNKS
    )
    assert result, f"Simple test failed with {tb.total_errors} errors{tb.get_time_ns_str()}"
    tb.log.info("✓ Simple test with arbiter monitoring passed!")

    # Run comprehensive randomizer sweep for medium and full levels
    if run_randomizer_sweep:
        tb.log.info("Running comprehensive data collect randomizer sweep...")
        await tb.run_comprehensive_randomizer_sweep(packets_per_config=packet_counts['randomizer_sweep'])
        tb.log.info("✓ Completed comprehensive data collect randomizer sweep")

    # Run weighted arbiter test for medium and full levels  
    if run_weighted_arbiter_test:
        tb.log.info("Running weighted arbiter test...")
        arbiter_result = await tb.run_weighted_arbiter_test()
        assert arbiter_result, f"Weighted arbiter test failed{tb.get_time_ns_str()}"
        tb.log.info("✓ Weighted arbiter test passed!")

    # Run stress test for full level only
    if run_stress_test:
        tb.log.info("Running stress test...")
        stress_result = await tb.run_stress_test(duration_clocks=5000)
        assert stress_result, f"Stress test failed{tb.get_time_ns_str()}"
        tb.log.info("✓ Stress test passed!")

    # Final verification
    if tb.arbiter_monitor:
        arb_stats = tb.get_arbiter_statistics()
        tb.log.info(f"Final arbiter monitor statistics: {arb_stats}")

        # Verify we captured some arbiter transactions
        assert arb_stats.get('total_grants', 0) > 0, "Arbiter monitor should have captured grants"

        # Check fairness
        fairness = arb_stats.get('fairness_index', 0)
        tb.log.info(f"Final arbiter fairness index: {fairness}")

    # Get final component statistics
    final_stats = tb.get_component_statistics()
    tb.log.info(f"Final component statistics: {final_stats}")

    tb.log.info(f"✓ ALL {test_level.upper()} DATA COLLECT TESTS PASSED!")


def generate_params():
    """
    Generate test parameters for data collect testing. Modify this function to limit test scope for debugging.
    
    Examples for quick debugging:
        # Single test case:
        return [(8, 4, 16, 'basic')]
        
        # Test only basic level:
        data_widths = [8]
        id_widths = [4] 
        output_fifo_depths = [16]
        test_levels = ['basic']  # Only basic
        return list(product(data_widths, id_widths, output_fifo_depths, test_levels))
        
        # Test all levels:
        data_widths = [8, 16]
        id_widths = [4, 8]
        output_fifo_depths = [16, 32]
        test_levels = ['basic', 'medium', 'full']  # All test levels
        return list(product(data_widths, id_widths, output_fifo_depths, test_levels))
    """
    data_widths = [8, 16]
    id_widths = [4, 8]
    output_fifo_depths = [16, 32]
    test_levels = ['basic', 'medium', 'full']  # All test levels
    return [(8, 4, 16, 'basic')]  # For quick debugging
    # return list(product(data_widths, id_widths, output_fifo_depths, test_levels))

params = generate_params()

@pytest.mark.parametrize("data_width, id_width, output_fifo_depth, test_level", params)
def test_fifo_data_collect(request, data_width, id_width, output_fifo_depth, test_level):
    """
    Parameterized FIFO data collect test with FlexConfigGen and configurable test levels.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (4-6 min)
    - medium: Integration testing (10-15 min)  
    - full: Comprehensive validation (25-35 min)

    For quick debugging: Modify generate_params() function to return only specific combinations
    """
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_cmn_integ': 'rtl/integ_common',
    })

    # set up test names
    dut_name = "fifo_data_collect"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_fixed_priority.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_subinst.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_cmn_integ'], f"{dut_name}.sv"),
    ]

    # Create a human-readable test identifier with test level
    dw_str = TBBase.format_dec(data_width, 2)
    idw_str = TBBase.format_dec(id_width, 2)
    fifo_str = TBBase.format_dec(output_fifo_depth, 2)
    # Updated test name format: includes test level in the main name
    test_name_plus_params = f"test_{dut_name}_flexgen_dw{dw_str}_idw{idw_str}_fifo{fifo_str}_{test_level}"
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
    rtl_parameters['DATA_WIDTH'] = str(data_width)
    rtl_parameters['ID_WIDTH'] = str(id_width)
    rtl_parameters['OUTPUT_FIFO_DEPTH'] = str(output_fifo_depth)
    rtl_parameters['CHUNKS'] = '4'  # Standard chunks for data collect

    # Add string parameter with quotes for Verilator
    rtl_parameters['INSTANCE_NAME'] = f'"data_collect_{test_level}"'  # Include test level in instance name

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 2, 'medium': 4, 'full': 8}
    base_timeout = 6000  # 6 seconds base for data collect testing
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
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),  # Dynamic timeout
        'DATA_WIDTH': str(data_width),
        'ID_WIDTH': str(id_width),
        'OUTPUT_FIFO_DEPTH': str(output_fifo_depth),
        'CHUNKS': '4'
    }

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
    print(f"Running {test_level.upper()} data collect test with FlexConfigGen")
    print(f"Parameters: data_width={data_width}, id_width={id_width}, fifo_depth={output_fifo_depth}")
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
        print(f"✓ {test_level.upper()} data collect test PASSED with FlexConfigGen")
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"✗ {test_level.upper()} data collect test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
