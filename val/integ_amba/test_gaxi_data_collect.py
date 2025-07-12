"""
GAXI Data Collect Test with Parameterized Test Levels and FlexConfigGen Integration

This test uses test_level as a parameter for maximum flexibility, following the
methodology from the FIFO data collect test runner:

TEST LEVELS:
    basic (2-3 min):   Quick verification during development
    medium (5-8 min):  Integration testing for CI/branches
    full (15-25 min):  Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - data_width: [8]
    - id_width: [4, 8]
    - fifo_depth: [8, 16, 32]
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
from CocoTBFramework.tbclasses.misc.tbbase import TBBase
from CocoTBFramework.tbclasses.gaxi.gaxi_data_collect_tb import GAXIDataCollectTB
from CocoTBFramework.tbclasses.misc.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=8, timeout_unit="ms")  # Increased timeout for comprehensive testing
async def gaxi_data_collect_test(dut):
    '''Test the GAXI Data Collect comprehensively with FlexConfigGen arbitration randomizers'''
    tb = GAXIDataCollectTB(dut)

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

    tb.log.info(f"Running test level: {test_level.upper()}")

    await tb.start_clock('axi_aclk', 10, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('axi_aclk', 5)
    await tb.deassert_reset()
    await tb.wait_clocks('axi_aclk', 5)
    tb.log.info(f"Starting {test_level.upper()} GAXI Data Collect test...")

    # Get available randomizer configurations from FlexConfigGen
    available_profiles = tb.get_available_profiles()
    tb.log.info(f"Available arbitration randomizer profiles: {available_profiles}")

    # Define test configurations based on test level
    if test_level == 'basic':
        # Minimal testing for quick verification
        test_profiles = ['arbitration_balanced', 'arbitration_fair']
        weight_configs = [
            (8, 8, 8, 8),  # Equal weights
            (12, 4, 2, 1), # Weighted A>B>C>D
        ]
        packets_per_channel = 16
        run_arbiter_analysis = False
        run_stress_test = False

    elif test_level == 'medium':
        # Moderate testing for development
        test_profiles = [
            'arbitration_balanced', 'arbitration_fair', 'arbitration_stress',
            'arbitration_burst', 'arbitration_coordinated'
        ]
        weight_configs = [
            (8, 8, 8, 8),  # Equal weights
            (15, 5, 3, 1), # Heavily weighted A
            (1, 15, 1, 1), # Heavily weighted B
            (4, 8, 12, 0), # C gets most, D gets none
        ]
        packets_per_channel = 32
        run_arbiter_analysis = True
        run_stress_test = True

    else:  # test_level == 'full'
        # Comprehensive testing for validation
        essential_profiles = [
            'arbitration_balanced', 'arbitration_fair', 'arbitration_stress',
            'arbitration_burst', 'arbitration_coordinated', 'arbitration_chaotic',
            'arbitration_weighted', 'backtoback', 'fast', 'constrained',
            'bursty', 'moderate', 'balanced'
        ]
        test_profiles = [profile for profile in essential_profiles if profile in available_profiles]
        weight_configs = [
            (8, 8, 8, 8),  # Equal weights
            (15, 5, 3, 1), # Heavily weighted A
            (1, 15, 1, 1), # Heavily weighted B
            (8, 8, 8, 8),  # All equal
            (4, 8, 12, 0), # C gets most, D gets none
            (2, 4, 8, 2),  # C gets most, A and D get least
            (0, 10, 10, 0), # Only B and C active
        ]
        packets_per_channel = 48
        run_arbiter_analysis = True
        run_stress_test = True

    # Filter to only test profiles that exist
    test_profiles = [profile for profile in test_profiles if profile in available_profiles]

    tb.log.info(f"Testing with {len(test_profiles)} profiles: {test_profiles}")
    tb.log.info(f"Testing with {len(weight_configs)} weight configurations")
    tb.log.info(f"Packets per channel: {packets_per_channel}")

    # Run core arbitration tests with different profiles and weights
    test_results = {}

    for i, profile in enumerate(test_profiles):
        tb.log.info(f"[{i+1}/{len(test_profiles)}] Testing arbitration profile '{profile}'")

        # Set the randomizer profile for this test
        tb.set_randomizer_profile(profile)

        for j, weights in enumerate(weight_configs):
            test_name = f"{profile}_weights_{weights}"
            tb.log.info(f"  [{j+1}/{len(weight_configs)}] Testing weights: {weights}")

            # Reset statistics and set weights
            tb.reset_statistics()
            tb.set_arbiter_weights(*weights)
            tb.start_arbiter_monitoring()

            # Run basic arbitration test
            await tb.run_basic_arbitration_test(
                packets_per_channel=packets_per_channel,
                weights=weights,
                profile=profile
            )

            # Verify arbiter behavior
            weight_compliance = tb.verify_arbiter_behavior(tolerance=0.3)  # More lenient for arbitration
            if not weight_compliance:
                tb.log.warning(f"Weight compliance issue for {test_name}")

            # Store results
            stats = tb.get_statistics()
            test_results[test_name] = {
                'profile': profile,
                'weights': weights,
                'stats': stats,
                'weight_compliance': weight_compliance
            }

            tb.log.info(f"✓ Completed test: {test_name}")

    # Run fairness analysis for medium and full levels
    if run_arbiter_analysis:
        tb.log.info("Running comprehensive arbiter fairness analysis...")
        await tb.run_fairness_analysis_test(test_profiles[:3])  # Test top 3 profiles
        tb.log.info("✓ Completed fairness analysis")

    # Run stress test for medium and full levels
    if run_stress_test:
        tb.log.info("Running arbiter stress test...")
        # Use a stress-optimized profile
        stress_profile = 'arbitration_stress' if 'arbitration_stress' in available_profiles else 'stress'
        tb.set_randomizer_profile(stress_profile)
        await tb.run_stress_arbitration_test(duration_packets=packets_per_channel * 4)
        tb.log.info("✓ Completed stress test")

    # Always run zero-weight test (essential for arbitration validation)
    tb.log.info("Running zero-weight arbitration test...")
    await tb.run_zero_weight_test()
    tb.log.info("✓ Completed zero-weight test")

    # Final statistics summary
    total_tests = len(test_results)
    passed_tests = sum(1 for result in test_results.values() if result['weight_compliance'])

    tb.log.info(f"Test Summary: {passed_tests}/{total_tests} tests passed weight compliance")

    final_stats = tb.get_statistics()
    tb.log.info(f"Final Statistics: {final_stats}")

    # Verify no errors occurred
    assert final_stats['verification_errors'] == 0, f"Verification errors detected: {final_stats['verification_errors']}"
    assert tb.total_errors == 0, f"Total errors: {tb.total_errors}"

    tb.log.info(f"✓ ALL {test_level.upper()} GAXI DATA COLLECT TESTS PASSED!")


def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.

    Examples for quick debugging:
        # Single test case:
        return [(8, 4, 8, 'basic')]

        # Just test one configuration:
        return [(8, 4, 8, 'basic'), (8, 4, 8, 'medium')]

        # Test only basic level:
        data_widths = [8]
        id_widths = [4, 8]
        fifo_depths = [8, 16]
        test_levels = ['basic']  # Only basic
        return list(product(data_widths, id_widths, fifo_depths, test_levels))
    """
    data_widths = [8]
    id_widths = [4, 8]
    fifo_depths = [8]
    test_levels = ['basic']  # All test levels

    # For quick testing, uncomment this line:
    return [(8, 4, 8, 'full'), (8, 8, 16, 'full')]
    # return list(product(data_widths, id_widths, fifo_depths, test_levels))


params = generate_params()


@pytest.mark.parametrize("data_width, id_width, fifo_depth, test_level", params)
def test_gaxi_data_collect_with_arbitration(request, data_width, id_width, fifo_depth, test_level):
    """
    Parameterized GAXI data collect test with configurable test levels and arbitration focus.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (2-3 min)
    - medium: Integration testing (5-8 min)
    - full: Comprehensive validation (15-25 min)

    For quick debugging: Modify generate_params() function to return only specific combinations
    """
    # get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba': 'rtl/amba',
        'rtl_amba_test': 'rtl/amba/testcode',
    })

    # set up all of the test names
    dut_name = "gaxi_data_collect"
    toplevel = dut_name

    # Get verilog sources
    verilog_sources = [
        # Arbiter components
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_fixed_priority.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted_subinst.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin_weighted.sv"),

        # FIFO components
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_fifo_sync.sv"),

        # GAXI components
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),

        # Main DUT
        os.path.join(rtl_dict['rtl_amba_test'], f"{dut_name}.sv"),
    ]

    # create a human readable test identifier with test level
    dw_str = TBBase.format_dec(data_width, 2)
    idw_str = TBBase.format_dec(id_width, 2)
    fifo_str = TBBase.format_dec(fifo_depth, 2)
    # Updated test name format: includes test level in the main name
    test_name_plus_params = f"test_gaxi_datacollect_dw{dw_str}_idw{idw_str}_fifo{fifo_str}_{test_level}"
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
    rtl_parameters['REGISTERED'] = '0'  # Use mux mode for GAXI data collect
    rtl_parameters['DATA_WIDTH'] = str(data_width)
    rtl_parameters['ID_WIDTH'] = str(id_width)
    rtl_parameters['OUTPUT_FIFO_DEPTH'] = str(fifo_depth)
    rtl_parameters['SKID_DEPTH'] = '2'  # Standard skid depth
    rtl_parameters['CHUNKS'] = '4'  # Standard chunks for data collect

    # Add string parameter with quotes for Verilator
    # rtl_parameters['INSTANCE_NAME'] = f'"gaxi_datacollect_{test_level}"'  # Include test level in instance name

    # Adjust timeout based on test level
    timeout_multipliers = {'basic': 1.5, 'medium': 3, 'full': 6}
    base_timeout = 4000  # 4 seconds base (GAXI data collect is complex)
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
        'OUTPUT_FIFO_DEPTH': str(fifo_depth),
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
    print(f"Running {test_level.upper()} test: GAXI Data Collect with Arbitration")
    print(f"Config: data_width={data_width}, id_width={id_width}, fifo_depth={fifo_depth}")
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
        print(f"✓ {test_level.upper()} test PASSED: GAXI Data Collect with Arbitration")
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
