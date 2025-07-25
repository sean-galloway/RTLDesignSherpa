"""
Arbiter WRR Test with Parameterized Test Levels and PWM Integration

This test combines PWM and Weighted Round Robin Arbiter testing with parameterized test levels:

TEST LEVELS:
    basic (2-3 min):   Quick verification during development - core PWM/arbiter interaction
    medium (5-8 min):  Integration testing for CI/branches - includes repeat and edge cases
    full (10-15 min):  Comprehensive validation for regression - includes stress testing

PARAMETER COMBINATIONS:
    - max_thresh: [8, 16]
    - clients: [4, 6, 8]
    - pwm_width: [8, 12]
    - wait_gnt_ack: [0, 1]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    MAX_THRESH: Maximum threshold for arbiter
    CLIENTS: Number of arbiter clients
    PWM_WIDTH: PWM counter width
    WAIT_GNT_ACK: Whether arbiter waits for grant acknowledgment
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the refactored testbench
from CocoTBFramework.tbclasses.amba.arbiter_wrr_pwm_monbus.arbiter_wrr_pwm_monbus_tb import ArbiterWRRPWMMonBusTestTB


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def arbiter_wrr_pwm_monbus_test(dut):
    """Test for combined Arbiter WRR, PWM, and MonBus module with refactored architecture"""
    tb = ArbiterWRRPWMMonBusTestTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'Arbiter WRR PWM MonBus Test starting with seed {seed}')

    # Start the clock
    await tb.start_clock('clk', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run comprehensive tests using refactored architecture
        passed = await tb.run_all_tests()

        # Report final result
        tb.log.info(f"Arbiter WRR PWM MonBus Test {'PASSED' if passed else 'FAILED'} "
                    f"at level {tb.test_params['test_level'].value.upper()}")

        # Detailed reporting from each test class
        if tb.test_failures:
            tb.log.error(f"Failed tests ({len(tb.test_failures)}): {', '.join(tb.test_failures)}")
        
        # Component statistics from proven components
        if tb.components.arbiter_monitor:
            arbiter_stats = tb.components.arbiter_monitor.get_stats_summary()
            tb.log.info(f"Final Arbiter Statistics:\n{arbiter_stats}")

        if tb.components.monbus_slave:
            monbus_summary = tb.components.monbus_slave.get_stats_summary()
            tb.log.info(f"Final MonBus Statistics:\n{monbus_summary}")

        # Test class summaries
        for class_name, results in tb.test_results.items():
            if isinstance(results, dict) and 'total_tests' in results:
                tb.log.info(f"{class_name}: {results['passed_tests']}/{results['total_tests']} tests passed")

        # Assert on failure
        assert passed, f"Arbiter WRR PWM MonBus Test FAILED - {len(tb.test_failures)} test failures detected"

        tb.log.info("✓ ALL ARBITER WRR PWM MONBUS TESTS COMPLETED SUCCESSFULLY!")

        return passed

    except AssertionError as e:
        tb.log.error(f"Test failed: {str(e)}")
        raise
    except Exception as e:
        tb.log.error(f"Unexpected error: {str(e)}")
        raise
    finally:
        # Wait for any pending tasks
        await tb.wait_clocks('clk', 10)


def generate_params():
    """
    Generate test parameters. Modify this function to limit test scope for debugging.

    Examples for quick debugging:
        # Single test case:
        return [(8, 4, 8, 0, 'basic')]

        # Test only basic level:
        max_threshes = [8, 16]
        clients_list = [4, 6]
        pwm_widths = [8]
        wait_gnt_acks = [0]
        test_levels = ['basic']  # Only basic
        return list(product(max_threshes, clients_list, pwm_widths, wait_gnt_acks, test_levels))
    """
    max_threshes  = [15]
    clients_list  = [4, 6, 8]
    pwm_widths    = [8, 12]
    wait_gnt_acks = [0, 1]
    fairness_threshes = [ 30, 40, 50]
    min_grants = [100, 200, 300]
    test_levels   = ['full']

    # For quick testing, uncomment one of these lines:
    return [(15, 4, 8, 0, 30, 100, 'medium')]  # Single basic test
    # return [(8, 4, 8, 0, 30, 100, 'basic'), (16, 6, 12, 1, 40, 200, 'medium')]  # Limited test set

    return list(product(max_threshes, clients_list, pwm_widths, wait_gnt_acks, fairness_threshes, min_grants, test_levels))


params = generate_params()


@pytest.mark.parametrize("max_thresh, clients, pwm_width, wait_gnt_ack, fairness_thresh, min_grants, test_level", params)
def test_arbiter_wrr_pwm_monbus(request, max_thresh, clients, pwm_width, wait_gnt_ack, fairness_thresh, min_grants, test_level):
    """
    Parameterized test for combined Arbiter WRR and PWM functionality.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (2-3 min) - core functionality
    - medium: Integration testing (5-8 min) - includes edge cases and repeat functionality
    - full: Comprehensive validation (10-15 min) - includes stress testing

    For quick debugging: Modify generate_params() function to return only specific combinations
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':           'rtl/common',
        'rtl_gaxi':          'rtl/amba/gaxi',
        'rtl_amba_shared':   'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes',    })

    # DUT information
    dut_name = "arbiter_wrr_pwm_monbus"
    verilog_sources = [
        # Monitor package (must be first)
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_pkg.sv"),

        # Arbiter components
        os.path.join(rtl_dict['rtl_cmn'],  "arbiter_round_robin_weighted_fixed_priority.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "arbiter_round_robin_weighted_subinst.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "arbiter_round_robin_weighted.sv"),

        # fifo components
        os.path.join(rtl_dict['rtl_cmn'],  "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'],  "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),

        # PWM component
        os.path.join(rtl_dict['rtl_cmn'],  "pwm.sv"),

        # Main DUT (combined module)
        os.path.join(rtl_dict['rtl_amba_shared'], f"{dut_name}.sv"),
    ]
    toplevel = dut_name

    # Create human-readable test identifier
    mt_str = TBBase.format_dec(max_thresh, 2)
    c_str = TBBase.format_dec(clients, 1)
    pw_str = TBBase.format_dec(pwm_width, 2)
    w_str = TBBase.format_dec(wait_gnt_ack, 1)
    ft_str = TBBase.format_dec(fairness_thresh, 2)
    mg_str = TBBase.format_dec(min_grants, 3)
    
    test_name_plus_params = (f"test_arbiter_wrr_pwm_monbus_mt{mt_str}_c{c_str}_pw{pw_str}_"
                            f"w{w_str}_ft{ft_str}_mg{mg_str}_{test_level}")
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'MAX_THRESH': str(max_thresh),
        'CLIENTS': str(clients),
        'WAIT_GNT_ACK': str(wait_gnt_ack),
        'PWM_WIDTH': str(pwm_width),
        # Derived parameters
        'MAX_THRESH_WIDTH': str((max_thresh - 1).bit_length()),
    }

    # Adjust timeout based on test level and parameters
    timeout_multipliers = {'basic': 2, 'medium': 4, 'full': 8}
    complexity_factor = (clients / 4.0) * (max_thresh / 8.0) * (pwm_width / 8.0)
    base_timeout = 5000  # 5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * complexity_factor)

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
        'MAX_THRESH': str(max_thresh),
        'CLIENTS': str(clients),
        'WAIT_GNT_ACK': str(wait_gnt_ack),
        'PWM_WIDTH': str(pwm_width),
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),
    }

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

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*70}")
    print(f"Running {test_level.upper()} test: Arbiter WRR + PWM Combined")
    print(f"Config: max_thresh={max_thresh}, clients={clients}, pwm_width={pwm_width}, wait_ack={wait_gnt_ack}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*70}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} test PASSED: Arbiter WRR + PWM Combined")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
