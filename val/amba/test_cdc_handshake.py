import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd

from CocoTBFramework.tbclasses.gaxi.cdc_handshake import CDCHandshakeTB


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cdc_handshake_test(dut):
    """Main cocotb test for CDC handshake."""
    tb = CDCHandshakeTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start the clocks with different periods (to test true CDC behavior)
    await tb.start_clock('clk_src', tb.clk_src_PERIOD_NS, 'ns')
    await tb.start_clock('clk_dst', tb.clk_dst_PERIOD_NS, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Test 1: Basic alternating reads/writes
        tb.log.info("=== Test 1: Basic alternating reads/writes ===")
        basic_result = await tb.run_basic_test(num_transactions=10)

        if tb.TEST_LEVEL != 'basic':
            # Test 2: Burst transactions
            tb.log.info("=== Test 2: Burst transactions ===")
            burst_result = await tb.run_burst_test(num_transactions=20)
        else:
            burst_result = True

        if tb.TEST_LEVEL == 'full':
            # Test 3: Random transactions
            tb.log.info("=== Test 3: Random transactions ===")
            random_result = await tb.run_random_test(num_transactions=30)
        else:
            random_result = True

        # Allow some additional time for any pending transactions
        await tb.wait_clocks('clk_src', 50)

        # Verify final results
        if basic_result and burst_result and random_result:
            tb.log.info("All tests passed successfully!")
        else:
            tb.log.error("Some tests failed:")
            tb.log.error(f"  Basic test: {'PASS' if basic_result else 'FAIL'}")
            if tb.TEST_LEVEL != 'basic':
                tb.log.error(f"  Burst test: {'PASS' if burst_result else 'FAIL'}")
            if tb.TEST_LEVEL == 'full':
                tb.log.error(f"  Random test: {'PASS' if random_result else 'FAIL'}")
            assert False, "Test failures detected"

    finally:
        # Set done flag to terminate handlers
        tb.done = True

        # Wait for tasks to complete
        await tb.wait_clocks('clk_src', 10)


@pytest.mark.parametrize("params", [

    # clk_src slower than clk_dst
    {'clk_src_period_ns':  15, 'clk_dst_period_ns': 10, 'test_level': 'basic'}, # 'basic', 'medium', 'full'
    {'clk_src_period_ns':  20, 'clk_dst_period_ns': 10, 'test_level': 'basic'},
    {'clk_src_period_ns':  50, 'clk_dst_period_ns': 10, 'test_level': 'basic'},
    {'clk_src_period_ns': 100, 'clk_dst_period_ns': 10, 'test_level': 'basic'},
    {'clk_src_period_ns': 200, 'clk_dst_period_ns': 10, 'test_level': 'basic'},

    # clk_src faster than clk_dst
    {'clk_src_period_ns': 10, 'clk_dst_period_ns':  15, 'test_level': 'basic'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns':  20, 'test_level': 'basic'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns':  50, 'test_level': 'basic'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns': 100, 'test_level': 'basic'},
    {'clk_src_period_ns': 10, 'clk_dst_period_ns': 200, 'test_level': 'basic'},

])
def test_cdc_handshake(request, params):
    """
    Pytest function to run the CDC handshake test using cocotb.
    """
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba': 'rtl/amba'})

    dut_name = "cdc_handshake"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], f"{dut_name}.sv")
    ]

    # Create a human readable test identifier
    t_clk_src = params['clk_src_period_ns']
    t_clk_dst = params['clk_dst_period_ns']
    t_name = f'cdc_handshake_{params['test_level']}'

    aw = 32
    aw_str = str(aw)
    dw = 32
    dw_str = str(dw)
    total_width = aw + dw + dw//8 + 1 + 3
    test_name_plus_params = f"test_{dut_name}_clk_src{t_clk_src}_clk_dst{t_clk_dst}_{t_name}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters
    rtl_parameters= {'DATA_WIDTH': str(total_width)}

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x434749),
        'TEST_ADDR_WIDTH': aw_str,
        'TEST_DATA_WIDTH': dw_str,
        'TEST_LEVLE': str(params['test_level']),
        'clk_src_PERIOD_NS': str(params['clk_src_period_ns']),
        'clk_dst_PERIOD_NS': str(params['clk_dst_period_ns'])
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
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure