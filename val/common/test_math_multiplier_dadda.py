"""
Test for the Dadda tree multiplier module.
"""
import os
import random
import subprocess
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the base MultiplierTB class
from CocoTBFramework.tbclasses.common.multiplier_testing import MultiplierTB


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def multiplier_test(dut):
    """Test the Dadda tree multiplier"""
    tb = MultiplierTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Print testbench settings
    tb.print_settings()

    # Clear and initialize interface
    tb.clear_interface()
    await tb.wait_time(1, 'ns')

    # Run the comprehensive test suite
    await tb.run_comprehensive_tests()


@pytest.mark.parametrize("params", [
    # Basic tests with different widths
    {'WIDTH': 8, 'test_level': 'simple'},   # Start with simple tests
    {'WIDTH': 8, 'test_level': 'basic'},    # Basic test level

    # Different bit widths with basic testing
    {'WIDTH': 16, 'test_level': 'basic'},   # Medium width
    {'WIDTH': 32, 'test_level': 'basic'},   # Full 32-bit width

    # More comprehensive testing
    {'WIDTH': 8, 'test_level': 'medium'},   # More thorough tests
    {'WIDTH': 16, 'test_level': 'medium'},  # Medium tests with larger width

    # Full test suite (only run selectively due to time)
    {'WIDTH': 16, 'test_level': 'full'},     # Complete test suite
])
def test_math_multiplier_dadda_tree(request, params):
    """PyTest function to run the cocotb test."""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    # The module name is specific to the bit width for Dadda tree
    n = params['WIDTH']
    t_name = params['test_level']
    dut_name = f"math_multiplier_dadda_tree_{n:03d}"
    toplevel = dut_name

    # Create a human-readable test identifier
    test_name_plus_params = f"test_{dut_name}_{t_name}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_carry_save.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # Define simulation build and log paths
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Define log path
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Set up environment variables
    seed = random.randint(0, 100000)

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
        'PARAM_N': str(params['WIDTH'])
    }

    # Create command file for viewing waveforms

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

    # Launch the simulation
    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters={'N': params['WIDTH']},
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