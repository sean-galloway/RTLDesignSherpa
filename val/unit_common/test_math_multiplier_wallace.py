"""
Test for the Wallace tree multiplier module.
"""
import os
import random
import subprocess
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.utilities import get_paths, create_view_cmd

# Import the base MultiplierTB class
from CocoTBFramework.tbclasses.common.multiplier_testing import MultiplierTB


@cocotb.test(timeout_time=1, timeout_unit="ms")
async def multiplier_test(dut):
    """Test the Wallace tree multiplier"""
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


@pytest.mark.parametrize("n", [8, 16, 32])
def test_math_multiplier_wallace_tree(request, n):
    """PyTest function to run the cocotb test."""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # The module name is specific to the bit width for Wallace tree
    dut_name = f"math_multiplier_wallace_tree_{n:03d}"
    toplevel = dut_name

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_half.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "math_adder_full.sv"),
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv"),
    ]

    # Define test parameters
    parameters = {'N': n}

    # Create human-readable test identifier
    test_name_plus_params = f"test_{dut_name}"

    # Define simulation build and log paths
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)

    # Define log path
    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Set up environment variables
    seed = random.randint(0, 100000)
    test_level = os.environ.get('TEST_LEVEL', 'basic')  # Can be basic, medium, or full

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': test_level,
        'PARAM_N': str(n)
    }

    # Create command file for viewing waveforms
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Launch the simulation
    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=True,
            keep_files=True
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
