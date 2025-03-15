#!/usr/bin/env python
"""
Pytest wrapper for GAXI component tests.

This can be integrated with your existing pytest framework to run GAXI component tests
with various combinations of signal modes and handshaking modes.
"""


import itertools
import os
import sys
import random
import pytest
from pathlib import Path
from cocotb_test.simulator import run
from TBClasses.utilities import get_paths, create_view_cmd

# Import the TEST_MODE_MAP from the GAXITestbench
from TBClasses.gaxi_components_tb import TEST_MODE_MAP

# All possible test modes (combinations of signal and handshake modes)
ALL_TEST_MODES = [
    'standard',          # Standard signals with skid buffer
    'multi_signal',      # Multi-signal with skid buffer
    'fifo_mux',          # Standard signals with FIFO mux
    'fifo_flop',         # Standard signals with FIFO flop
    'skid_multi',        # Multi-signal with skid buffer (alternate naming)
    'fifo_mux_multi',    # Multi-signal with FIFO mux
    'fifo_flop_multi'    # Multi-signal with FIFO flop
]

# Generate all combinations for testing
def generate_test_combinations():
    """Generate all test combinations for parametrization"""
    # Base combinations
    base_combinations = []

    # Data widths to test
    data_widths = [32]  # Can add more like [8, 16, 32, 64]

    # Control widths to test
    ctrl_widths = [8]   # Can add more like [4, 8, 16]

    # Number of packets to test
    packet_counts = [10, 20]

    # Generate combinations
    for data_width, ctrl_width in itertools.product(data_widths, ctrl_widths):
        for test_mode in ALL_TEST_MODES:
            base_combinations.extend(
                (data_width, ctrl_width, test_mode, packet_count)
                for packet_count in packet_counts
            )
    return base_combinations

# Test cases for GAXI components
@pytest.mark.parametrize("data_width, ctrl_width, test_mode, num_packets", generate_test_combinations())
def test_gaxi_components(request, data_width, ctrl_width, test_mode, num_packets):
    """Run the testbench for GAXI components with various modes"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_axi': 'rtl/axi'
    })

    # Set up all of the test names
    dut_name = "gaxi_test_dut"
    toplevel = dut_name

    # This is a basic test harness for GAXI components - you would
    # replace this with your actual test harness or create a dedicated harness
    verilog_sources = [
        os.path.join(rtl_dict['rtl_axi'], f"{dut_name}.sv")
    ]

    # Create a human readable test identifier
    dw_str = f"{data_width:03d}"
    cw_str = f"{ctrl_width:03d}"

    # Get signal and handshake modes for clearer test naming
    signal_mode = "std"
    handshake_mode = "skid"

    if test_mode in TEST_MODE_MAP:
        config = TEST_MODE_MAP[test_mode]
        signal_mode = "multi" if config['signal_mode'] == 'multi_signal' else "std"
        handshake_mode = config['handshake_mode']

    test_name_plus_params = f"test_gaxi_comp_dw{dw_str}_cw{cw_str}_{signal_mode}_{handshake_mode}_p{num_packets}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    includes = []

    # RTL parameters - these would match your DUT parameters
    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'CTRL_WIDTH': str(ctrl_width)
    }

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add test parameters for the Python test module
    extra_env['TEST_WIDTH'] = str(data_width)
    extra_env['TEST_CTRL_WIDTH'] = str(ctrl_width)
    extra_env['TEST_MODE'] = test_mode
    extra_env['TEST_NUM_PACKETS'] = str(num_packets)
    extra_env['TEST_USE_MEMORY'] = 'True'  # Enable memory model
    extra_env['TEST_RANDOMIZE_DELAYS'] = 'True'  # Enable randomized delays

    # Create the command file for viewing waveforms
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,  # Python test module
            parameters=rtl_parameters,
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
