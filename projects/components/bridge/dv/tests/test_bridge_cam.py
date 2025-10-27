# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_bridge_cam
# Purpose: Test suite for bridge_cam module
#
# Documentation: projects/components/bridge/CLAUDE.md
# Subsystem: bridge/dv/tests
#
# Author: sean galloway
# Created: 2025-10-26

import os
import sys
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

# Add project root to path for importing TB class from PROJECT AREA
sys.path.insert(0, repo_root)

from projects.components.bridge.dv.tbclasses.bridge_cam_tb import BridgeCamTB
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


# ===========================================================================
# COCOTB TEST FUNCTIONS - Prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_bridge_cam(dut):
    """Test the bridge_cam functionality - comprehensive test for both modes"""
    tb = BridgeCamTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'seed changed to {seed}'
    tb.log.info(msg)

    # Print settings
    tb.print_settings()

    # Start the clock
    await tb.start_clock('clk', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run basic test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting basic CAM test @ {time_ns}ns ===")
        await tb.run_basic_test()
        await tb.cleanup_cam()  # Clean up after test

        # Run capacity test
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting capacity test @ {time_ns}ns ===")
        await tb.run_capacity_test()
        await tb.cleanup_cam()  # Clean up after test

        # Run Mode 2 test (only if ALLOW_DUPLICATES=1)
        if tb.ALLOW_DUPLICATES == 1:
            time_ns = get_sim_time('ns')
            tb.log.info(f"=== Starting Mode 2 duplicate handling test @ {time_ns}ns ===")
            await tb.run_mode2_test()
            await tb.cleanup_cam()  # Clean up after test

        time_ns = get_sim_time('ns')
        tb.log.info(f"All tests completed successfully @ {time_ns}ns")

    except AssertionError as e:
        tb.log.error(f"Test failed: {str(e)}")
        raise
    finally:
        # Set done flag and wait for any pending tasks
        tb.done = True
        await tb.wait_clocks('clk', 10)


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def get_bridge_cam_params():
    """Generate bridge_cam test parameters based on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Test both Mode 1 (ALLOW_DUPLICATES=0) and Mode 2 (ALLOW_DUPLICATES=1)
    # Parameters: (tag_width, data_width, depth, allow_duplicates)

    if reg_level == 'GATE':
        # GATE: Minimal - small configurations for both modes
        return [
            (4, 4, 8, 0),   # Mode 1: Simple blocking
            (4, 4, 8, 1),   # Mode 2: FIFO ordering
        ]
    elif reg_level == 'FUNC':
        # FUNC: Medium configurations
        return [
            (8, 8, 16, 0),  # Mode 1: Medium size
            (8, 8, 16, 1),  # Mode 2: Medium size
            (4, 4, 8, 0),   # Mode 1: Small
            (4, 4, 8, 1),   # Mode 2: Small
        ]
    else:  # FULL
        # FULL: Comprehensive configurations
        return [
            (8, 8, 16, 0),  # Mode 1: Standard
            (8, 8, 16, 1),  # Mode 2: Standard
            (4, 4, 8, 0),   # Mode 1: Small
            (4, 4, 8, 1),   # Mode 2: Small
            (8, 8, 32, 0),  # Mode 1: Large depth
            (8, 8, 32, 1),  # Mode 2: Large depth
            (12, 12, 16, 0), # Mode 1: Wide tags/data
            (12, 12, 16, 1), # Mode 2: Wide tags/data
        ]


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("tag_width, data_width, depth, allow_duplicates", get_bridge_cam_params())
def test_bridge_cam(request, tag_width, data_width, depth, allow_duplicates):
    """Run the bridge_cam test with pytest"""

    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': 'projects/components/bridge/rtl',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "bridge_cam"
    toplevel = dut_name

    # Verilog sources - bridge_cam.sv plus any dependencies
    verilog_sources = [
        os.path.join(repo_root, 'projects/components/bridge/rtl/bridge_cam.sv'),
    ]

    # Include directories
    includes = [
        os.path.join(repo_root, 'rtl/amba/includes'),
    ]

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Create a human readable test identifier
    tag_str = TBBase.format_dec(tag_width, 2)
    data_str = TBBase.format_dec(data_width, 2)
    depth_str = TBBase.format_dec(depth, 3)
    mode_str = f"mode{allow_duplicates + 1}"  # Mode 1 or Mode 2
    test_name_plus_params = f"test_{dut_name}_tw{tag_str}_dw{data_str}_d{depth_str}_{mode_str}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'TAG_WIDTH': tag_width,
        'DATA_WIDTH': data_width,
        'DEPTH': depth,
        'ALLOW_DUPLICATES': allow_duplicates,
        'PIPELINE_EVICT': 0  # Start with combinational eviction
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000))
    }

    # Add parameter values to environment variables
    for k, v in parameters.items():
        extra_env[f'PARAM_{k}'] = str(v)

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # Tell Verilator to use vcd
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            testcase="cocotb_test_bridge_cam",  # Name of cocotb test function
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
            simulator="verilator",  # Use Verilator simulator
            timescale="1ns/1ps",  # Verilator timescale
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
