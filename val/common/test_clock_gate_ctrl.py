# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ClockGateCtrlConfig
# Purpose: Configuration class for clock gate controller tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.clock_gate_ctrl_tb import ClockGateCtrlTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

class ClockGateCtrlConfig:
    """Configuration class for clock gate controller tests"""
    def __init__(self, name, counter_width):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            counter_width: Counter width in bits
        """
        self.name = name
        self.counter_width = counter_width


@cocotb.test(timeout_time=2, timeout_unit="ms")  # Increased timeout for randomized tests
async def clock_gate_ctrl_test(dut):
    """Test the clock gate control block with FlexRandomizer"""
    tb = ClockGateCtrlTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'Using seed: {seed}'
    tb.log.info(msg)

    # Start the clock
    await tb.start_clock('clk_in', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run all test sequences
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting clock gate controller tests with FlexRandomizer @ {time_ns}ns ===")
        await tb.run_test()

        time_ns = get_sim_time('ns')
        tb.log.info(f"All tests completed successfully @ {time_ns}ns")

    except AssertionError as e:
        tb.log.error(f"Test failed: {str(e)}")
        raise
    finally:
        # Wait for any pending tasks
        await tb.wait_clocks('clk_in', 10)

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (4-bit)
    REG_LEVEL=FUNC: 2 tests (4, 8-bit) - default
    REG_LEVEL=FULL: 3 tests (4, 6, 8-bit counters)

    Returns:
        List of counter widths
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [4]
    if reg_level == 'FULL':
        # FULL used to return the same [4, 8] as FUNC -- the docstring said so
        # outright -- which made the most expensive level a relabelling of the
        # middle one. It sweeps the counter width properly now; TEST_LEVEL adds
        # the per-test depth on top. 12-bit was tried and dropped: max_count
        # is 2**N-1, so a 12-bit counter costs 4095 cycles per timeout
        # scenario and pushed FULL past ten minutes on its own.
        return [4, 6, 8]
    return [4, 8]

@pytest.mark.parametrize("counter_width", generate_test_params())
def test_clock_gate_ctrl(request, counter_width):
    """Run the test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "clock_gate_ctrl"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/clock_gate_ctrl.f'
    )

    # Create a human readable test identifier
    n_str = TBBase.format_dec(counter_width, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_n{n_str}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # RTL parameters
    parameters = {'IDLE_CNTR_WIDTH': counter_width}

    # Environment variables
    extra_env = {
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', reg_level.lower()),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
    }

    # Add coverage compile args if COVERAGE=1
    # Add parameter values to environment variables
    # sourcery skip: no-loop-in-tests
    for k, v in parameters.items():
        extra_env[f'PARAM_{k}'] = str(v)

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_args=extra_args,
            plus_args=sim_args,
            extra_env=extra_env,
            waves=enable_waves,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure