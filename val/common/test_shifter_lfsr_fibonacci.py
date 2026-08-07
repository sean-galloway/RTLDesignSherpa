# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ShifterLFSRFibonacciConfig
# Purpose: Configuration class for Fibonacci LFSR Shifter tests
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
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.shifter_lfsr_fibonacci_tb import ShifterLFSRFibonacciTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args
from TBClasses.common.lfsr_mirror import simulate_xor_lfsr as _shared_lfsr_mirror

class ShifterLFSRFibonacciConfig:
    """Configuration class for Fibonacci LFSR Shifter tests"""
    def __init__(self, name, width=8, tap_index_width=12, tap_count=4, tap_values=None):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            width: LFSR width
            tap_index_width: Width of tap indices
            tap_count: Number of taps
            tap_values: List of tap values (if None, default taps will be used)
        """
        self.name = name
        self.width = width
        self.tap_index_width = tap_index_width
        self.tap_count = tap_count

        # Default taps if not provided
        if tap_values is None:
            if width == 8:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [8]
                elif tap_count == 2:
                    self.tap_values = [8, 6]
                elif tap_count == 3:
                    self.tap_values = [8, 6, 5]
                else:
                    self.tap_values = [8, 6, 5, 4]  # Standard taps for 8-bit LFSR
            elif width == 16:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [16]
                elif tap_count == 2:
                    self.tap_values = [16, 15]
                elif tap_count == 3:
                    self.tap_values = [16, 15, 13]
                else:
                    self.tap_values = [16, 15, 13, 4]  # Standard taps for 16-bit LFSR
            elif width == 32:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [32]
                elif tap_count == 2:
                    self.tap_values = [32, 22]
                elif tap_count == 3:
                    self.tap_values = [32, 22, 2]
                else:
                    self.tap_values = [32, 22, 2, 1]  # Standard taps for 32-bit LFSR
            elif width == 64:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [64]
                elif tap_count == 2:
                    self.tap_values = [64, 63]
                elif tap_count == 3:
                    self.tap_values = [64, 63, 61]
                else:
                    self.tap_values = [64, 63, 61, 60]  # Standard taps for 64-bit LFSR
            elif width == 96:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [96]
                elif tap_count == 2:
                    self.tap_values = [96, 94]
                elif tap_count == 3:
                    self.tap_values = [96, 94, 49]
                else:
                    self.tap_values = [96, 94, 49, 47]  # Standard taps for 96-bit LFSR
            elif width == 128:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [128]
                elif tap_count == 2:
                    self.tap_values = [128, 126]
                elif tap_count == 3:
                    self.tap_values = [128, 126, 101]
                else:
                    self.tap_values = [128, 126, 101, 99]  # Standard taps for 128-bit LFSR
            else:
                # For other widths, use some reasonable defaults based on tap_count
                self.tap_values = []
                if tap_count >= 1:
                    self.tap_values.append(width)
                if tap_count >= 2:
                    self.tap_values.append(width//2)
                if tap_count >= 3:
                    self.tap_values.append(2)
                if tap_count >= 4:
                    self.tap_values.append(1)
                # Pad with zeros if needed
                while len(self.tap_values) < tap_count:
                    self.tap_values.append(0)
        else:
            # Use provided tap values, but ensure we have exactly tap_count values
            self.tap_values = tap_values[:tap_count]
            # Pad with zeros if needed
            while len(self.tap_values) < tap_count:
                self.tap_values.append(0)


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = ShifterLFSRFibonacciTB(dut)

    # Start clock with configured period
    await tb.start_clock('clk', 10, 'ns')

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"

def generate_test_params():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (8-bit, gate+func)
    REG_LEVEL=FUNC: 6 tests (8-bit all levels, plus 16, 32, 64-bit) - default
    REG_LEVEL=FULL: 11 tests (all widths including 4, 96, 128-bit + tap configs)

    Returns:
        List of dicts with WIDTH, TAP_INDEX_WIDTH, TAP_COUNT, test_level
    """
    import os
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'gate'},
            {'WIDTH': 8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'gate'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'full'},
            {'WIDTH': 16, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH': 32, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH': 64, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
        ]
    else:  # FULL
        return [
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'gate'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'full'},
            {'WIDTH':  4, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH': 16, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH': 32, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH': 64, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH': 96, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            {'WIDTH': 128, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'func'},
            # Different tap configurations
            {'WIDTH':  8, 'TAP_INDEX_WIDTH':  8, 'TAP_COUNT': 2, 'test_level': 'func'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 16, 'TAP_COUNT': 6, 'test_level': 'func'},
        ]

@pytest.mark.parametrize("params", generate_test_params())
def test_shifter_lfsr_fibonacci(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "shifter_lfsr_fibonacci"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/shifter_lfsr_fibonacci.f'
    )

    # Create a human-readable test identifier
    t_width = params['WIDTH']
    t_tiw = params['TAP_INDEX_WIDTH']
    t_tc = params['TAP_COUNT']
    t_name = params['test_level']
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_W{t_width}_TIW{t_tiw}_TC{t_tc}_{t_name}_{reg_level}"

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
    parameters = {
        'WIDTH': params['WIDTH'],
        'TAP_INDEX_WIDTH': params['TAP_INDEX_WIDTH'],
        'TAP_COUNT': params['TAP_COUNT']
    }

    # Prepare environment variables
    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': params['test_level'],
        'TEST_WIDTH': str(params['WIDTH']),
        'TEST_TAP_INDEX_WIDTH': str(params['TAP_INDEX_WIDTH']),
        'TEST_TAP_COUNT': str(params['TAP_COUNT'])
    }

    # Calculate timeout based on test complexity
    complexity_factor = 1.0
    # sourcery skip: no-conditionals-in-tests
    if params['test_level'] == 'func':
        complexity_factor = 2.0
    elif params['test_level'] == 'full':
        complexity_factor = 5.0
    timeout_factor = complexity_factor * 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this
    # the run produces no coverage.dat at all and `make coverage-report`
    # silently reports 0.0% from 0 merged files.
    extra_args.extend(get_coverage_compile_args())

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
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
