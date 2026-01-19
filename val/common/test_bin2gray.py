# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Bin2GrayTB
# Purpose: Binary to Gray Code Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Binary to Gray Code Converter Test

This test verifies the binary to gray code conversion functionality:

CONFIGURATION:
    WIDTH: Bit width of the converter (4, 8, 16, 32)

TEST LEVELS:
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - WIDTH: [4, 8, 16, 32]
    - test_level: [basic, medium, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Bit width for converter

CONVERSION BEHAVIOR:
    Gray code conversion: gray[i] = binary[i] ^ binary[i+1] (except MSB)
    MSB: gray[WIDTH-1] = binary[WIDTH-1]
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from conftest import get_coverage_compile_args

class Bin2GrayTB(TBBase):
    """Testbench for Binary to Gray Code Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Bin2Gray TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Calculate test ranges
        self.max_value = (1 << self.WIDTH) - 1

    def _setup_signals(self):
        """Setup signal mappings"""
        self.binary = self.dut.binary
        self.gray = self.dut.gray

    def bin_to_gray_reference(self, binary_val):
        """Reference implementation of binary to gray conversion"""
        gray_val = 0
        # MSB of gray is same as MSB of binary
        gray_val |= (binary_val & (1 << (self.WIDTH - 1)))

        # Other bits: gray[i] = binary[i] ^ binary[i+1]
        for i in range(self.WIDTH - 1):
            bit_i = (binary_val >> i) & 1
            bit_i_plus_1 = (binary_val >> (i + 1)) & 1
            gray_bit = bit_i ^ bit_i_plus_1
            gray_val |= (gray_bit << i)

        return gray_val

    async def check_conversion(self, binary_val):
        """Check a single conversion"""
        self.binary.value = binary_val
        await Timer(1, units='ns')  # Allow combinational logic to settle

        actual_gray = int(self.gray.value)
        expected_gray = self.bin_to_gray_reference(binary_val)

        success = actual_gray == expected_gray

        if not success or self.DEBUG:
            self.log.info(f"Binary: 0x{binary_val:0{(self.WIDTH+3)//4}X} "
                            f"-> Gray: 0x{actual_gray:0{(self.WIDTH+3)//4}X} "
                            f"(Expected: 0x{expected_gray:0{(self.WIDTH+3)//4}X}) "
                            f"{'✓' if success else '✗'}")

        return success, actual_gray, expected_gray

    async def test_exhaustive(self):
        """Test all possible values (for small widths)"""
        if self.WIDTH > 16:
            self.log.info(f"Skipping exhaustive test for WIDTH={self.WIDTH} (too large)")
            return True

        self.log.info(f"Testing exhaustive conversion for WIDTH={self.WIDTH}")

        all_passed = True
        failed_count = 0

        for binary_val in range(self.max_value + 1):
            success, actual, expected = await self.check_conversion(binary_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'exhaustive',
                    'binary_input': binary_val,
                    'expected_gray': expected,
                    'actual_gray': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'basic' and failed_count >= 5:
                    break

        # Store summary result
        result = {
            'test_type': 'exhaustive',
            'total_tests': min(self.max_value + 1, binary_val + 1),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Exhaustive test: {result['total_tests']} tests, "
                        f"{failed_count} failures")

        return all_passed

    async def test_random_values(self):
        """Test random values for larger widths"""
        self.log.info(f"Testing random conversions for WIDTH={self.WIDTH}")

        # Determine number of tests based on level
        if self.TEST_LEVEL == 'basic':
            num_tests = min(100, self.max_value + 1)
        elif self.TEST_LEVEL == 'medium':
            num_tests = min(1000, self.max_value + 1)
        else:  # full
            num_tests = min(10000, self.max_value + 1)

        all_passed = True
        failed_count = 0

        # Always test corner cases
        corner_cases = [0, 1, self.max_value, self.max_value - 1]
        if self.WIDTH > 2:
            corner_cases.extend([
                1 << (self.WIDTH - 1),  # MSB only
                (1 << (self.WIDTH - 1)) - 1,  # All bits except MSB
            ])

        # Add power of 2 values
        for i in range(self.WIDTH):
            corner_cases.append(1 << i)

        # Remove duplicates and ensure within range
        corner_cases = list(set([val for val in corner_cases if val <= self.max_value]))

        test_values = corner_cases.copy()

        # Add random values
        while len(test_values) < num_tests:
            val = random.randint(0, self.max_value)
            if val not in test_values:
                test_values.append(val)

        test_values = test_values[:num_tests]

        for i, binary_val in enumerate(test_values):
            success, actual, expected = await self.check_conversion(binary_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'random',
                    'test_index': i,
                    'binary_input': binary_val,
                    'expected_gray': expected,
                    'actual_gray': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'basic' and failed_count >= 10:
                    break

        # Store summary result
        result = {
            'test_type': 'random',
            'total_tests': min(len(test_values), i + 1),
            'failures': failed_count,
            'corner_cases_tested': len([v for v in corner_cases if v in test_values]),
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Random test: {result['total_tests']} tests, "
                        f"{failed_count} failures, "
                        f"{result['corner_cases_tested']} corner cases")

        return all_passed

    async def test_sequential_patterns(self):
        """Test sequential counting patterns"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping sequential pattern test")
            return True

        self.log.info(f"Testing sequential patterns")

        all_passed = True
        failed_count = 0

        # Test Gray code property: adjacent values differ by only one bit
        num_tests = min(1000 if self.TEST_LEVEL == 'medium' else 5000, self.max_value)

        prev_gray = None
        for i in range(num_tests):
            binary_val = i % (self.max_value + 1)
            success, actual_gray, expected_gray = await self.check_conversion(binary_val)

            if not success:
                failed_count += 1
                all_passed = False
                continue

            # Check Gray code property
            if prev_gray is not None:
                diff = actual_gray ^ prev_gray
                # Count number of bits that differ
                bit_diff_count = bin(diff).count('1')

                if bit_diff_count != 1:
                    self.log.error(f"Gray code property violation: "
                                    f"Binary {binary_val-1} -> {binary_val}, "
                                    f"Gray 0x{prev_gray:X} -> 0x{actual_gray:X}, "
                                    f"{bit_diff_count} bits differ")
                    failed_count += 1
                    all_passed = False

                    # Store failure
                    result = {
                        'test_type': 'sequential_gray_property',
                        'binary_prev': binary_val - 1,
                        'binary_curr': binary_val,
                        'gray_prev': prev_gray,
                        'gray_curr': actual_gray,
                        'bit_diff_count': bit_diff_count,
                        'success': False
                    }
                    self.test_failures.append(result)

            prev_gray = actual_gray

        # Store summary result
        result = {
            'test_type': 'sequential_patterns',
            'total_tests': num_tests,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Sequential pattern test: {num_tests} tests, {failed_count} failures")

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running BIN2GRAY tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = []

        # Choose appropriate test strategy based on width
        if self.WIDTH <= 16:
            test_functions.append((self.test_exhaustive, "Exhaustive conversion"))
        else:
            test_functions.append((self.test_random_values, "Random value conversion"))

        if self.TEST_LEVEL in ['medium', 'full']:
            test_functions.append((self.test_sequential_patterns, "Sequential patterns"))

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall BIN2GRAY result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed

@cocotb.test(timeout_time=60000, timeout_unit="us")
async def bin2gray_test(dut):
    """Test for Binary to Gray Code Converter module"""
    tb = Bin2GrayTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"BIN2GRAY test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Bin2Gray test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters"""
    widths = [4, 8, 16, 32]
    test_levels = ['full']

    valid_params = []
    for width, test_level in product(widths, test_levels):
        valid_params.append((width, test_level))

    # For debugging, uncomment one of these:
    # return [(4, 'full')]  # Single test
    # return [(8, 'medium'), (16, 'medium')]  # Specific configurations

    return valid_params

params = generate_params()

@pytest.mark.parametrize("width, test_level", params)
def test_bin2gray(request, width, test_level):
    """
    Parameterized Binary to Gray Code Converter test
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "bin2gray"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/bin2gray.f'
    )
    toplevel = dut_name

    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    # Create human-readable test identifier
    width_str = TBBase.format_dec(width, 2)
    test_name_plus_params = f"test_bin2gray_w{width_str}_{test_level}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width)
    }

    # Adjust timeout based on test level and width
    timeout_multipliers = {'basic': 1, 'medium': 3, 'full': 6}
    width_factor = max(1.0, (1 << width) / 1000.0) if width <= 16 else max(1.0, width / 8.0)
    base_timeout = 5000  # 5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_WIDTH': str(width),
        'TEST_DEBUG': '0',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: width={width}")
    print(f"Max values to test: {min(2**width, 10000)}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

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
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ {test_level.upper()} test PASSED: width={width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
