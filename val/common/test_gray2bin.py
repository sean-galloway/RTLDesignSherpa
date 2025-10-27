# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Gray2BinTB
# Purpose: Gray Code to Binary Converter Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Gray Code to Binary Converter Test

This test verifies the gray code to binary conversion functionality:

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
    Binary conversion: binary[i] = XOR of gray[i:WIDTH-1]
    This is the inverse of the bin2gray operation
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
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class Gray2BinTB(TBBase):
    """Testbench for Gray Code to Binary Converter module"""

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
        self.log.info(f"Gray2Bin TB initialized{self.get_time_ns_str()}")
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
        self.gray = self.dut.gray
        self.binary = self.dut.binary

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

    def gray_to_bin_reference(self, gray_val):
        """Reference implementation of gray to binary conversion"""
        binary_val = 0

        # Each binary bit is XOR of all gray bits from that position to MSB
        for i in range(self.WIDTH):
            bit_val = 0
            for j in range(i, self.WIDTH):
                bit_val ^= (gray_val >> j) & 1
            binary_val |= (bit_val << i)

        return binary_val

    async def check_conversion(self, gray_val):
        """Check a single conversion"""
        self.gray.value = gray_val
        await Timer(1, units='ns')  # Allow combinational logic to settle

        actual_binary = int(self.binary.value)
        expected_binary = self.gray_to_bin_reference(gray_val)

        success = actual_binary == expected_binary

        if not success or self.DEBUG:
            self.log.info(f"Gray: 0x{gray_val:0{(self.WIDTH+3)//4}X} "
                         f"-> Binary: 0x{actual_binary:0{(self.WIDTH+3)//4}X} "
                         f"(Expected: 0x{expected_binary:0{(self.WIDTH+3)//4}X}) "
                         f"{'✓' if success else '✗'}")

        return success, actual_binary, expected_binary

    async def test_exhaustive(self):
        """Test all possible values (for small widths)"""
        if self.WIDTH > 16:
            self.log.info(f"Skipping exhaustive test for WIDTH={self.WIDTH} (too large)")
            return True

        self.log.info(f"Testing exhaustive conversion for WIDTH={self.WIDTH}")

        all_passed = True
        failed_count = 0

        for gray_val in range(self.max_value + 1):
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'exhaustive',
                    'gray_input': gray_val,
                    'expected_binary': expected,
                    'actual_binary': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'basic' and failed_count >= 5:
                    break

        # Store summary result
        result = {
            'test_type': 'exhaustive',
            'total_tests': min(self.max_value + 1, gray_val + 1),
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

        for i, gray_val in enumerate(test_values):
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'random',
                    'test_index': i,
                    'gray_input': gray_val,
                    'expected_binary': expected,
                    'actual_binary': actual,
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

    async def test_inverse_property(self):
        """Test that gray2bin is inverse of bin2gray"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping inverse property test")
            return True

        self.log.info(f"Testing inverse property (bin->gray->bin)")

        all_passed = True
        failed_count = 0

        # Number of random tests
        num_tests = min(1000 if self.TEST_LEVEL == 'medium' else 5000, self.max_value + 1)

        test_values = []
        # Include corner cases
        corner_cases = [0, 1, self.max_value, self.max_value - 1]
        if self.WIDTH > 2:
            corner_cases.extend([
                1 << (self.WIDTH - 1),
                (1 << (self.WIDTH - 1)) - 1,
            ])

        for i in range(self.WIDTH):
            corner_cases.append(1 << i)

        corner_cases = list(set([val for val in corner_cases if val <= self.max_value]))
        test_values.extend(corner_cases)

        # Add random values
        while len(test_values) < num_tests:
            val = random.randint(0, self.max_value)
            if val not in test_values:
                test_values.append(val)

        test_values = test_values[:num_tests]

        for i, original_binary in enumerate(test_values):
            # Convert binary to gray using reference
            gray_val = self.bin_to_gray_reference(original_binary)

            # Convert gray back to binary using DUT
            success, recovered_binary, expected_binary = await self.check_conversion(gray_val)

            # Check if we recovered the original binary
            inverse_success = recovered_binary == original_binary

            if not success or not inverse_success:
                failed_count += 1
                all_passed = False

                self.log.error(f"Inverse property failure: "
                                f"Original binary: 0x{original_binary:X}, "
                                f"Gray: 0x{gray_val:X}, "
                                f"Recovered binary: 0x{recovered_binary:X}")

                # Store failure
                result = {
                    'test_type': 'inverse_property',
                    'original_binary': original_binary,
                    'intermediate_gray': gray_val,
                    'recovered_binary': recovered_binary,
                    'conversion_success': success,
                    'inverse_success': inverse_success,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for medium tests
                if self.TEST_LEVEL == 'medium' and failed_count >= 10:
                    break

        # Store summary result
        result = {
            'test_type': 'inverse_property',
            'total_tests': min(len(test_values), i + 1),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Inverse property test: {result['total_tests']} tests, {failed_count} failures")

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running GRAY2BIN tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = []

        # Choose appropriate test strategy based on width
        if self.WIDTH <= 16:
            test_functions.append((self.test_exhaustive, "Exhaustive conversion"))
        else:
            test_functions.append((self.test_random_values, "Random value conversion"))

        if self.TEST_LEVEL in ['medium', 'full']:
            test_functions.append((self.test_inverse_property, "Inverse property"))

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
        self.log.info(f"Overall GRAY2BIN result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed


@cocotb.test(timeout_time=60000, timeout_unit="us")
async def gray2bin_test(dut):
    """Test for Gray Code to Binary Converter module"""
    tb = Gray2BinTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"GRAY2BIN test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Gray2Bin test FAILED - {len(tb.test_failures)} failures detected"

    return passed


def generate_params():
    """Generate test parameters"""
    widths = [4, 8, 16, 32]
    test_levels = ['full']

    valid_params = []
    for width, test_level in product(widths, test_levels):
        valid_params.append((width, test_level))

    return valid_params


params = generate_params()


@pytest.mark.parametrize("width, test_level", params)
def test_gray2bin(request, width, test_level):
    """
    Parameterized Gray Code to Binary Converter test
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "gray2bin"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/gray2bin.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    width_str = TBBase.format_dec(width, 2)
    test_name_plus_params = f"test_gray2bin_w{width_str}_{test_level}"
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
