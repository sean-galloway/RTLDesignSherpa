# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: Bin2GrayTB
# Purpose: Testbench for bin2gray
# Subsystem: framework
#
# Extracted from val/cdc/test_bin2gray.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from cocotb.triggers import Timer
from TBClasses.shared.tbbase import TBBase


class Bin2GrayTB(TBBase):
    """Testbench for Binary to Gray Code Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '4'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

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
                if self.TEST_LEVEL == 'gate' and failed_count >= 5:
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
        if self.TEST_LEVEL == 'gate':
            num_tests = min(100, self.max_value + 1)
        elif self.TEST_LEVEL == 'func':
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
                if self.TEST_LEVEL == 'gate' and failed_count >= 10:
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
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping sequential pattern test")
            return True

        self.log.info(f"Testing sequential patterns")

        all_passed = True
        failed_count = 0

        # Test Gray code property: adjacent values differ by only one bit
        num_tests = min(1000 if self.TEST_LEVEL == 'func' else 5000, self.max_value)

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

        if self.TEST_LEVEL in ['func', 'full']:
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
