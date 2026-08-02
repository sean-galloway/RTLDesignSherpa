# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: Gray2BinTB
# Purpose: Testbench for gray2bin
# Subsystem: framework
#
# Extracted from val/cdc/test_gray2bin.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from cocotb.triggers import Timer
from TBClasses.shared.tbbase import TBBase


class Gray2BinTB(TBBase):
    """Testbench for Gray Code to Binary Converter module"""

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
                if self.TEST_LEVEL == 'gate' and failed_count >= 5:
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

    async def test_inverse_property(self):
        """Test that gray2bin is inverse of bin2gray"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping inverse property test")
            return True

        self.log.info(f"Testing inverse property (bin->gray->bin)")

        all_passed = True
        failed_count = 0

        # Number of random tests
        num_tests = min(1000 if self.TEST_LEVEL == 'func' else 5000, self.max_value + 1)

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

                # Stop early for func tests
                if self.TEST_LEVEL == 'func' and failed_count >= 10:
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

        if self.TEST_LEVEL in ['func', 'full']:
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
