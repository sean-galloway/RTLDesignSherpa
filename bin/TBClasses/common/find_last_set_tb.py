# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: FindLastSetTB
# Purpose: Testbench for find_last_set
# Subsystem: framework
#
# Extracted from val/common/test_find_last_set.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import math
from cocotb.triggers import Timer
from TBClasses.shared.tbbase import TBBase


class FindLastSetTB(TBBase):
    """Testbench for Find Last Set module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"FindLastSet TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Calculate test ranges
        self.max_value = (1 << self.WIDTH) - 1
        self.index_width = math.ceil(math.log2(self.WIDTH)) if self.WIDTH > 1 else 1

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """No reset: this DUT is combinational."""
        return

    async def deassert_reset(self):
        """No reset: this DUT is combinational."""
        return

    async def setup_clocks_and_reset(self):
        """Combinational DUT: no clock or reset to set up."""
        return

    def _setup_signals(self):
        """Setup signal mappings"""
        self.data = self.dut.data
        self.index = self.dut.index

    def find_last_set_reference(self, data_val):
        """Reference implementation of find last set"""
        if data_val == 0:
            return 0  # Default when no bits are set

        for i in range(self.WIDTH - 1, -1, -1):
            if (data_val >> i) & 1:
                return i

        return 0  # Should not reach here if data_val != 0

    async def check_find_last_set(self, data_val):
        """Check a single find last set operation"""
        self.data.value = data_val
        await Timer(1, units='ns')  # Allow combinational logic to settle

        actual_index = int(self.index.value)
        expected_index = self.find_last_set_reference(data_val)

        success = actual_index == expected_index

        if not success or self.DEBUG:
            self.log.info(f"Data: 0x{data_val:0{(self.WIDTH+3)//4}X} "
                            f"-> Index: {actual_index} "
                            f"(Expected: {expected_index}) "
                            f"{'✓' if success else '✗'}")

        return success, actual_index, expected_index

    async def test_exhaustive(self):
        """Test all possible values (for small widths)"""
        if self.WIDTH > 20:
            self.log.info(f"Skipping exhaustive test for WIDTH={self.WIDTH} (too large)")
            return True

        self.log.info(f"Testing exhaustive find last set for WIDTH={self.WIDTH}")

        all_passed = True
        failed_count = 0

        for data_val in range(self.max_value + 1):
            success, actual, expected = await self.check_find_last_set(data_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'exhaustive',
                    'data_input': data_val,
                    'expected_index': expected,
                    'actual_index': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early for basic tests
                if self.TEST_LEVEL == 'gate' and failed_count >= 5:
                    break

        # Store summary result
        result = {
            'test_type': 'exhaustive',
            'total_tests': min(self.max_value + 1, data_val + 1),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Exhaustive test: {result['total_tests']} tests, "
                        f"{failed_count} failures")

        return all_passed

    async def test_random_values(self):
        """Test random values for larger widths"""
        self.log.info(f"Testing random find last set for WIDTH={self.WIDTH}")

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

        # Add single bit patterns
        for i in range(self.WIDTH):
            corner_cases.append(1 << i)

        # Add patterns with multiple bits
        if self.WIDTH >= 4:
            corner_cases.extend([
                0b1010101010101010 & self.max_value,  # Alternating pattern
                0b0111111111111111 & self.max_value,  # All but MSB
                0b1111111111111110 & self.max_value,  # All but LSB
            ])

        # Remove duplicates and ensure within range
        corner_cases = list(set([val for val in corner_cases if val <= self.max_value]))

        test_values = corner_cases.copy()

        # Add random values
        while len(test_values) < num_tests:
            val = random.randint(0, self.max_value)
            if val not in test_values:
                test_values.append(val)

        test_values = test_values[:num_tests]

        for i, data_val in enumerate(test_values):
            success, actual, expected = await self.check_find_last_set(data_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'random',
                    'test_index': i,
                    'data_input': data_val,
                    'expected_index': expected,
                    'actual_index': actual,
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

    async def test_single_bit_patterns(self):
        """Test single bit patterns specifically"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping single bit pattern test")
            return True

        self.log.info(f"Testing single bit patterns")

        all_passed = True
        failed_count = 0

        # Test each bit position individually
        for bit_pos in range(self.WIDTH):
            data_val = 1 << bit_pos
            success, actual, expected = await self.check_find_last_set(data_val)

            if not success:
                failed_count += 1
                all_passed = False

                self.log.error(f"Single bit test failed: bit_pos={bit_pos}, "
                                f"data=0x{data_val:X}, expected={expected}, actual={actual}")

                # Store failure
                result = {
                    'test_type': 'single_bit',
                    'bit_position': bit_pos,
                    'data_input': data_val,
                    'expected_index': expected,
                    'actual_index': actual,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'single_bit_patterns',
            'total_tests': self.WIDTH,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Single bit pattern test: {self.WIDTH} tests, {failed_count} failures")

        return all_passed

    async def test_priority_behavior(self):
        """Test that the function correctly prioritizes higher bits"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping priority behavior test")
            return True

        self.log.info(f"Testing priority behavior")

        all_passed = True
        failed_count = 0

        # Test patterns where multiple bits are set
        test_patterns = []

        # For each bit position, test with lower bits also set
        for last_bit in range(min(self.WIDTH, 8), 0, -1):  # Start from higher bits
            for num_lower_bits in range(1, min(4, last_bit)):
                # Create pattern with last_bit set and some lower bits set
                pattern = 1 << (last_bit - 1)
                for i in range(num_lower_bits):
                    if last_bit - 2 - i >= 0:
                        pattern |= 1 << (last_bit - 2 - i)

                test_patterns.append((pattern, last_bit - 1))

        # Also test some specific patterns
        if self.WIDTH >= 8:
            test_patterns.extend([
                (0b01111111, self.WIDTH - 2 if self.WIDTH > 7 else 6),  # All bits set except MSB
                (0b00111111, self.WIDTH - 3 if self.WIDTH > 6 else 5),  # All bits set except top 2
                (0b00001111, 3),  # Lower nibble set
            ])

        for i, (pattern, expected_last_bit) in enumerate(test_patterns):
            if pattern > self.max_value:
                # Adjust pattern to fit within width
                pattern = pattern & self.max_value
                # Recalculate expected last bit
                expected_last_bit = self.find_last_set_reference(pattern)

            success, actual, expected = await self.check_find_last_set(pattern)

            # Verify the expected matches our test expectation
            if expected != expected_last_bit:
                self.log.error(f"Test setup error: pattern=0x{pattern:X}, "
                                f"expected_last_bit={expected_last_bit}, "
                                f"reference_result={expected}")
                continue

            if not success:
                failed_count += 1
                all_passed = False

                self.log.error(f"Priority test failed: pattern=0x{pattern:X}, "
                                f"expected_last_bit={expected_last_bit}, "
                                f"actual={actual}")

                # Store failure
                result = {
                    'test_type': 'priority_behavior',
                    'test_index': i,
                    'pattern': pattern,
                    'expected_last_bit': expected_last_bit,
                    'actual_index': actual,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'priority_behavior',
            'total_tests': len([p for p, _ in test_patterns if p <= self.max_value]),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Priority behavior test: {result['total_tests']} tests, {failed_count} failures")

        return all_passed

    async def test_complementary_with_ffs(self):
        """Test relationship with find_first_set for symmetric patterns"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping complementary FFS test")
            return True

        self.log.info(f"Testing complementary behavior with find_first_set")

        all_passed = True
        failed_count = 0

        # Test symmetric patterns
        num_tests = min(100, self.max_value + 1)

        for i in range(num_tests):
            # Test with single bit patterns
            if i < self.WIDTH:
                pattern = 1 << i

                # Find last set should return the bit position
                success, fls_result, fls_expected = await self.check_find_last_set(pattern)

                if not success:
                    failed_count += 1
                    all_passed = False
                    continue

                # For single bit, FLS should return the bit position
                if fls_result != i:
                    failed_count += 1
                    all_passed = False

                    self.log.error(f"Single bit FLS test failed: bit={i}, "
                                    f"pattern=0x{pattern:X}, result={fls_result}")

            # Test with random patterns
            else:
                pattern = random.randint(1, self.max_value)  # Avoid 0

                success, actual, expected = await self.check_find_last_set(pattern)

                if not success:
                    failed_count += 1
                    all_passed = False

        # Store summary result
        result = {
            'test_type': 'complementary_ffs',
            'total_tests': num_tests,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Complementary FFS test: {num_tests} tests, {failed_count} failures")

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running FIND_LAST_SET tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = []

        # Choose appropriate test strategy based on width
        if self.WIDTH <= 20:
            test_functions.append((self.test_exhaustive, "Exhaustive find last set"))
        else:
            test_functions.append((self.test_random_values, "Random value find last set"))

        if self.TEST_LEVEL in ['func', 'full']:
            test_functions.append((self.test_single_bit_patterns, "Single bit patterns"))

        if self.TEST_LEVEL == 'full':
            test_functions.append((self.test_priority_behavior, "Priority behavior"))
            test_functions.append((self.test_complementary_with_ffs, "Complementary with FFS"))

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
        self.log.info(f"Overall FIND_LAST_SET result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
