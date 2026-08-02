# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: GrayJ2BinTB
# Purpose: Testbench for johnson2bin
# Subsystem: framework
#
# Extracted from val/cdc/test_johnson2bin.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from TBClasses.shared.tbbase import TBBase


class GrayJ2BinTB(TBBase):
    """Testbench for Gray Johnson Counter to Binary Converter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.JCW = self.convert_to_int(os.environ.get('TEST_JCW', '10'))
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
        self.log.info(f"GrayJ2Bin TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"JCW={self.JCW}, WIDTH={self.WIDTH}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Calculate test ranges
        self.max_gray = (1 << self.JCW) - 1
        self.max_binary = (1 << self.WIDTH) - 1

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.gray = self.dut.gray
        self.binary = self.dut.binary

    async def setup_clock(self):
        """Setup clock (idempotent: one driver per sim -- repeated calls from
        each subtest must not stack a second Clock on the same signal)"""
        if not getattr(self, '_clk_started', False):
            cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
            self._clk_started = True
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.gray.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    def generate_johnson_sequence(self):
        """Generate valid Johnson counter sequence"""
        # Johnson counter sequence: shift register with inverted feedback
        # Produces 2*N different states in a cycle
        sequence = []
        state = 0

        for i in range(2 * self.JCW):
            sequence.append(state)

            # Shift left and add inverted MSB to LSB
            msb = (state >> (self.JCW - 1)) & 1
            state = ((state << 1) | (1 - msb)) & ((1 << self.JCW) - 1)

            # Prevent infinite loop
            if state in sequence:
                break

        return sequence

    def find_leading_one(self, value):
        """Find position of leading (most significant) one"""
        if value == 0:
            return None

        for i in range(self.JCW - 1, -1, -1):
            if (value >> i) & 1:
                return i
        return None

    def find_trailing_one(self, value):
        """Find position of trailing (least significant) one"""
        if value == 0:
            return None

        for i in range(self.JCW):
            if (value >> i) & 1:
                return i
        return None

    def grayj_to_binary_reference(self, gray_val):
        """Reference implementing the DOCUMENTED decode algorithm
        (docs/markdown/rtl-cdc/johnson2bin.md), not RTL observations. The
        previous version had special cases fitted to observed RTL output
        ("RTL shows it outputs 16") -- a systematic RTL conversion error
        would have been baked into the check (test-audit finding).

        Documented algorithm: all-zero -> 0; MSB set (second half) -> wrap
        flag | trailing_one (rightmost 1); MSB clear (first half) ->
        leading_one + 1 (leftmost 1 + 1). The all-ones case needs NO
        special case: MSB set with trailing_one=0 gives wrap|0 directly.
        Cross-check: on valid Johnson states this equals the position of
        the state in the twisted-ring sequence (next = {cur[JCW-2:0],
        ~cur[JCW-1]}) under the documented output format (MSB=wrap flag,
        low bits=within-half index) -- two independent derivations, and
        they must agree.
        """
        if gray_val == 0:
            return 0
        msb = (gray_val >> (self.JCW - 1)) & 1
        if msb:
            for i in range(self.JCW):
                if (gray_val >> i) & 1:
                    return (1 << (self.WIDTH - 1)) | i
            return (1 << (self.WIDTH - 1))  # all-ones: trailing_one == 0
        else:
            for i in range(self.JCW - 1, -1, -1):
                if (gray_val >> i) & 1:
                    return i + 1
            return 0

    async def check_conversion(self, gray_val):
        """Check a single Gray Johnson to binary conversion"""
        self.gray.value = gray_val
        await RisingEdge(self.clk)  # Clock the value in
        await Timer(1, units='ns')  # Allow for combinational settling

        actual_binary = int(self.binary.value)
        expected_binary = self.grayj_to_binary_reference(gray_val)

        success = actual_binary == expected_binary

        if not success or self.DEBUG:
            self.log.info(f"Gray: 0x{gray_val:0{(self.JCW+3)//4}X} "
                            f"-> Binary: {actual_binary:>3d} "
                            f"(Expected: {expected_binary:>3d}) "
                            f"{'✓' if success else '✗'}")

        return success, actual_binary, expected_binary

    async def test_johnson_sequence(self):
        """Test with valid Johnson counter sequence"""
        self.log.info(f"Testing Johnson counter sequence")

        await self.setup_clock()
        await self.reset_dut()

        # Generate valid Johnson sequence
        johnson_sequence = self.generate_johnson_sequence()

        all_passed = True
        failed_count = 0

        for i, gray_val in enumerate(johnson_sequence):
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'johnson_sequence',
                    'sequence_index': i,
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
            'test_type': 'johnson_sequence',
            'total_tests': min(len(johnson_sequence), i + 1 if 'i' in locals() else 0),
            'sequence_length': len(johnson_sequence),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Johnson sequence test: {result['total_tests']} tests, "
                        f"{failed_count} failures, sequence length: {len(johnson_sequence)}")

        return all_passed

    async def test_corner_cases(self):
        """Test corner cases"""
        self.log.info(f"Testing corner cases")

        await self.setup_clock()
        await self.reset_dut()

        corner_cases = [
            0,  # All zeros
            (1 << self.JCW) - 1,  # All ones
            1,  # Single LSB
            1 << (self.JCW - 1),  # Single MSB
        ]

        # Add some specific patterns
        if self.JCW >= 4:
            corner_cases.extend([
                0b1111,  # Lower nibble
                0b1111 << (self.JCW - 4),  # Upper nibble
            ])

        if self.JCW >= 8:
            corner_cases.extend([
                0b11110000,  # Alternating nibbles
                0b10101010,  # Alternating bits
            ])

        # Ensure all values fit in JCW bits
        corner_cases = [val & ((1 << self.JCW) - 1) for val in corner_cases]
        corner_cases = list(set(corner_cases))  # Remove duplicates

        all_passed = True
        failed_count = 0

        for gray_val in corner_cases:
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'corner_cases',
                    'gray_input': gray_val,
                    'expected_binary': expected,
                    'actual_binary': actual,
                    'success': False
                }
                self.test_failures.append(result)

        # Store summary result
        result = {
            'test_type': 'corner_cases',
            'total_tests': len(corner_cases),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Corner cases test: {len(corner_cases)} tests, {failed_count} failures")

        return all_passed

    async def test_random_values(self):
        """Test random Gray values"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping random values test")
            return True

        self.log.info(f"Testing random Gray values")

        await self.setup_clock()
        await self.reset_dut()

        # Determine number of tests based on level
        if self.TEST_LEVEL == 'func':
            num_tests = min(100, self.max_gray + 1)
        else:  # full
            num_tests = min(500, self.max_gray + 1)

        all_passed = True
        failed_count = 0

        test_values = []
        for _ in range(num_tests):
            val = random.randint(0, self.max_gray)
            test_values.append(val)

        for i, gray_val in enumerate(test_values):
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

                # Store failure
                result = {
                    'test_type': 'random_values',
                    'test_index': i,
                    'gray_input': gray_val,
                    'expected_binary': expected,
                    'actual_binary': actual,
                    'success': False
                }
                self.test_failures.append(result)

                # Stop early if too many failures
                if failed_count >= 20:
                    break

        # Store summary result
        result = {
            'test_type': 'random_values',
            'total_tests': min(len(test_values), i + 1),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Random values test: {result['total_tests']} tests, {failed_count} failures")

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping reset behavior test")
            return True

        self.log.info(f"Testing reset behavior")

        await self.setup_clock()

        all_passed = True
        failed_count = 0

        # Test reset with various Gray values
        test_values = [0x55, 0xAA, self.max_gray, 0x123 & self.max_gray]

        for gray_val in test_values:
            # Set Gray value
            self.gray.value = gray_val
            await RisingEdge(self.clk)

            # Apply reset
            self.rst_n.value = 0
            await RisingEdge(self.clk)

            # johnson2bin is combinational -- its clk/rst_n ports are
            # declared but unused (see the module doc), so reset must NOT
            # change the decode of the current input. reset_output was read
            # into a variable and never compared for years (test audit).
            reset_output = int(self.binary.value)
            reset_expected = self.grayj_to_binary_reference(gray_val)
            if reset_output != reset_expected:
                self.log.error(f"Reset changed the combinational decode: "
                               f"gray=0x{gray_val:X} -> {reset_output} "
                               f"(expected {reset_expected})")
                failed_count += 1
                all_passed = False

            # Release reset
            self.rst_n.value = 1
            await RisingEdge(self.clk)

            # Check conversion after reset
            success, actual, expected = await self.check_conversion(gray_val)

            if not success:
                failed_count += 1
                all_passed = False

        # Store summary result
        result = {
            'test_type': 'reset_behavior',
            'total_tests': len(test_values),
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Reset behavior test: {len(test_values)} tests, {failed_count} failures")

        return all_passed

    async def test_timing_behavior(self):
        """Test timing behavior with rapid changes"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping timing behavior test")
            return True

        self.log.info(f"Testing timing behavior")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        failed_count = 0

        # Test rapid Gray value changes
        for i in range(50):
            gray_val1 = random.randint(0, self.max_gray)
            gray_val2 = random.randint(0, self.max_gray)

            # Set first value
            self.gray.value = gray_val1
            await RisingEdge(self.clk)
            result1 = int(self.binary.value)

            # Set second value
            self.gray.value = gray_val2
            await RisingEdge(self.clk)
            result2 = int(self.binary.value)

            # Verify results
            expected1 = self.grayj_to_binary_reference(gray_val1)
            expected2 = self.grayj_to_binary_reference(gray_val2)

            if result1 != expected1 or result2 != expected2:
                failed_count += 1
                all_passed = False

                self.log.error(f"Timing test failed: "
                                f"gray1=0x{gray_val1:X}->binary1={result1} (exp {expected1}), "
                                f"gray2=0x{gray_val2:X}->binary2={result2} (exp {expected2})")

        # Store summary result
        result = {
            'test_type': 'timing_behavior',
            'total_tests': 50,
            'failures': failed_count,
            'success': all_passed
        }
        self.test_results.append(result)

        self.log.info(f"Timing behavior test: 50 tests, {failed_count} failures")

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running GRAYJ2BIN tests at level: {self.TEST_LEVEL.upper()}")

        # Define test functions
        test_functions = [
            (self.test_johnson_sequence, "Johnson sequence"),
            (self.test_corner_cases, "Corner cases"),
            (self.test_random_values, "Random values"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_timing_behavior, "Timing behavior")
        ]

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
        self.log.info(f"Overall GRAYJ2BIN result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
