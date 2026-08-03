# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: ShifterBarrelTB
# Purpose: Testbench for shifter_barrel
# Subsystem: framework
#
# Extracted from val/common/test_shifter_barrel.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class ShifterBarrelTB(TBBase):
    """
    Testbench for the Barrel Shifter module
    Features:
    - Verify all shift modes (no shift, logical right, arithmetic right, wrap right, logical left, wrap left)
    - Test various shift amounts
    - Test with different data widths
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))

        # Calculate maximum data value based on width
        self.MAX_DATA = (1 << self.WIDTH) - 1
        self.SHIFT_BITS = (self.WIDTH).bit_length()  # Number of bits needed to represent shift amount

        # Initialize random generator
        random.seed(self.SEED)

        # Extract DUT signals
        self.data = self.dut.data
        self.ctrl = self.dut.ctrl
        self.shift_amount = self.dut.shift_amount
        self.data_out = self.dut.data_out

        # Control signal definitions for clarity
        self.CTRL_NO_SHIFT = 0
        self.CTRL_RIGHT_SHIFT = 1
        self.CTRL_ARITH_RIGHT_SHIFT = 2
        self.CTRL_RIGHT_SHIFT_WRAP = 3
        self.CTRL_LEFT_SHIFT = 4
        self.CTRL_LEFT_SHIFT_WRAP = 6

        # Log configuration
        self.log.info("Barrel Shifter TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")

        # Test results storage
        self.test_results = []

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

    async def drive_and_check(self, data, ctrl, shift_amount, expected=None):
        """
        Drive the inputs and check the outputs

        Args:
            data: Input data
            ctrl: Control signal
            shift_amount: Shift amount
            expected: Expected output (None for auto calculation)

        Returns:
            True if output matched expected value
        """
        # Mask to correct bit widths
        data &= self.MAX_DATA
        ctrl &= 0x7
        shift_amount &= ((1 << self.SHIFT_BITS) - 1)

        time_ns = get_sim_time('ns')
        self.log.info(f"Testing @ {time_ns}ns: data=0x{data:x}, ctrl={ctrl}, shift_amount={shift_amount}")

        # Drive the inputs
        self.data.value = data
        self.ctrl.value = ctrl
        self.shift_amount.value = shift_amount

        # Wait a small time for combinational logic to settle
        await Timer(1, units='ns')

        # Read output
        actual_output = int(self.data_out.value)

        # Calculate expected output if not provided
        if expected is None:
            expected = self._calculate_expected_output(data, ctrl, shift_amount)

        # Check result
        match = (actual_output == expected)

        # Log result
        if match:
            self.log.info(f"PASS: output=0x{actual_output:x}")
        else:
            self.log.error(f"FAIL: data=0x{data:x}, ctrl={ctrl}, shift_amount={shift_amount}")
            self.log.error(f"  Expected=0x{expected:x}, Actual=0x{actual_output:x}")

        # Store result for reporting
        self.test_results.append({
            'data': data,
            'ctrl': ctrl,
            'shift_amount': shift_amount,
            'expected': expected,
            'actual': actual_output,
            'match': match
        })

        return match

    def _calculate_expected_output(self, data, ctrl, shift_amount):
        """
        Calculate the expected output based on the inputs

        Args:
            data: Input data
            ctrl: Control signal
            shift_amount: Shift amount

        Returns:
            Expected output
        """
        # Ensure inputs are masked to appropriate width
        data &= self.MAX_DATA
        shift_amount_mod = shift_amount % self.WIDTH

        # Calculate expected output based on control signal
        if ctrl == self.CTRL_NO_SHIFT:
            # No shift
            return data
        elif ctrl == self.CTRL_RIGHT_SHIFT:
            # Logical right shift (no wrap)
            return data if shift_amount_mod == 0 else data >> shift_amount
        elif ctrl == self.CTRL_ARITH_RIGHT_SHIFT:
            # Arithmetic right shift
            # Check if MSB is set (negative number)
            msb_set = (data >> (self.WIDTH - 1)) & 1
            if not msb_set:
                # For positive numbers, same as logical shift
                return (data >> shift_amount_mod) & self.MAX_DATA
            # Arithmetic shift for negative number
            mask = ((1 << shift_amount_mod) - 1) << (self.WIDTH - shift_amount_mod)
            return ((data >> shift_amount_mod) | mask) & self.MAX_DATA
        elif ctrl == self.CTRL_RIGHT_SHIFT_WRAP:
            # Logical right shift with wrap
            if shift_amount_mod == 0:
                return data
            # Calculate wrapped bits
            wrapped = (data & ((1 << shift_amount_mod) - 1)) << (self.WIDTH - shift_amount_mod)
            # Calculate shifted bits
            shifted = data >> shift_amount_mod
            # Combine
            return (wrapped | shifted) & self.MAX_DATA
        elif ctrl == self.CTRL_LEFT_SHIFT:
            # Logical left shift (no wrap)
            return (
                data
                if shift_amount_mod == 0
                else (data << shift_amount) & self.MAX_DATA
            )
        elif ctrl == self.CTRL_LEFT_SHIFT_WRAP:
            # Logical left shift with wrap
            if shift_amount_mod == 0:
                return data
            # Calculate wrapped bits
            wrapped = (data >> (self.WIDTH - shift_amount_mod))
            # Calculate shifted bits
            shifted = (data << shift_amount_mod) & self.MAX_DATA
            # Combine
            return (wrapped | shifted) & self.MAX_DATA
        else:
            # Default is no shift
            return data

    async def test_no_shift(self):
        """
        Test no shift operation (ctrl=0)

        Returns:
            True if all tests passed
        """
        time_ns = get_sim_time('ns')
        self.log.info(f"Testing no shift operation (ctrl=0) @ {time_ns}ns")

        # Test cases for no shift
        test_cases = [
            0x00,
            0x01,
            0xFF & self.MAX_DATA,
            0xA5 & self.MAX_DATA,
            0x5A & self.MAX_DATA
        ]

        all_passed = True

        for data in test_cases:
            # Test with different shift amounts, but they should be ignored
            for shift in [0, 1, self.WIDTH // 2, self.WIDTH - 1]:
                test_passed = await self.drive_and_check(data, self.CTRL_NO_SHIFT, shift, data)

                if not test_passed:
                    all_passed = False
                    if self.TEST_LEVEL == 'gate':
                        return False

        return all_passed

    async def test_logical_right_shift(self):
        """
        Test logical right shift (ctrl=1)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing logical right shift (ctrl=1)")

        # Test cases for logical right shift
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 2),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_RIGHT_SHIFT, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    return False

        return all_passed

    async def test_arithmetic_right_shift(self):
        """
        Test arithmetic right shift (ctrl=2)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing arithmetic right shift (ctrl=2)")

        # Test cases for arithmetic right shift
        test_cases = [
            # (data, shift_amount)
            (0x7F & self.MAX_DATA, 1),    # Positive number (MSB=0)
            ((0x80 | 0x3F) & self.MAX_DATA, 1),    # Negative number (MSB=1)
            (0x7F & self.MAX_DATA, 4),    # Larger shift for positive
            ((0x80 | 0x3F) & self.MAX_DATA, 4)     # Larger shift for negative
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_ARITH_RIGHT_SHIFT, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    return False

        return all_passed

    async def test_right_shift_wrap(self):
        """
        Test right shift with wrap (ctrl=3)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing right shift with wrap (ctrl=3)")

        # Test cases for right shift with wrap
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 4),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_RIGHT_SHIFT_WRAP, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    return False

        return all_passed

    async def test_left_shift(self):
        """
        Test left shift (ctrl=4)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing left shift (ctrl=4)")

        # Test cases for left shift
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 2),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_LEFT_SHIFT, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    return False

        return all_passed

    async def test_left_shift_wrap(self):
        """
        Test left shift with wrap (ctrl=6)

        Returns:
            True if all tests passed
        """
        self.log.info("Testing left shift with wrap (ctrl=6)")

        # Test cases for left shift with wrap
        test_cases = [
            # (data, shift_amount)
            (0xFF & self.MAX_DATA, 0),    # No shift
            (0xFF & self.MAX_DATA, 1),    # Shift by 1
            (0xFF & self.MAX_DATA, 4),    # Shift by 4
            (0xA5 & self.MAX_DATA, 2),    # Alternating bits
            (0x0F & self.MAX_DATA, 4),    # Low nibble set
            (0xF0 & self.MAX_DATA, 4)     # High nibble set
        ]

        all_passed = True

        for data, shift in test_cases:
            test_passed = await self.drive_and_check(data, self.CTRL_LEFT_SHIFT_WRAP, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    return False

        return all_passed

    async def test_shift_amounts(self):
        """
        Test various shift amounts including 0, width, and full range

        Returns:
            True if all tests passed
        """
        self.log.info("Testing various shift amounts")

        # Test shift amounts
        shift_amounts = [0]  # No shift

        # Include more shift amounts based on test level
        if self.TEST_LEVEL == 'gate':
            shift_amounts.extend([1, self.WIDTH // 2, self.WIDTH - 1])
        elif self.TEST_LEVEL == 'func':
            shift_amounts.extend(list(range(1, min(self.WIDTH, 16))))
        else:  # full
            shift_amounts.extend(list(range(1, self.WIDTH + 8)))  # Include beyond width

        # Data patterns: use more patterns for full coverage
        if self.TEST_LEVEL == 'full':
            # Strategic patterns for comprehensive coverage
            data_patterns = [
                0x00,                        # All zeros
                self.MAX_DATA,               # All ones
                0xA5 & self.MAX_DATA,        # Alternating 10100101
                0x5A & self.MAX_DATA,        # Alternating 01011010
                0x01,                        # Single bit low
                (1 << (self.WIDTH - 1)) & self.MAX_DATA,  # Single bit high (MSB)
                0x0F & self.MAX_DATA,        # Low nibble
                (0xF0 << max(0, self.WIDTH - 8)) & self.MAX_DATA,  # High nibble
            ]
        else:
            data_patterns = [0xA5 & self.MAX_DATA]  # Single pattern for basic/medium

        all_passed = True

        for ctrl in [self.CTRL_RIGHT_SHIFT, self.CTRL_ARITH_RIGHT_SHIFT,
                        self.CTRL_RIGHT_SHIFT_WRAP, self.CTRL_LEFT_SHIFT,
                        self.CTRL_LEFT_SHIFT_WRAP]:
            for data in data_patterns:
                for shift in shift_amounts:
                    test_passed = await self.drive_and_check(data, ctrl, shift)

                    if not test_passed:
                        all_passed = False
                        if self.TEST_LEVEL == 'gate':
                            return False

        return all_passed

    async def test_random_patterns(self):
        """
        Test random data patterns

        Returns:
            True if all tests passed
        """
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping random pattern tests in gate mode")
            return True

        self.log.info("Testing random data patterns")

        # Determine number of tests based on test level
        num_tests = 10 if self.TEST_LEVEL == 'func' else 50

        all_passed = True

        for _ in range(num_tests):
            data = random.randint(0, self.MAX_DATA)
            ctrl = random.choice([self.CTRL_NO_SHIFT, self.CTRL_RIGHT_SHIFT,
                                    self.CTRL_ARITH_RIGHT_SHIFT, self.CTRL_RIGHT_SHIFT_WRAP,
                                    self.CTRL_LEFT_SHIFT, self.CTRL_LEFT_SHIFT_WRAP])
            shift = random.randint(0, self.WIDTH + 4)  # Include beyond width

            test_passed = await self.drive_and_check(data, ctrl, shift)

            if not test_passed:
                all_passed = False
                if self.TEST_LEVEL == 'func':
                    return False

        return all_passed

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        time_ns = get_sim_time('ns')
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL} @ {time_ns}ns")

        all_passed = True

        # 1. No shift test
        self.log.info("1. Testing no shift operation")
        no_shift_passed = await self.test_no_shift()
        if not no_shift_passed:
            self.log.error("No shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 2. Logical right shift test
        self.log.info("2. Testing logical right shift")
        right_shift_passed = await self.test_logical_right_shift()
        if not right_shift_passed:
            self.log.error("Logical right shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 3. Arithmetic right shift test
        self.log.info("3. Testing arithmetic right shift")
        arith_shift_passed = await self.test_arithmetic_right_shift()
        if not arith_shift_passed:
            self.log.error("Arithmetic right shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 4. Right shift with wrap test
        self.log.info("4. Testing right shift with wrap")
        right_wrap_passed = await self.test_right_shift_wrap()
        if not right_wrap_passed:
            self.log.error("Right shift wrap test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 5. Left shift test
        self.log.info("5. Testing left shift")
        left_shift_passed = await self.test_left_shift()
        if not left_shift_passed:
            self.log.error("Left shift test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 6. Left shift with wrap test
        self.log.info("6. Testing left shift with wrap")
        left_wrap_passed = await self.test_left_shift_wrap()
        if not left_wrap_passed:
            self.log.error("Left shift wrap test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 7. Shift amount test
        self.log.info("7. Testing various shift amounts")
        shift_amount_passed = await self.test_shift_amounts()
        if not shift_amount_passed:
            self.log.error("Shift amount test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 8. Random pattern test (func and full only)
        if self.TEST_LEVEL != 'gate':
            self.log.info("8. Testing random patterns")
            random_passed = await self.test_random_patterns()
            if not random_passed:
                self.log.error("Random pattern test failed")
                all_passed = False

        # Print summary
        self.print_summary()

        return all_passed

    def print_summary(self):
        """Print summary of test results"""
        total_tests = len(self.test_results)
        passed_tests = sum(bool(r['match'])
                        for r in self.test_results)

        self.log.info("="*50)
        self.log.info(f"Test Summary: {passed_tests}/{total_tests} tests passed")
        self.log.info("="*50)

        # Print detailed results based on test level
        if self.TEST_LEVEL != 'gate' and passed_tests < total_tests:
            self.log.info("Failed tests:")
            for i, result in enumerate(self.test_results):
                if not result['match']:
                    self.log.info(f"Test {i+1}:")
                    self.log.info(f"  Inputs: data=0x{result['data']:x}, ctrl={result['ctrl']}, shift={result['shift_amount']}")
                    self.log.info(f"  Expected=0x{result['expected']:x}, Actual=0x{result['actual']:x}")
