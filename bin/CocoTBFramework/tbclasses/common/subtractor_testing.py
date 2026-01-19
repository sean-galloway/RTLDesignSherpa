# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SubtractorTB
# Purpose: Subtractor Testing Module
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Subtractor Testing Module

This module provides a robust testbench for various subtractor implementations.
It contains a base class that can be extended for different subtractor architectures.
"""
import os
import random
import contextlib
import itertools
from typing import List, Tuple, Dict, Any, Optional, Union

from cocotb.triggers import Timer
from cocotb.utils import get_sim_time
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class SubtractorTB(TBBase):
    """Base Testbench for various subtractor implementations

    This class provides common functionality for testing various
    subtractor architectures and configurations.
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '1'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize the random generator
        random.seed(self.seed)

        # Track test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        # Get DUT type
        self.dut_type = os.environ.get('DUT', 'unknown')
        self.log.info(f"Testing {self.dut_type} with N={self.N}")

    def _generate_strategic_test_vectors(self) -> list:
        """Generate strategic test vectors for larger bit widths (>8 bits).

        For bit widths > 8, exhaustive testing is impractical. Instead, use:
        - All powers of 2 (log2 values)
        - Powers of 2 ± 1 (boundary values)
        - Walking 0s and walking 1s patterns
        - Edge cases (0, max, alternating patterns)

        Returns:
            List of test values covering critical bit patterns
        """
        values = set()

        # Edge cases
        values.add(0)
        values.add(self.mask)  # All 1s

        # Powers of 2 and ±1 (log2 values)
        for i in range(self.N):
            pow2 = 1 << i
            values.add(pow2 & self.mask)
            values.add((pow2 - 1) & self.mask)
            values.add((pow2 + 1) & self.mask)

        # Walking 1s: single bit set at each position
        for i in range(self.N):
            values.add(1 << i)

        # Walking 0s: all bits set except one at each position
        for i in range(self.N):
            values.add(self.mask ^ (1 << i))

        # Alternating patterns
        pattern1 = 0
        pattern2 = 0
        for i in range(self.N):
            if i % 2 == 0:
                pattern1 |= (1 << i)
            else:
                pattern2 |= (1 << i)
        values.add(pattern1)  # 0101...
        values.add(pattern2)  # 1010...

        return sorted(list(values))

    async def main_loop(self, count: int = 256) -> None:
        """Main test loop for standard subtractors.

        Tests all combinations of inputs up to max_val or uses strategic
        sampling for larger bit widths.

        Args:
            count: Number of test vectors to generate if random sampling
        """
        self.log.info("Starting Main Test")
        b_list = [0, 1]  # Borrow input values to test

        # Determine test strategy based on bit width
        # Only use Cartesian product for very small widths (N <= 4, max 512 tests)
        if self.N <= 4:
            # Exhaustive testing for very small bit widths (N <= 4)
            self.log.info(f"Exhaustive testing: all {self.max_val}x{self.max_val}x2 combinations")
            a_list = list(range(self.max_val))
            b_list_vals = list(range(self.max_val))
            test_pairs = list(itertools.product(a_list, b_list_vals))
        elif self.N > 8:
            # Strategic coverage for larger bit widths
            strategic_values = self._generate_strategic_test_vectors()
            self.log.info(f"Strategic coverage: {len(strategic_values)} values for {self.N}-bit subtractor")
            test_pairs = list(itertools.product(strategic_values, strategic_values))
            self.log.info(f"Testing {len(test_pairs)} strategic value pairs")
        else:
            # Random sampling with paired vectors (NOT Cartesian product)
            self.log.info(f"Random sampling with {count} paired test vectors")
            test_pairs = [(random.randint(0, self.mask), random.randint(0, self.mask))
                          for _ in range(count)]

        total_tests = len(test_pairs) * len(b_list)
        self.log.info(f"Will run {total_tests} total test cases")

        for test_idx, ((a, b), b_in) in enumerate(itertools.product(test_pairs, b_list)):
            # Log progress periodically
            if test_idx % max(1, total_tests // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{total_tests} tests completed")

            msg = f'Testing {a=} {b=} {b_in=}'
            self.log.debug(msg)

            # Apply the inputs to DUT
            try:
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                self.dut.i_borrow_in.value = b_in
            except AttributeError:
                try:
                    # Try alternative naming convention
                    self.dut.i_a.value = a
                    self.dut.i_b.value = b
                    self.dut.i_b_in.value = b_in
                except AttributeError as e:
                    self.log.warning(f"Error setting inputs: {e}")
                    continue

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Read outputs
            try:
                ow_difference = int(self.dut.ow_difference.value)
                ow_borrow = int(self.dut.ow_carry_out.value)
            except AttributeError:
                try:
                    # Try alternative naming convention
                    ow_difference = int(self.dut.ow_d.value)
                    ow_borrow = int(self.dut.ow_b.value)
                except AttributeError as e:
                    self.log.warning(f"Error reading outputs: {e}")
                    continue

            # Calculate expected values for subtraction
            # a - b - borrow_in
            expected_difference = (a - b - b_in) & self.mask
            # Borrow out is 1 if result would be negative
            expected_borrow = int(a < (b + b_in))

            # Verify results
            if (ow_difference != expected_difference) or (ow_borrow != expected_borrow):
                self.log.error(f"Test failed at {test_idx+1}/{total_tests}:")
                self.log.error(f"  Input: a={a}, b={b}, borrow_in={b_in}")
                self.log.error(f"  Expected: difference={expected_difference}, borrow={expected_borrow}")
                self.log.error(f"  Actual: difference={ow_difference}, borrow={ow_borrow}")
                self.fail_count += 1

                # For comprehensive analysis, should also print binary representation
                # of both expected and actual results for easier debugging
                self.log.error(f"  Binary comparison:")
                self.log.error(f"    a      = {bin(a)[2:].zfill(self.N)}")
                self.log.error(f"    b      = {bin(b)[2:].zfill(self.N)}")
                self.log.error(f"    b_in   = {bin(b_in)[2:]}")
                self.log.error(f"    exp_diff = {bin(expected_difference)[2:].zfill(self.N)}")
                self.log.error(f"    act_diff = {bin(ow_difference)[2:].zfill(self.N)}")

                assert False, f"Subtractor test failed: Input: a={a}, b={b}, borrow_in={b_in}\nExpected: difference={expected_difference}, borrow={expected_borrow}\nGot: difference={ow_difference}, borrow={ow_borrow}"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def half_subtractor_test(self) -> None:
        """Specific test for half subtractors.

        Tests all four input combinations for a half subtractor.
        Half subtractors only have i_a and i_b inputs (no borrow in).
        """
        self.log.info("Starting Half Subtractor Test")

        # Define the expected results for all input combinations in the format:
        # (i_a, i_b) -> (ow_d, ow_b)
        expected_results = {
            (0, 0): (0, 0),
            (0, 1): (1, 1),  # Borrow out is 1 (negative result)
            (1, 0): (1, 0),
            (1, 1): (0, 0)
        }

        for inputs, expected_output in expected_results.items():
            self.dut.i_a.value = inputs[0]
            self.dut.i_b.value = inputs[1]

            await Timer(1, units='ns')  # wait for the combinatorial logic to settle

            # Get actual output
            try:
                actual_output = (int(self.dut.o_d.value), int(self.dut.o_b.value))
            except AttributeError:
                try:
                    actual_output = (int(self.dut.ow_d.value), int(self.dut.ow_b.value))
                except AttributeError as e:
                    self.log.warning(f"Error reading outputs: {e}")
                    continue

            # Verify results
            if actual_output != expected_output:
                self.log.error(f"Half subtractor test failed:")
                self.log.error(f"  Inputs: a={inputs[0]}, b={inputs[1]}")
                self.log.error(f"  Expected: {expected_output}")
                self.log.error(f"  Actual: {actual_output}")
                self.fail_count += 1
                assert False, f"Half subtractor test failed for inputs {inputs}"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Half Subtractor Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def clear_interface(self) -> None:
        """Clear the DUT interface by setting all inputs to 0."""
        self.log.debug('Clearing DUT interface')
        with contextlib.suppress(AttributeError):
            self.dut.i_a.value = 0
            self.dut.i_b.value = 0
            try:
                self.dut.i_borrow_in.value = 0
            except AttributeError:
                self.dut.i_b_in.value = 0

    def print_settings(self) -> None:
        """Print the current testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('Subtractor Testbench Settings:')
        self.log.info(f'    DUT:   {self.dut_type}')
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    Mask:  0x{self.mask:X}')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def walking_ones_test(self) -> None:
        """Walking ones test pattern.

        Tests the subtractor with a sequential pattern where a single bit
        is set to 1 and walks through all bit positions.
        """
        self.log.info("Starting Walking Ones Test")

        # Test with walking ones pattern (single bit set to 1, shifted through all positions)
        for pos in range(self.N):
            a = 1 << pos  # Set only the bit at position 'pos' to 1

            # Test with b=0 and all borrows
            for b_in in [0, 1]:
                b = 0

                # Apply the inputs to DUT
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                try:
                    self.dut.i_borrow_in.value = b_in
                except AttributeError:
                    self.dut.i_b_in.value = b_in

                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')

                # Calculate expected values for subtraction
                expected_difference = (a - b - b_in) & self.mask
                expected_borrow = int(a < (b + b_in))

                # Read outputs
                try:
                    ow_difference = int(self.dut.ow_difference.value)
                    ow_borrow = int(self.dut.ow_carry_out.value)
                except AttributeError:
                    ow_difference = int(self.dut.ow_d.value)
                    ow_borrow = int(self.dut.ow_b.value)

                # Verify results
                if (ow_difference != expected_difference) or (ow_borrow != expected_borrow):
                    self.log.error(f"Walking ones test failed:")
                    self.log.error(f"  Input: a=0b{bin(a)[2:].zfill(self.N)}, b=0b{bin(b)[2:].zfill(self.N)}, b_in={b_in}")
                    self.log.error(f"  Expected: difference=0b{bin(expected_difference)[2:].zfill(self.N)}, borrow={expected_borrow}")
                    self.log.error(f"  Actual: difference=0b{bin(ow_difference)[2:].zfill(self.N)}, borrow={ow_borrow}")
                    self.fail_count += 1
                    assert False, f"Walking ones test failed at bit position {pos}"
                else:
                    self.pass_count += 1

                self.test_count += 1

        # Test with b as walking ones
        for pos in range(self.N):
            b = 1 << pos  # Set only the bit at position 'pos' to 1

            # Test with a=max_val-1 (all bits set) and all borrows
            for b_in in [0, 1]:
                a = self.mask  # All bits set

                # Apply the inputs to DUT
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                try:
                    self.dut.i_borrow_in.value = b_in
                except AttributeError:
                    self.dut.i_b_in.value = b_in

                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')

                # Calculate expected values for subtraction
                expected_difference = (a - b - b_in) & self.mask
                expected_borrow = int(a < (b + b_in))

                # Read outputs
                try:
                    ow_difference = int(self.dut.ow_difference.value)
                    ow_borrow = int(self.dut.ow_carry_out.value)
                except AttributeError:
                    ow_difference = int(self.dut.ow_d.value)
                    ow_borrow = int(self.dut.ow_b.value)

                # Verify results
                if (ow_difference != expected_difference) or (ow_borrow != expected_borrow):
                    self.log.error(f"Walking ones test failed:")
                    self.log.error(f"  Input: a=0b{bin(a)[2:].zfill(self.N)}, b=0b{bin(b)[2:].zfill(self.N)}, b_in={b_in}")
                    self.log.error(f"  Expected: difference=0b{bin(expected_difference)[2:].zfill(self.N)}, borrow={expected_borrow}")
                    self.log.error(f"  Actual: difference=0b{bin(ow_difference)[2:].zfill(self.N)}, borrow={ow_borrow}")
                    self.fail_count += 1
                    assert False, f"Walking ones test failed at bit position {pos}"
                else:
                    self.pass_count += 1

                self.test_count += 1

        # Print test summary
        self.log.info(f"Walking Ones Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def alternating_pattern_test(self) -> None:
        """Test with alternating bit patterns (0101... and 1010...).

        This tests for issues with adjacent bits affecting each other.
        """
        self.log.info("Starting Alternating Pattern Test")

        # Create alternating patterns
        pattern1 = 0  # Will be 0101...
        pattern2 = 0  # Will be 1010...

        for i in range(self.N):
            if i % 2 == 0:  # Even bit positions
                pattern1 |= (1 << i)
            else:  # Odd bit positions
                pattern2 |= (1 << i)

        # Test combinations of these patterns with different borrow inputs
        for a, b, b_in in itertools.product([pattern1, pattern2], [pattern1, pattern2], [0, 1]):
            # Apply the inputs to DUT
            self.dut.i_a.value = a
            self.dut.i_b.value = b
            try:
                self.dut.i_borrow_in.value = b_in
            except AttributeError:
                self.dut.i_b_in.value = b_in

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Calculate expected values for subtraction
            expected_difference = (a - b - b_in) & self.mask
            expected_borrow = int(a < (b + b_in))

            # Read outputs
            try:
                ow_difference = int(self.dut.ow_difference.value)
                ow_borrow = int(self.dut.ow_carry_out.value)
            except AttributeError:
                ow_difference = int(self.dut.ow_d.value)
                ow_borrow = int(self.dut.ow_b.value)

            # Verify results
            if (ow_difference != expected_difference) or (ow_borrow != expected_borrow):
                self.log.error(f"Alternating pattern test failed:")
                self.log.error(f"  Input: a=0b{bin(a)[2:].zfill(self.N)}, b=0b{bin(b)[2:].zfill(self.N)}, b_in={b_in}")
                self.log.error(f"  Expected: difference=0b{bin(expected_difference)[2:].zfill(self.N)}, borrow={expected_borrow}")
                self.log.error(f"  Actual: difference=0b{bin(ow_difference)[2:].zfill(self.N)}, borrow={ow_borrow}")
                self.fail_count += 1
                assert False, f"Alternating pattern test failed"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Alternating Pattern Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def run_comprehensive_tests(self) -> None:
        """Run a comprehensive suite of tests based on test_level.

        This combines multiple test patterns to thoroughly test the subtractor.
        """
        self.log.info(f"Running comprehensive tests at {self.test_level} level")

        # Clear the interface
        await self.clear_interface()

        # Start with basic tests
        await self.wait_time(1, 'ns')

        # Determine test count based on level
        if self.test_level == 'basic':
            count = min(64, 2**self.N)
        elif self.test_level == 'medium':
            count = min(128, 2**self.N)
        else:  # 'full' or anything else
            count = min(256, 2**self.N)

        # Always run the main loop for standard tests
        await self.main_loop(count)

        # For medium and full test levels, add walking ones test
        if self.test_level in ['medium', 'full']:
            await self.walking_ones_test()

        # For full test level, add alternating pattern test
        if self.test_level == 'full':
            await self.alternating_pattern_test()

        # Print final test summary
        self.log.info(f"Comprehensive Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
