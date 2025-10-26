# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AdderTB
# Purpose: Adder Testing Module
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Adder Testing Module

This module provides a robust testbench for various adder implementations.
It contains a base class that can be extended for different adder architectures.
"""
import os
import random
import contextlib
import itertools

from cocotb.triggers import Timer
from cocotb.utils import get_sim_time
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class AdderTB(TBBase):
    """Base Testbench for various adder implementations

    This class provides common functionality for testing various
    adder architectures and configurations.
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

    async def main_loop(self, count: int = 256) -> None:
        """Main test loop for standard adders.

        Tests all combinations of inputs up to max_val or randomly samples
        if max_val is larger than count.

        Args:
            count: Number of test vectors to generate if random sampling
        """
        self.log.info("Starting Main Test")
        c_list = [0, 1]  # Carry input values to test

        # Determine if we need to test all possible values or random sampling
        if self.max_val < count:
            self.log.info(f"Testing all {self.max_val} possible values")
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            self.log.info(f"Random sampling with {count} test vectors")
            a_list = [random.randint(0, self.mask) for _ in range(count)]
            b_list = [random.randint(0, self.mask) for _ in range(count)]

        total_tests = len(a_list) * len(b_list) * len(c_list)
        self.log.info(f"Will run {total_tests} total test cases")

        for test_idx, (a, b, c_in) in enumerate(itertools.product(a_list, b_list, c_list)):
            # Log progress periodically
            if test_idx % max(1, total_tests // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{total_tests} tests completed")

            msg = f'Testing {a=} {b=} {c_in=}'
            self.log.debug(msg)

            # Apply the inputs to DUT
            try:
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                self.dut.i_c.value = c_in
            except AttributeError as e:
                self.log.warning(f"Error setting inputs: {e}")
                continue

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Read outputs
            try:
                ow_sum = int(self.dut.ow_sum.value)
                ow_carry = int(self.dut.ow_carry.value)
            except AttributeError as e:
                self.log.warning(f"Error reading outputs: {e}")
                continue

            # Calculate expected values
            expected_sum = (a + b + c_in) & self.mask
            expected_carry = int(a + b + c_in >= self.max_val)

            # Verify results
            if (ow_sum != expected_sum) or (ow_carry != expected_carry):
                self.log.error(f"Test failed at {test_idx+1}/{total_tests}:")
                self.log.error(f"  Input: a={a}, b={b}, c_in={c_in}")
                self.log.error(f"  Expected: sum={expected_sum}, carry={expected_carry}")
                self.log.error(f"  Actual: sum={ow_sum}, carry={ow_carry}")
                self.fail_count += 1

                # For comprehensive analysis, should also print binary representation
                # of both expected and actual results for easier debugging
                self.log.error("  Binary comparison:")
                self.log.error(f"    a      = {bin(a)[2:].zfill(self.N)}")
                self.log.error(f"    b      = {bin(b)[2:].zfill(self.N)}")
                self.log.error(f"    c_in   = {bin(c_in)[2:]}")
                self.log.error(f"    exp_sum= {bin(expected_sum)[2:].zfill(self.N)}")
                self.log.error(f"    act_sum= {bin(ow_sum)[2:].zfill(self.N)}")

                assert False, f"Adder test failed: Input: a={a}, b={b}, c_in={c_in}\nExpected: sum={expected_sum}, carry={expected_carry}\nGot: sum={ow_sum}, carry={ow_carry}"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def half_adder_test(self) -> None:
        """Specific test for half adders.

        Tests all four input combinations for a half adder.
        Half adders only have i_a and i_b inputs (no carry in).
        """
        self.log.info("Starting Half Adder Test")

        # Define the expected results for all input combinations in the format:
        # (i_a, i_b) -> (ow_sum, ow_carry)
        expected_results = {
            (0, 0): (0, 0),
            (0, 1): (1, 0),
            (1, 0): (1, 0),
            (1, 1): (0, 1)
        }

        for inputs, expected_output in expected_results.items():
            self.dut.i_a.value = inputs[0]
            self.dut.i_b.value = inputs[1]

            await Timer(1, units='ns')  # wait for the combinatorial logic to settle

            # Get actual output
            actual_output = (int(self.dut.ow_sum.value), int(self.dut.ow_carry.value))

            # Verify results
            if actual_output != expected_output:
                self.log.error(f"Half adder test failed:")
                self.log.error(f"  Inputs: a={inputs[0]}, b={inputs[1]}")
                self.log.error(f"  Expected: {expected_output}")
                self.log.error(f"  Actual: {actual_output}")
                self.fail_count += 1
                assert False, f"Half adder test failed for inputs {inputs}"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Half Adder Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def main_loop_carry_save(self, count: int = 256) -> None:
        """Test loop for carry-save adders.

        Carry-save adders produce separate sum and carry outputs for each bit position.

        Args:
            count: Number of test vectors to generate if random sampling
        """
        self.log.info("Starting Carry-Save Adder Test")
        msg = f'{count=}'
        self.log.debug(msg)

        c_list = [0, 1]
        if self.max_val < count:
            self.log.info(f"Testing all {self.max_val} possible values")
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            self.log.info(f"Random sampling with {count} test vectors")
            a_list = [random.randint(0, self.mask) for _ in range(count)]
            b_list = [random.randint(0, self.mask) for _ in range(count)]

        total_tests = len(a_list) * len(b_list) * len(c_list)
        self.log.info(f"Will run {total_tests} total test cases")

        for test_idx, (a, b, c_in) in enumerate(itertools.product(a_list, b_list, c_list)):
            # Log progress periodically
            if test_idx % max(1, total_tests // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{total_tests} tests completed")

            msg = f'Testing {a=} {b=} {c_in=}'
            self.log.debug(msg)

            # Apply the inputs to DUT
            try:
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                self.dut.i_c.value = c_in
            except AttributeError as e:
                self.log.warning(f"Error setting inputs: {e}")
                continue

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Python-based reference computation for sum and carry
            expected_sum = [0] * self.N
            expected_carry = [0] * self.N

            for i in range(self.N):
                a_bit = (a >> i) & 1
                b_bit = (b >> i) & 1
                c_bit = (c_in >> i) & 1
                expected_sum[i] = a_bit ^ b_bit ^ c_bit
                expected_carry[i] = (a_bit & b_bit) | (a_bit & c_bit) | (b_bit & c_bit)

            # Convert bit arrays to integers
            expected_sum_int = int("".join(str(bit) for bit in reversed(expected_sum)), 2)
            expected_carry_int = int("".join(str(bit) for bit in reversed(expected_carry)), 2)

            # Get DUT outputs
            ow_sum = int(self.dut.ow_sum.value)
            ow_carry = int(self.dut.ow_carry.value)

            # Verify results
            if (ow_sum != expected_sum_int) or (ow_carry != expected_carry_int):
                self.log.error(f"Carry-save test failed for inputs: a={a}, b={b}, c_in={c_in}")
                self.log.error(f"Expected: sum={expected_sum_int}, carry={expected_carry_int}")
                self.log.error(f"Got: sum={ow_sum}, carry={ow_carry}")

                # Print detailed bit-by-bit analysis for debugging
                self.log.error("Bit-by-bit analysis:")
                for i in range(self.N):
                    a_bit = (a >> i) & 1
                    b_bit = (b >> i) & 1
                    c_bit = (c_in >> i) & 1
                    exp_sum_bit = expected_sum[i]
                    exp_carry_bit = expected_carry[i]
                    actual_sum_bit = (ow_sum >> i) & 1
                    actual_carry_bit = (ow_carry >> i) & 1

                    if (exp_sum_bit != actual_sum_bit) or (exp_carry_bit != actual_carry_bit):
                        self.log.error(f"  Bit {i}: a={a_bit}, b={b_bit}, c={c_bit}")
                        self.log.error(f"    Expected: sum={exp_sum_bit}, carry={exp_carry_bit}")
                        self.log.error(f"    Actual: sum={actual_sum_bit}, carry={actual_carry_bit}")

                self.fail_count += 1
                assert False, f"Carry-save adder test failed for inputs: a={a}, b={b}, c_in={c_in}"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Carry-Save Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def clear_interface(self) -> None:
        """Clear the DUT interface by setting all inputs to 0."""
        self.log.debug('Clearing DUT interface')
        with contextlib.suppress(AttributeError):
            self.dut.i_a.value = 0
            self.dut.i_b.value = 0
            self.dut.i_c.value = 0

    def print_settings(self) -> None:
        """Print the current testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('Adder Testbench Settings:')
        self.log.info(f'    DUT:   {self.dut_type}')
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    Mask:  0x{self.mask:X}')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def walking_ones_test(self) -> None:
        """Walking ones test pattern.

        Tests the adder with a sequential pattern where a single bit
        is set to 1 and walks through all bit positions.
        """
        self.log.info("Starting Walking Ones Test")

        # Test with walking ones pattern (single bit set to 1, shifted through all positions)
        for pos in range(self.N):
            a = 1 << pos  # Set only the bit at position 'pos' to 1

            # Test with b=0 and all carries
            for c_in in [0, 1]:
                b = 0

                # Apply the inputs to DUT
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                self.dut.i_c.value = c_in

                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')

                # Calculate expected values
                expected_sum = (a + b + c_in) & self.mask
                expected_carry = int(a + b + c_in >= self.max_val)

                # Read outputs
                ow_sum = int(self.dut.ow_sum.value)
                ow_carry = int(self.dut.ow_carry.value)

                # Verify results
                if (ow_sum != expected_sum) or (ow_carry != expected_carry):
                    self.log.error(f"Walking ones test failed:")
                    self.log.error(f"  Input: a=0b{bin(a)[2:].zfill(self.N)}, b=0b{bin(b)[2:].zfill(self.N)}, c_in={c_in}")
                    self.log.error(f"  Expected: sum=0b{bin(expected_sum)[2:].zfill(self.N)}, carry={expected_carry}")
                    self.log.error(f"  Actual: sum=0b{bin(ow_sum)[2:].zfill(self.N)}, carry={ow_carry}")
                    self.fail_count += 1
                    assert False, f"Walking ones test failed at bit position {pos}"
                else:
                    self.pass_count += 1

                self.test_count += 1

        # Test with b as walking ones
        for pos in range(self.N):
            b = 1 << pos  # Set only the bit at position 'pos' to 1

            # Test with a=0 and all carries
            for c_in in [0, 1]:
                a = 0

                # Apply the inputs to DUT
                self.dut.i_a.value = a
                self.dut.i_b.value = b
                self.dut.i_c.value = c_in

                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')

                # Calculate expected values
                expected_sum = (a + b + c_in) & self.mask
                expected_carry = int(a + b + c_in >= self.max_val)

                # Read outputs
                ow_sum = int(self.dut.ow_sum.value)
                ow_carry = int(self.dut.ow_carry.value)

                # Verify results
                if (ow_sum != expected_sum) or (ow_carry != expected_carry):
                    self.log.error(f"Walking ones test failed:")
                    self.log.error(f"  Input: a=0b{bin(a)[2:].zfill(self.N)}, b=0b{bin(b)[2:].zfill(self.N)}, c_in={c_in}")
                    self.log.error(f"  Expected: sum=0b{bin(expected_sum)[2:].zfill(self.N)}, carry={expected_carry}")
                    self.log.error(f"  Actual: sum=0b{bin(ow_sum)[2:].zfill(self.N)}, carry={ow_carry}")
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

        # Test combinations of these patterns with different carry inputs
        for a, b, c_in in itertools.product([pattern1, pattern2], [pattern1, pattern2], [0, 1]):
            # Apply the inputs to DUT
            self.dut.i_a.value = a
            self.dut.i_b.value = b
            self.dut.i_c.value = c_in

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Calculate expected values
            expected_sum = (a + b + c_in) & self.mask
            expected_carry = int(a + b + c_in >= self.max_val)

            # Read outputs
            ow_sum = int(self.dut.ow_sum.value)
            ow_carry = int(self.dut.ow_carry.value)

            # Verify results
            if (ow_sum != expected_sum) or (ow_carry != expected_carry):
                self.log.error(f"Alternating pattern test failed:")
                self.log.error(f"  Input: a=0b{bin(a)[2:].zfill(self.N)}, b=0b{bin(b)[2:].zfill(self.N)}, c_in={c_in}")
                self.log.error(f"  Expected: sum=0b{bin(expected_sum)[2:].zfill(self.N)}, carry={expected_carry}")
                self.log.error(f"  Actual: sum=0b{bin(ow_sum)[2:].zfill(self.N)}, carry={ow_carry}")
                self.fail_count += 1
                assert False, f"Alternating pattern test failed"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Alternating Pattern Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

    async def run_comprehensive_tests(self) -> None:
        """Run a comprehensive suite of tests based on test_level.

        This combines multiple test patterns to thoroughly test the adder.
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
