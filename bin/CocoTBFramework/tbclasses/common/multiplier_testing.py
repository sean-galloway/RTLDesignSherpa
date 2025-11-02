# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MultiplierTB
# Purpose: Multiplier Testing Module
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Multiplier Testing Module

This module provides a robust testbench for various multiplier implementations.
It contains a base class that can be extended for different multiplier architectures.
"""
import os
import random
import contextlib
import itertools
from typing import List, Tuple, Dict, Any, Optional, Union

from cocotb.triggers import Timer
from cocotb.utils import get_sim_time
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class MultiplierTB(TBBase):
    """Base Testbench for various multiplier implementations

    This class provides common functionality for testing various
    multiplier architectures and configurations.
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '8'))
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

    async def main_loop(self, count: int = 256) -> list:
        """Main test loop for multipliers.

        Tests various combinations of inputs up to max_val or randomly samples
        if max_val is larger than count.

        Args:
            count: Number of test vectors to generate if random sampling

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        failures = []
        self.log.info("Starting Main Test")

        # Determine if we need to test all possible values or random sampling
        if self.max_val * self.max_val < count:
            self.log.info(f"Testing all {self.max_val} possible values")
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            self.log.info(f"Random sampling with {count} test vectors")
            a_list = [random.randint(0, self.mask) for _ in range(count)]
            b_list = [random.randint(0, self.mask) for _ in range(count)]

        total_tests = len(a_list) * len(b_list)
        self.log.info(f"Will run {min(total_tests, count)} total test cases")

        test_idx = 0
        for a, b in itertools.product(a_list, b_list):
            # Stop when we've reached the desired count
            if test_idx >= count:
                break

            # Log progress periodically
            if test_idx % max(1, count // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{count} tests completed")

            msg = f'Testing {a=} {b=}'
            self.log.debug(msg)

            # Apply the inputs to DUT
            try:
                self.dut.i_multiplier.value = a
                self.dut.i_multiplicand.value = b
            except AttributeError as e:
                self.log.warning(f"Error setting inputs: {e}")
                continue

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Read outputs
            try:
                ow_product = int(self.dut.ow_product.value)
            except AttributeError as e:
                self.log.warning(f"Error reading outputs: {e}")
                continue

            # Calculate expected values
            expected_product = (a * b) & (2**(2*self.N) - 1)

            # Verify results
            if ow_product != expected_product:
                error_msg_lines = []
                error_msg_lines.append(f"Test failed at {test_idx+1}/{count}:")
                error_msg_lines.append(f"  Input: multiplier={a}, multiplicand={b}")
                error_msg_lines.append(f"  Expected: product={expected_product} (0x{expected_product:X})")
                error_msg_lines.append(f"  Actual: product={ow_product} (0x{ow_product:X})")

                # For comprehensive analysis, also print binary representation
                # of both expected and actual results for easier debugging
                error_msg_lines.append("  Binary comparison:")
                error_msg_lines.append(f"    multiplier   = {bin(a)[2:].zfill(self.N)}")
                error_msg_lines.append(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
                error_msg_lines.append(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
                error_msg_lines.append(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")

                if a > 0 and b > 0:
                    # Analyze bit by bit for partial products debug
                    error_msg_lines.append("  Analyzing partial products:")
                    for i in range(self.N):
                        for j in range(self.N):
                            bit_pos = i + j
                            partial_product = ((a >> i) & 1) & ((b >> j) & 1)
                            expected_bit = (expected_product >> bit_pos) & 1
                            actual_bit = (ow_product >> bit_pos) & 1
                            if expected_bit != actual_bit:
                                error_msg_lines.append(f"    Bit position {bit_pos}: Expected {expected_bit}, Got {actual_bit}")
                                error_msg_lines.append(f"      Partial product a[{i}] & b[{j}] = {partial_product}")

                error_str = "\n".join(error_msg_lines)
                self.log.error(error_str)
                failures.append(error_str)
                self.fail_count += 1
            else:
                self.pass_count += 1

            self.test_count += 1
            test_idx += 1

        # Print test summary
        self.log.info(f"Main Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        return failures

    async def booth_specific_test(self) -> list:
        """Test cases specifically designed to test Booth radix-4 multiplier edge cases.

        These test cases focus on patterns that exercise different Booth encoding groups
        and ensure proper sign extension is happening. The test adapts to different bit
        widths (N) automatically.

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        self.log.info("Starting Booth Radix-4 Specific Test")
        failures = []

        # Create bit-width specific values
        max_positive = (1 << (self.N - 1)) - 1     # Largest positive number (all 1s except MSB)
        min_negative = (1 << (self.N - 1))         # Most negative number (MSB set, rest 0)
        all_ones = (1 << self.N) - 1               # All ones (-1 in two's complement)

        # Generate recurring patterns scaled to the appropriate width
        def pattern_0101(width):
            pattern = 0
            for i in range(0, width, 2):
                if i < width:
                    pattern |= (1 << i)
            return pattern

        def pattern_1010(width):
            pattern = 0
            for i in range(1, width, 2):
                if i < width:
                    pattern |= (1 << i)
            return pattern

        # Generate patterns for this bit width
        pattern_01 = pattern_0101(self.N)
        pattern_10 = pattern_1010(self.N)

        # Basic test cases that apply to any bit width
        basic_cases = [
            # Small positive numbers
            (5, 7),               # Simple case with different booth groups
            (4, 15),              # Tests the +2 encoding

            # Numbers with interesting bit patterns
            (1, all_ones),        # 1 * (-1) = -1
            (all_ones, all_ones), # (-1) * (-1) = 1

            # Edge cases
            (0, max_positive),    # 0 * (2^(N-1)-1)
            (1, max_positive),    # 1 * (2^(N-1)-1)
            (max_positive, max_positive),  # Largest positive * Largest positive
            (min_negative, min_negative),  # Most negative * Most negative
            (min_negative, max_positive),  # Most negative * Largest positive

            # Patterns that exercise specific Booth encoding groups
            (3, 5),               # 0b11 * 0b101 - Tests 01|1 encoding
            (4, 7),               # 0b100 * 0b111 - Tests 01|11 encoding
            (4, 8),               # 0b100 * 0b1000 - Tests 10|00 encoding

            # Alternating patterns
            (pattern_01, pattern_10),  # 0b01010... * 0b10101...
        ]

        # Add some bit-width specific test cases
        width_specific_cases = []

        # Add values around power-of-2 boundaries
        for power in range(2, self.N-1):
            boundary = 1 << power
            width_specific_cases.extend([
                (boundary-1, boundary-1),  # Just below boundary
                (boundary, boundary),      # At boundary
                (boundary+1, boundary+1),  # Just above boundary
                (boundary-1, boundary),    # Cross boundary
                (boundary, boundary+1),    # Cross boundary
            ])

        # Add cases that have failed in the original test
        if self.N >= 8:
            width_specific_cases.append((5, 235))  # Failed in original 8-bit test

        # Combine all test cases
        all_test_cases = basic_cases + width_specific_cases

        # Run each test case
        for a, b in all_test_cases:
            # Ensure values fit within N bits
            a &= self.mask
            b &= self.mask

            # Apply the inputs to DUT
            self.dut.i_multiplier.value = a
            self.dut.i_multiplicand.value = b

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Read outputs
            ow_product = int(self.dut.ow_product.value)

            # Calculate expected values using signed arithmetic
            a_signed = a if a < (1 << (self.N - 1)) else a - (1 << self.N)
            b_signed = b if b < (1 << (self.N - 1)) else b - (1 << self.N)
            signed_product = a_signed * b_signed

            # Mask to 2*N bits
            expected_product = signed_product & ((1 << (2 * self.N)) - 1)

            # Verify results
            if ow_product != expected_product:
                error_msg_lines = []
                error_msg_lines.append("Booth specific test failed:")
                error_msg_lines.append(f"  Input: multiplier={a} (0x{a:X}), multiplicand={b} (0x{b:X})")
                error_msg_lines.append(f"  Signed values: a_signed={a_signed}, b_signed={b_signed}")
                error_msg_lines.append(f"  Expected: product={expected_product} (0x{expected_product:X})")
                error_msg_lines.append(f"  Actual: product={ow_product} (0x{ow_product:X})")

                # Print binary representation for easier debugging
                # For large bit widths, only show the relevant bits
                bit_display_width = min(32, 2*self.N)  # Limit display to keep logs readable

                a_bin = bin(a)[2:].zfill(self.N)
                b_bin = bin(b)[2:].zfill(self.N)
                exp_bin = bin(expected_product)[2:].zfill(2*self.N)
                act_bin = bin(ow_product)[2:].zfill(2*self.N)

                if self.N > 16:
                    # For large bit widths, show abbreviated binary with '...'
                    error_msg_lines.append("  Binary comparison (abbreviated):")
                    error_msg_lines.append(f"    multiplier   = {a_bin[:4]}...{a_bin[-4:]}")
                    error_msg_lines.append(f"    multiplicand = {b_bin[:4]}...{b_bin[-4:]}")
                    error_msg_lines.append(f"    exp_product  = {exp_bin[:8]}...{exp_bin[-8:]}")
                    error_msg_lines.append(f"    act_product  = {act_bin[:8]}...{act_bin[-8:]}")
                else:
                    # For smaller bit widths, show full binary
                    error_msg_lines.append("  Binary comparison:")
                    error_msg_lines.append(f"    multiplier   = {a_bin}")
                    error_msg_lines.append(f"    multiplicand = {b_bin}")
                    error_msg_lines.append(f"    exp_product  = {exp_bin}")
                    error_msg_lines.append(f"    act_product  = {act_bin}")

                # Find first bit position that differs
                for i in range(2*self.N):
                    if ((expected_product >> i) & 1) != ((ow_product >> i) & 1):
                        error_msg_lines.append(f"  First difference at bit position {i}: Expected {(expected_product >> i) & 1}, Got {(ow_product >> i) & 1}")
                        break

                # Booth group analysis scaled to bit width
                error_msg_lines.append("  Booth groups analysis:")
                num_groups = (self.N + 1) // 2

                for i in range(num_groups):
                    # Calculate current Booth group
                    if i == 0:
                        booth_group = ((a >> 1) & 1, a & 1, 0)
                        group_val = (booth_group[0] << 2) | (booth_group[1] << 1) | booth_group[2]
                    else:
                        low_idx = 2 * i - 1
                        mid_idx = 2 * i
                        high_idx = 2 * i + 1

                        if high_idx >= self.N:  # Out of bounds
                            high_bit = (a >> (self.N - 1)) & 1  # Sign bit
                            mid_bit = (a >> mid_idx) & 1 if mid_idx < self.N else high_bit
                            low_bit = (a >> low_idx) & 1 if low_idx < self.N else 0
                        else:
                            high_bit = (a >> high_idx) & 1
                            mid_bit = (a >> mid_idx) & 1
                            low_bit = (a >> low_idx) & 1

                        booth_group = (high_bit, mid_bit, low_bit)
                        group_val = (high_bit << 2) | (mid_bit << 1) | low_bit

                    # Determine operation based on Booth encoding
                    op = "Unknown"
                    if group_val in [0b000, 0b111]:
                        op = "0"
                    elif group_val in [0b001, 0b010]:
                        op = "+A"
                    elif group_val == 0b011:
                        op = "+2A"
                    elif group_val == 0b100:
                        op = "-2A"
                    elif group_val in [0b101, 0b110]:
                        op = "-A"

                    error_msg_lines.append(f"    Group {i}: bits={booth_group[0]}{booth_group[1]}{booth_group[2]} (value={group_val}) => operation: {op}")

                error_str = "\n".join(error_msg_lines)
                self.log.error(error_str)
                failures.append(error_str)
                self.fail_count += 1
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Booth Specific Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        return failures

    async def corner_cases_test(self) -> list:
        """Test with corner cases specific to multipliers.

        Includes cases like zeros, ones, powers of 2, max values, etc.

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        self.log.info("Starting Corner Cases Test")
        failures = []

        # Define corner cases
        corner_cases = [
            0,                  # Zero
            1,                  # One
            self.mask,          # All ones (max value)
            self.mask // 2,     # 01111...
            self.mask // 2 + 1, # 10000...
            0xA,                # 1010
            0x5,                # 0101
        ]

        # Add some powers of 2
        corner_cases.extend(1 << i for i in range(1, self.N))
        # Add some values with single bit set
        corner_cases.extend(1 << i for i in range(self.N))
        # Remove duplicates and ensure values fit in N bits
        corner_cases = list({case & self.mask for case in corner_cases})

        total_tests = len(corner_cases)**2
        self.log.info(f"Will run {total_tests} corner case tests")

        for a in corner_cases:
            for b in corner_cases:
                # Apply the inputs to DUT
                self.dut.i_multiplier.value = a
                self.dut.i_multiplicand.value = b

                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')

                # Read outputs
                ow_product = int(self.dut.ow_product.value)

                # Calculate expected values
                expected_product = (a * b) & (2**(2*self.N) - 1)

                # Verify results
                if ow_product != expected_product:
                    error_msg_lines = [
                        "Corner case test failed:",
                        f"  Input: multiplier={a} (0x{a:X}), multiplicand={b} (0x{b:X})",
                        f"  Expected: product={expected_product} (0x{expected_product:X})",
                        f"  Actual: product={ow_product} (0x{ow_product:X})",
                        "  Binary comparison:",
                        f"    multiplier   = {bin(a)[2:].zfill(self.N)}",
                    ]
                    error_msg_lines.append(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
                    error_msg_lines.append(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
                    error_msg_lines.append(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")

                    error_str = "\n".join(error_msg_lines)
                    self.log.error(error_str)
                    failures.append(error_str)
                    self.fail_count += 1
                else:
                    self.pass_count += 1

                self.test_count += 1

        # Print test summary
        self.log.info(f"Corner Cases Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        return failures

    async def walking_ones_test(self) -> list:
        """Walking ones test pattern.

        Tests the multiplier with a sequential pattern where a single bit
        is set to 1 and walks through all bit positions.

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        self.log.info("Starting Walking Ones Test")
        failures = []

        # Test with walking ones pattern in multiplier
        for pos_a in range(self.N):
            a = 1 << pos_a  # Set only the bit at position 'pos_a' to 1

            # Test against walking ones in multiplicand
            for pos_b in range(self.N):
                b = 1 << pos_b  # Set only the bit at position 'pos_b' to 1

                # Apply the inputs to DUT
                self.dut.i_multiplier.value = a
                self.dut.i_multiplicand.value = b

                # Wait for combinational logic to settle
                await self.wait_time(1, 'ns')

                # Calculate expected values - for walking ones, should be a single bit set
                expected_product = 1 << (pos_a + pos_b)

                # Read outputs
                ow_product = int(self.dut.ow_product.value)

                # Verify results
                if ow_product != expected_product:
                    error_msg_lines = [
                        "Walking ones test failed:",
                        f"  Input: multiplier=0b{bin(a)[2:].zfill(self.N)}, multiplicand=0b{bin(b)[2:].zfill(self.N)}",
                    ]
                    error_msg_lines.append(f"  Expected: product=0b{bin(expected_product)[2:].zfill(2*self.N)}")
                    error_msg_lines.extend(
                        (
                            f"  Actual: product=0b{bin(ow_product)[2:].zfill(2 * self.N)}",
                            f"  First difference at bit position {pos_a + pos_b}: Expected 1, Got {ow_product >> pos_a + pos_b & 1}",
                        )
                    )
                    error_str = "\n".join(error_msg_lines)
                    self.log.error(error_str)
                    failures.append(error_str)
                    self.fail_count += 1
                else:
                    self.pass_count += 1

                self.test_count += 1

        # Print test summary
        self.log.info(f"Walking Ones Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        return failures

    async def alternating_pattern_test(self) -> list:
        """Test with alternating bit patterns (0101... and 1010...).

        This tests for issues with adjacent bits affecting each other.

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        self.log.info("Starting Alternating Pattern Test")
        failures = []

        # Create alternating patterns
        pattern1 = 0  # Will be 0101...
        pattern2 = 0  # Will be 1010...

        for i in range(self.N):
            if i % 2 == 0:  # Even bit positions
                pattern1 |= (1 << i)
            else:  # Odd bit positions
                pattern2 |= (1 << i)

        # Test combinations of these patterns
        for a, b in itertools.product([pattern1, pattern2], [pattern1, pattern2]):
            # Apply the inputs to DUT
            self.dut.i_multiplier.value = a
            self.dut.i_multiplicand.value = b

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Calculate expected values
            expected_product = (a * b) & (2**(2*self.N) - 1)

            # Read outputs
            ow_product = int(self.dut.ow_product.value)

            # Verify results
            if ow_product != expected_product:
                error_msg_lines = [
                    "Alternating pattern test failed:",
                    f"  Input: multiplier=0b{bin(a)[2:].zfill(self.N)}, multiplicand=0b{bin(b)[2:].zfill(self.N)}",
                ]
                error_msg_lines.append(f"  Expected: product=0b{bin(expected_product)[2:].zfill(2*self.N)}")
                error_msg_lines.append(f"  Actual: product=0b{bin(ow_product)[2:].zfill(2*self.N)}")

                error_str = "\n".join(error_msg_lines)
                self.log.error(error_str)
                failures.append(error_str)
                self.fail_count += 1
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Alternating Pattern Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        return failures

    async def special_patterns_test(self) -> list:
        """Test multiplier with special patterns specific to multiplier architectures.

        Includes tests for booth encoding, carry propagation, etc.

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        self.log.info("Starting Special Patterns Test")
        failures = []

        # Special cases for Booth algorithm
        booth_special = [
            (0x2, 0x2),     # 2*2, simple multiplication
            (0x3, 0x3),     # 3*3, testing +1 -1 sequence
            (0x7, 0x7),     # 7*7, testing multiple +1 patterns
            (0x5, 0x5),     # 5*5, testing +1 0 -1 sequence
            (0xA, 0xA),     # 10*10, testing -1 +1 sequence
            (0x55, 0xAA),   # Alternating 01/10 patterns
            (0x33, 0xCC),   # Alternating 00/11 patterns
        ]

        # Limit patterns to N bits
        booth_special = [(a & self.mask, b & self.mask) for a, b in booth_special]

        # Test each special case
        for a, b in booth_special:
            # Apply the inputs to DUT
            self.dut.i_multiplier.value = a
            self.dut.i_multiplicand.value = b

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Calculate expected values
            expected_product = (a * b) & (2**(2*self.N) - 1)

            # Read outputs
            ow_product = int(self.dut.ow_product.value)

            # Verify results
            if ow_product != expected_product:
                error_msg_lines = [
                    "Special pattern test failed:",
                    f"  Input: multiplier=0x{a:X}, multiplicand=0x{b:X}",
                    f"  Expected: product=0x{expected_product:X}",
                    f"  Actual: product=0x{ow_product:X}",
                    "  Binary comparison:",
                    f"    multiplier   = {bin(a)[2:].zfill(self.N)}",
                ]
                error_msg_lines.append(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
                error_msg_lines.append(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
                error_msg_lines.append(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")

                error_str = "\n".join(error_msg_lines)
                self.log.error(error_str)
                failures.append(error_str)
                self.fail_count += 1
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Special Patterns Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        return failures

    async def simple_test(self) -> list:
        """Run a simple test with the specific case 5*7=35.

        This is the exact case that's failing in our tests, so it's a good starting point.

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        self.log.info("Running simple test (5*7=35)")
        failures = []

        a, b = 5, 7
        self.dut.i_multiplier.value = a
        self.dut.i_multiplicand.value = b

        # Wait for combinational logic to settle
        await self.wait_time(1, 'ns')

        # Read outputs
        ow_product = int(self.dut.ow_product.value)

        # Calculate expected values
        expected_product = (a * b) & (2**(2*self.N) - 1)

        # Verify results
        if ow_product != expected_product:
            error_msg_lines = [
                "Simple test failed:",
                f"  Input: multiplier={a} (0x{a:X}), multiplicand={b} (0x{b:X})",
                f"  Expected: product={expected_product} (0x{expected_product:X})",
                f"  Actual: product={ow_product} (0x{ow_product:X})",
                "  Binary comparison:",
                f"    multiplier   = {bin(a)[2:].zfill(self.N)}",
            ]
            error_msg_lines.append(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
            error_msg_lines.append(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
            error_msg_lines.append(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")

            error_str = "\n".join(error_msg_lines)
            self.log.error(error_str)
            failures.append(error_str)
            self.fail_count += 1
        else:
            self.log.info("Simple test PASSED!")
            self.pass_count += 1

        self.test_count += 1
        return failures

    async def booth_specific_simple_test(self) -> list:
        """Run simpler booth-specific tests focusing on common patterns.

        This runs a subset of the most critical test cases for Booth algorithm.

        Returns:
            list: List of failure messages, empty if all tests passed
        """
        self.log.info("Running simplified Booth test")
        failures = []

        # Test cases that emphasize different Booth patterns
        test_cases = [
            (5, 7),      # Simple positive * positive
            (1, 1),      # Simplest case
            (2, 2),      # Power of 2
            (3, 3),      # Adjacent bits set
            (4, 15),     # Tests +2 encoding
            (1, -1),     # Positive * negative (using 2's complement)
            (-1, -1),    # Negative * negative
        ]

        for a_signed, b_signed in test_cases:
            # Convert signed values to N-bit 2's complement representations
            a = a_signed & self.mask
            b = b_signed & self.mask

            # Apply the inputs to DUT
            self.dut.i_multiplier.value = a
            self.dut.i_multiplicand.value = b

            # Wait for combinational logic to settle
            await self.wait_time(1, 'ns')

            # Read outputs
            ow_product = int(self.dut.ow_product.value)

            # Calculate expected values
            expected_product = (a_signed * b_signed) & (2**(2*self.N) - 1)

            # Verify results
            if ow_product != expected_product:
                error_msg_lines = [
                    "Simple Booth test failed:",
                    f"  Input: multiplier={a} (0x{a:X}), multiplicand={b} (0x{b:X})",
                    f"  Signed values: a_signed={a_signed}, b_signed={b_signed}",
                    f"  Expected: product={expected_product} (0x{expected_product:X})",
                    f"  Actual: product={ow_product} (0x{ow_product:X})",
                    "  Binary comparison:",
                    f"    multiplier   = {bin(a)[2:].zfill(self.N)}",
                ]
                error_msg_lines.append(f"    multiplicand = {bin(b)[2:].zfill(self.N)}")
                error_msg_lines.append(f"    exp_product  = {bin(expected_product)[2:].zfill(2*self.N)}")
                error_msg_lines.append(f"    act_product  = {bin(ow_product)[2:].zfill(2*self.N)}")

                error_str = "\n".join(error_msg_lines)
                self.log.error(error_str)
                failures.append(error_str)
                self.fail_count += 1
            else:
                self.log.info(f"PASS: {a_signed} * {b_signed} = {a_signed * b_signed}")
                self.pass_count += 1

            self.test_count += 1

        self.log.info(f"Simple Booth Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        return failures

    async def clear_interface(self) -> None:
        """Clear the DUT interface by setting all inputs to 0."""
        self.log.debug('Clearing DUT interface')
        with contextlib.suppress(AttributeError):
            self.dut.i_multiplier.value = 0
            self.dut.i_multiplicand.value = 0

    def print_settings(self) -> None:
        """Print the current testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('Multiplier Testbench Settings:')
        self.log.info(f'    DUT:   {self.dut_type}')
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    Mask:  0x{self.mask:X}')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run a comprehensive suite of tests based on test_level.

        Different test levels:
        - simple: Run only the most basic test (5*7=35)
        - basic: Run essential tests including simple cases and Booth-specific tests
        - booth: Run only Booth radix-4 specific test cases
        - medium: Run more extensive tests including various patterns
        - full: Run all tests including edge cases and exhaustive checks
        """
        self.log.info(f"Running comprehensive tests at {self.test_level} level")

        # List to store failure details for later reporting
        failures = []

        # Clear the interface
        await self.clear_interface()

        if self.test_level == 'simple':
            # Run only the simplest test case: 5 * 7 = 35
            failures.extend(await self.simple_test())
        elif self.test_level == 'booth':
            # Run only Booth specific test cases
            failures.extend(await self.booth_specific_simple_test())
            failures.extend(await self.booth_specific_test())
        else:
            # For basic level and above
            failures.extend(await self.simple_test())

            if "booth" in self.dut_type.lower():
                failures.extend(await self.booth_specific_simple_test())
                failures.extend(await self.booth_specific_test())

            # Determine test count based on level
            if self.test_level == 'basic':
                count = min(64, 2**self.N)
            elif self.test_level == 'medium':
                count = min(128, 2**self.N)
            else:  # 'full' or anything else
                count = min(256, 2**self.N)

            # Always run the main loop for standard tests
            failures.extend(await self.main_loop(count))

            # For all levels above basic, include corner cases
            if self.test_level in ['medium', 'full']:
                failures.extend(await self.corner_cases_test())

            # For medium and full test levels, add walking ones test
            if self.test_level in ['medium', 'full']:
                failures.extend(await self.walking_ones_test())

            # For full test level, add alternating pattern and special patterns tests
            if self.test_level == 'full':
                failures.extend(await self.alternating_pattern_test())
                failures.extend(await self.special_patterns_test())

        # Print final test summary
        self.log.info(f"Comprehensive Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")

        # Print summary of failures
        if failures:
            self.log.error("=== FAILURES SUMMARY ===")
            self.log.error(f"Total failures: {len(failures)}")
            if len(failures) > 10:
                self.log.error(f"Showing first 10 failures out of {len(failures)}:")
                for i, failure in enumerate(failures[:10]):
                    self.log.error(f"Failure {i+1}:")
                    for line in failure.split('\n'):
                        self.log.error(f"  {line}")
                self.log.error(f"... and {len(failures) - 10} more failures")
            else:
                for i, failure in enumerate(failures):
                    self.log.error(f"Failure {i+1}:")
                    for line in failure.split('\n'):
                        self.log.error(f"  {line}")
            self.log.error("=== END FAILURES SUMMARY ===")

            # Only assert after all tests have run
            assert self.fail_count == 0, f"Tests failed: {self.fail_count} out of {self.test_count}"
