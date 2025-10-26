# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DividerTB
# Purpose: Divider Testing Module
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Divider Testing Module

This module provides a robust testbench for various divider implementations.
It contains a base class that can be extended for different divider architectures.
"""
import os
import random
import contextlib
import itertools
from typing import List, Tuple, Dict, Any, Optional, Union

import cocotb
from cocotb.triggers import Timer, RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
from cocotb.utils import get_sim_time
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class DividerTB(TBBase):
    """Base Testbench for various divider implementations

    This class provides common functionality for testing various
    divider architectures and configurations.
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '16'))
        self.max_val = 2**self.DATA_WIDTH
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize the random generator
        random.seed(self.seed)

        # Track test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.dbz_count = 0

        # Get DUT type
        self.dut_type = os.environ.get('DUT', 'unknown')
        self.log.info(f"Testing {self.dut_type} with DATA_WIDTH={self.DATA_WIDTH}")

    async def start_clock(self, clock_period=10, units='ns'):
        """Start the clock for the DUT.

        Args:
            clock_period: Period of the clock in time units
            units: Time units for the clock period
        """
        self.log.info(f"Starting clock with period {clock_period} {units}")
        clock = Clock(self.dut.i_clk, clock_period, units)
        self.clock_thread = await cocotb.start(clock.start())

    async def reset_dut(self, reset_duration=10, units='ns'):
        """Reset the DUT.

        Args:
            reset_duration: Duration of the reset in time units
            units: Time units for the reset duration
        """
        self.log.info(f"Resetting DUT for {reset_duration} {units}")
        self.dut.i_rst_b.value = 0
        await self.wait_time(reset_duration, units)
        self.dut.i_rst_b.value = 1
        await self.wait_time(reset_duration, units)
        self.log.info("Reset complete")

    async def wait_for_completion(self, timeout=1000, units='ns'):
        """Wait for the division operation to complete.

        Args:
            timeout: Maximum time to wait for completion
            units: Time units for the timeout

        Returns:
            Tuple of (success, o_quotient, o_remainder, o_dbz)
        """
        start_time = get_sim_time('ns')
        timeout_ns = timeout + start_time

        while get_sim_time('ns') - start_time < timeout_ns:
            if int(self.dut.o_done.value):
                is_valid = int(self.dut.o_valid.value)
                quotient = int(self.dut.o_quotient.value)
                remainder = int(self.dut.o_remainder.value)
                dbz = int(self.dut.o_dbz.value)

                return (is_valid, quotient, remainder, dbz)

            await RisingEdge(self.dut.i_clk)

        self.log.error(f"Timeout waiting for division to complete after {timeout} {units}")
        return (False, 0, 0, False)

    async def perform_division(self, dividend, divisor):
        """Perform a single division operation.

        Args:
            dividend: Dividend value
            divisor: Divisor value

        Returns:
            Tuple of (success, quotient, remainder, dbz)
        """
        self.log.debug(f"Performing division: {dividend} / {divisor}")

        # Apply inputs
        self.dut.i_dividend.value = dividend
        self.dut.i_divisor.value = divisor

        # Start operation
        self.dut.i_start.value = 1
        await RisingEdge(self.dut.i_clk)
        self.dut.i_start.value = 0

        # Wait for completion
        max_cycles = self.DATA_WIDTH + 10  # Should be enough for any divider
        return await self.wait_for_completion(timeout=max_cycles, units='cycles')

    async def main_loop(self, count: int = 100) -> None:
        """Main test loop for dividers.

        Tests a range of input values and edge cases.

        Args:
            count: Number of random test vectors to generate
        """
        self.log.info("Starting Main Divider Test")

        # Define test vectors for thorough testing
        test_vectors = []

        # Add edge cases and special values
        edge_cases = [
            (0, 1),                # Zero dividend
            (1, 1),                # Identity
            (self.mask, 1),        # Max dividend, divisor 1
            (self.mask, self.mask) # Max dividend, max divisor
        ]
        test_vectors.extend(edge_cases)

        # Add divide by zero cases
        dbz_cases = [(random.randint(1, self.mask), 0) for _ in range(5)]
        test_vectors.extend(dbz_cases)

        # Add random values
        if count <= 100:
            # For small counts, add a full distribution of values
            random_cases = [
                (random.randint(0, self.mask), random.randint(1, self.mask))
                for _ in range(count - len(test_vectors))
            ]
        else:
            # For larger counts, stratify the random values
            small_range = self.max_val // 4
            mid_range = self.max_val // 2
            large_range = 3 * self.max_val // 4

            random_cases = []
            ranges = [
                (0, small_range),
                (small_range, mid_range),
                (mid_range, large_range),
                (large_range, self.mask)
            ]

            remaining = count - len(test_vectors)
            per_range = remaining // 4

            for low, high in ranges:
                for _ in range(per_range):
                    dividend = random.randint(low, high)
                    divisor = random.randint(1, self.mask)
                    random_cases.append((dividend, divisor))

            # Add any remaining cases
            remaining = count - len(test_vectors) - len(random_cases)
            for _ in range(remaining):
                dividend = random.randint(0, self.mask)
                divisor = random.randint(1, self.mask)
                random_cases.append((dividend, divisor))

        test_vectors.extend(random_cases)

        # Shuffle to avoid patterns
        random.shuffle(test_vectors)

        # Run tests
        total_tests = len(test_vectors)
        self.log.info(f"Will run {total_tests} total test cases")

        for test_idx, (dividend, divisor) in enumerate(test_vectors):
            # Log progress periodically
            if test_idx % max(1, total_tests // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{total_tests} tests completed")

            msg = f'Testing {dividend=} {divisor=}'
            self.log.debug(msg)

            # Perform the division
            valid, quotient, remainder, dbz = await self.perform_division(dividend, divisor)

            # Verify results
            if divisor == 0:
                # Should detect divide by zero
                expected_valid = False
                expected_dbz = True
                expected_quotient = 0  # Don't care
                expected_remainder = 0  # Don't care
            else:
                expected_valid = True
                expected_dbz = False
                expected_quotient = dividend // divisor
                expected_remainder = dividend % divisor

            if dbz and divisor == 0:
                self.log.debug(f"Divide by zero detected as expected")
                self.dbz_count += 1
                self.pass_count += 1
            elif not valid and divisor == 0:
                self.log.debug(f"Division invalid as expected for divide by zero")
                self.dbz_count += 1
                self.pass_count += 1
            elif valid and divisor != 0:
                # For valid results, check correctness
                if quotient == expected_quotient and remainder == expected_remainder:
                    self.log.debug(f"Division correct: {dividend} / {divisor} = {quotient} remainder {remainder}")
                    self.pass_count += 1
                else:
                    self.log.error(f"Division incorrect at {test_idx+1}/{total_tests}:")
                    self.log.error(f"  Input: dividend={dividend}, divisor={divisor}")
                    self.log.error(f"  Expected: quotient={expected_quotient}, remainder={expected_remainder}")
                    self.log.error(f"  Actual: quotient={quotient}, remainder={remainder}")
                    self.fail_count += 1
                    assert False, f"Division test failed: Input: dividend={dividend}, divisor={divisor}, Expected: quotient={expected_quotient}, remainder={expected_remainder}, Got: quotient={quotient}, remainder={remainder}"
            else:
                self.log.error(f"Unexpected results at {test_idx+1}/{total_tests}:")
                self.log.error(f"  Input: dividend={dividend}, divisor={divisor}")
                self.log.error(f"  Expected: valid={expected_valid}, dbz={expected_dbz}, quotient={expected_quotient}, remainder={expected_remainder}")
                self.log.error(f"  Actual: valid={valid}, dbz={dbz}, quotient={quotient}, remainder={remainder}")
                self.fail_count += 1
                assert False, f"Division test failed with unexpected results: Input: dividend={dividend}, divisor={divisor}"

            self.test_count += 1

        # Print test summary
        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed, {self.dbz_count} divide-by-zero detected")

    async def latency_test(self, count: int = 20) -> None:
        """Test the latency of the divider.

        Measures how many clock cycles are required for different inputs.

        Args:
            count: Number of test vectors to generate
        """
        self.log.info("Starting Divider Latency Test")

        # Generate test vectors (avoid divide by zero)
        test_vectors = []

        # Add small, medium and large values
        ranges = [
            (1, 10),
            (100, 1000),
            (self.mask // 2, self.mask)
        ]

        per_range = count // 3
        for low, high in ranges:
            for _ in range(per_range):
                dividend = random.randint(low, high)
                divisor = random.randint(1, high)
                test_vectors.append((dividend, divisor))

        # Add any remaining tests
        remaining = count - len(test_vectors)
        for _ in range(remaining):
            dividend = random.randint(1, self.mask)
            divisor = random.randint(1, self.mask)
            test_vectors.append((dividend, divisor))

        # Run tests
        latencies = []

        for dividend, divisor in test_vectors:
            self.log.debug(f"Testing latency for {dividend} / {divisor}")

            # Apply inputs
            self.dut.i_dividend.value = dividend
            self.dut.i_divisor.value = divisor

            # Start operation and measure time
            await RisingEdge(self.dut.i_clk)
            start_time = get_sim_time('ns')

            self.dut.i_start.value = 1
            await RisingEdge(self.dut.i_clk)
            self.dut.i_start.value = 0

            # Wait for completion
            while not int(self.dut.o_done.value):
                await RisingEdge(self.dut.i_clk)

            end_time = get_sim_time('ns')

            # Calculate latency in clock cycles
            latency_ns = end_time - start_time
            clock_period = 10  # Assuming 10ns clock
            latency_cycles = latency_ns / clock_period

            self.log.debug(f"Latency for {dividend} / {divisor}: {latency_cycles:.1f} cycles")
            latencies.append(latency_cycles)

        # Analyze results
        avg_latency = sum(latencies) / len(latencies)
        min_latency = min(latencies)
        max_latency = max(latencies)

        self.log.info(f"Latency Analysis:")
        self.log.info(f"  Average: {avg_latency:.2f} cycles")
        self.log.info(f"  Minimum: {min_latency:.2f} cycles")
        self.log.info(f"  Maximum: {max_latency:.2f} cycles")

    async def back_to_back_test(self, count: int = 10) -> None:
        """Test back-to-back division operations.

        This tests how the divider handles consecutive operations
        without delay between them.

        Args:
            count: Number of consecutive operations to test
        """
        self.log.info("Starting Back-to-Back Divider Test")

        # Generate random dividend/divisor pairs (avoid divide by zero)
        test_vectors = [
            (random.randint(1, self.mask), random.randint(1, self.mask))
            for _ in range(count)
        ]

        # Run operations back-to-back
        for i, (dividend, divisor) in enumerate(test_vectors):
            self.log.debug(f"Back-to-back test {i+1}/{count}: {dividend} / {divisor}")

            # Apply inputs
            self.dut.i_dividend.value = dividend
            self.dut.i_divisor.value = divisor

            # Start operation immediately
            self.dut.i_start.value = 1
            await RisingEdge(self.dut.i_clk)
            self.dut.i_start.value = 0

            # Wait for busy to assert before checking
            await RisingEdge(self.dut.o_busy)

            # Calculate expected results
            expected_quotient = dividend // divisor
            expected_remainder = dividend % divisor

            # Wait for completion
            while not int(self.dut.o_done.value):
                await RisingEdge(self.dut.i_clk)

            # Verify results
            valid = int(self.dut.o_valid.value)
            quotient = int(self.dut.o_quotient.value)
            remainder = int(self.dut.o_remainder.value)

            if valid and quotient == expected_quotient and remainder == expected_remainder:
                self.log.debug(f"Back-to-back test {i+1} passed")
                self.pass_count += 1
            else:
                self.log.error(f"Back-to-back test {i+1} failed:")
                self.log.error(f"  Input: dividend={dividend}, divisor={divisor}")
                self.log.error(f"  Expected: quotient={expected_quotient}, remainder={expected_remainder}")
                self.log.error(f"  Actual: valid={valid}, quotient={quotient}, remainder={remainder}")
                self.fail_count += 1
                assert False, f"Back-to-back test failed: Input: dividend={dividend}, divisor={divisor}, Expected: quotient={expected_quotient}, remainder={expected_remainder}, Got: quotient={quotient}, remainder={remainder}"

            self.test_count += 1

            # Do not add delay - start next operation immediately

        self.log.info(f"Back-to-back test complete: {self.pass_count}/{self.test_count} passed")

    async def clear_interface(self) -> None:
        """Clear the DUT interface by setting all inputs to 0."""
        self.log.debug('Clearing DUT interface')
        with contextlib.suppress(AttributeError):
            self.dut.i_start.value = 0
            self.dut.i_dividend.value = 0
            self.dut.i_divisor.value = 0

    def print_settings(self) -> None:
        """Print the current testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('Divider Testbench Settings:')
        self.log.info(f'    DUT:          {self.dut_type}')
        self.log.info(f'    DATA_WIDTH:   {self.DATA_WIDTH}')
        self.log.info(f'    Mask:         0x{self.mask:X}')
        self.log.info(f'    Seed:         {self.seed}')
        self.log.info(f'    Level:        {self.test_level}')
        self.log.info('-------------------------------------------')

    async def run_comprehensive_tests(self) -> None:
        """Run a comprehensive suite of tests based on test_level.

        This combines multiple test patterns to thoroughly test the divider.
        """
        self.log.info(f"Running comprehensive tests at {self.test_level} level")

        # Clear the interface
        await self.clear_interface()

        # Start with basic tests
        await self.wait_time(1, 'ns')

        # Determine test count based on level
        if self.test_level == 'basic':
            main_count = 50
            latency_count = 10
            b2b_count = 5
        elif self.test_level == 'medium':
            main_count = 100
            latency_count = 20
            b2b_count = 10
        else:  # 'full' or anything else
            main_count = 200
            latency_count = 30
            b2b_count = 20

        # Start clock and reset DUT
        await self.start_clock()
        await self.reset_dut()

        # Always run the main loop for standard tests
        await self.main_loop(main_count)

        # For medium and full test levels, add latency test
        if self.test_level in ['medium', 'full']:
            await self.reset_dut()
            await self.latency_test(latency_count)

        # For full test level, add back-to-back test
        if self.test_level == 'full':
            await self.reset_dut()
            await self.back_to_back_test(b2b_count)

        # Stop clock
        self.clock_thread.kill()

        # Print final test summary
        self.log.info(f"Comprehensive Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
