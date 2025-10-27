# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterJohnsonTB
# Purpose: Johnson Counter Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Johnson Counter Test with Parameterized Test Levels and Configuration

This test uses WIDTH as parameter for maximum flexibility:

CONFIGURATION:
    WIDTH: Counter width in bits (4, 5, 8, 12)

TEST LEVELS (per-test depth):
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~2 min) - smoke test (4-bit, basic)
    FUNC: 4 tests (~8 min) - functional coverage - DEFAULT
    FULL: 12 tests (~2 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 width × 1 level = 1 test
    FUNC: 4 widths × 1 level = 4 tests (all widths, basic only)
    FULL: 4 widths × 3 levels = 12 tests

Environment Variables:
    REG_LEVEL: Control parameter combinations (GATE/FUNC/FULL)
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Counter width in bits

COUNTER_JOHNSON BEHAVIOR:
    Johnson counter (twisted ring counter):
    - Shifts left and feeds inverted MSB to LSB
    - Sequence length: 2 * WIDTH
    - For WIDTH=4: 0000 → 0001 → 0011 → 0111 → 1111 → 1110 → 1100 → 1000 → 0000
    - Creates a "walking ones" then "walking zeros" pattern
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class CounterJohnsonTB(TBBase):
    """Testbench for Johnson Counter module"""

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
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}{self.get_time_ns_str()}")
            self.TEST_LEVEL = 'basic'

        # Calculate sequence properties
        self.SEQUENCE_LENGTH = 2 * self.WIDTH

        # Log configuration
        self.log.info(f"Johnson Counter TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}{self.get_time_ns_str()}")
        self.log.info(f"WIDTH={self.WIDTH}, SEQUENCE_LENGTH={self.SEQUENCE_LENGTH}{self.get_time_ns_str()}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

        # Calculate expected sequence
        self._calculate_expected_sequence()

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.counter_gray = self.dut.counter_gray

    def _calculate_expected_sequence(self):
        """Calculate the expected Johnson counter sequence"""
        self.expected_sequence = []

        # Johnson counter sequence: shift left with inverted feedback
        # Start with all zeros
        current_value = 0

        for i in range(self.SEQUENCE_LENGTH):
            self.expected_sequence.append(current_value)

            # Calculate next value: shift left and feed inverted MSB to LSB
            msb = (current_value >> (self.WIDTH - 1)) & 1
            current_value = ((current_value << 1) | (1 - msb)) & ((1 << self.WIDTH) - 1)

        self.log.info(f"Expected sequence length: {len(self.expected_sequence)}{self.get_time_ns_str()}")
        if self.DEBUG:
            self.log.debug(f"Expected sequence: {[f'0b{x:0{self.WIDTH}b}' for x in self.expected_sequence]}{self.get_time_ns_str()}")

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')
        self.log.debug(f"Clock setup complete{self.get_time_ns_str()}")

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug(f"Starting reset sequence{self.get_time_ns_str()}")
        self.enable.value = 0
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)
        self.log.debug(f"Reset sequence complete{self.get_time_ns_str()}")

    async def check_counter_value(self, expected_value, cycle_num):
        """Check if counter has expected value"""
        actual_value = int(self.counter_gray.value)
        if actual_value != expected_value:
            self.log.error(f"Cycle {cycle_num}: Expected 0b{expected_value:0{self.WIDTH}b} (0x{expected_value:X}), got 0b{actual_value:0{self.WIDTH}b} (0x{actual_value:X}){self.get_time_ns_str()}")
            return False
        else:
            if self.DEBUG or cycle_num % 10 == 0:
                self.log.debug(f"Cycle {cycle_num}: Correct value 0b{actual_value:0{self.WIDTH}b}{self.get_time_ns_str()}")
            return True

    def analyze_johnson_properties(self, sequence):
        """Analyze Johnson counter properties"""
        properties = {
            'correct_length': len(sequence) == self.SEQUENCE_LENGTH,
            'unique_states': len(set(sequence)) == self.SEQUENCE_LENGTH,
            'proper_shifts': True,
            'hamming_distance_1': True
        }

        # Check that each transition is a proper shift with inverted feedback
        for i in range(1, len(sequence)):
            prev_val = sequence[i-1]
            curr_val = sequence[i]

            # Expected: shift left with inverted MSB feedback
            msb = (prev_val >> (self.WIDTH - 1)) & 1
            expected = ((prev_val << 1) | (1 - msb)) & ((1 << self.WIDTH) - 1)

            if curr_val != expected:
                properties['proper_shifts'] = False
                self.log.error(f"Improper shift at position {i}: 0b{prev_val:0{self.WIDTH}b} -> 0b{curr_val:0{self.WIDTH}b}, expected 0b{expected:0{self.WIDTH}b}{self.get_time_ns_str()}")
                break

        # Check Hamming distance between adjacent states is 1
        for i in range(1, len(sequence)):
            hamming_dist = bin(sequence[i-1] ^ sequence[i]).count('1')
            if hamming_dist != 1:
                properties['hamming_distance_1'] = False
                self.log.error(f"Hamming distance != 1 at position {i}: {hamming_dist}{self.get_time_ns_str()}")
                break

        return properties

    async def test_basic_counting(self):
        """Test basic counting functionality"""
        self.log.info(f"Testing basic counting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test based on level
        if self.TEST_LEVEL == 'basic':
            num_cycles = min(self.SEQUENCE_LENGTH, 20)  # Test partial sequence
        elif self.TEST_LEVEL == 'medium':
            num_cycles = self.SEQUENCE_LENGTH * 2  # Test two complete sequences
        else:  # full
            num_cycles = self.SEQUENCE_LENGTH * 3  # Test three complete sequences

        all_passed = True
        self.enable.value = 1
        observed_sequence = []

        for cycle in range(num_cycles):
            await RisingEdge(self.clk)

            expected_value = self.expected_sequence[cycle % self.SEQUENCE_LENGTH]
            observed_sequence.append(int(self.counter_gray.value))

            if not await self.check_counter_value(expected_value, cycle):
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_counting',
                'cycle': cycle,
                'expected_value': expected_value,
                'actual_value': int(self.counter_gray.value),
                'success': int(self.counter_gray.value) == expected_value
            }
            self.test_results.append(result)
            if not result['success']:
                self.test_failures.append(result)

            # Progress reporting
            if cycle % 20 == 0:
                self.mark_progress(f"Basic counting cycle {cycle}")

        # Analyze first complete sequence if we have it
        if len(observed_sequence) >= self.SEQUENCE_LENGTH:
            properties = self.analyze_johnson_properties(observed_sequence[:self.SEQUENCE_LENGTH])
            self.log.info(f"Johnson counter properties: {properties}{self.get_time_ns_str()}")
            if not all(properties.values()):
                all_passed = False

        self.log.info(f"Basic counting test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_enable_disable(self):
        """Test enable/disable functionality"""
        self.log.info(f"Testing enable/disable functionality{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Count a few cycles
        for i in range(min(8, self.SEQUENCE_LENGTH)):
            await RisingEdge(self.clk)
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break

        # Disable and check counter stops - use same pattern as working counter_bin test
        self.enable.value = 0
        await self.wait_time(100)
        stored_value = int(self.counter_gray.value)
        self.log.debug(f"Disabled counter at value 0b{stored_value:0{self.WIDTH}b}{self.get_time_ns_str()}")

        for i in range(10):
            await RisingEdge(self.clk)
            await self.wait_time(100)
            current_value = int(self.counter_gray.value)
            if current_value != stored_value:
                self.log.error(f"Counter changed while disabled: 0b{stored_value:0{self.WIDTH}b} -> 0b{current_value:0{self.WIDTH}b}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Re-enable and check counting resumes - use same pattern as working counter_bin test
        self.enable.value = 1
        await RisingEdge(self.clk)
        self.log.debug(f"Re-enabled counter{self.get_time_ns_str()}")

        # Find where we were in the sequence
        try:
            stored_idx = self.expected_sequence.index(stored_value)
        except ValueError:
            self.log.error(f"Stored value 0b{stored_value:0{self.WIDTH}b} not found in expected sequence{self.get_time_ns_str()}")
            all_passed = False
            stored_idx = 0

        for i in range(min(8, self.SEQUENCE_LENGTH)):
            await RisingEdge(self.clk)
            expected_idx = (stored_idx + 1 + i) % self.SEQUENCE_LENGTH
            expected_value = self.expected_sequence[expected_idx]
            if not await self.check_counter_value(expected_value, stored_idx + 1 + i):
                all_passed = False
                break

        # Store result
        result = {
            'test_type': 'enable_disable',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Enable/disable test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info(f"Testing reset behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Count partway through sequence
        partial_count = min(self.SEQUENCE_LENGTH // 2, 10)

        for i in range(partial_count):
            await RisingEdge(self.clk)
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break

        # Apply reset - use same pattern as working counter_bin test
        self.log.debug(f"Applying reset during counting{self.get_time_ns_str()}")
        await self.wait_time(100)
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await self.wait_time(100)
        self.rst_n.value = 1

        # Check counter is reset to 0
        if int(self.counter_gray.value) != 0:
            self.log.error(f"Counter not reset to 0: got 0b{int(self.counter_gray.value):0{self.WIDTH}b}{self.get_time_ns_str()}")
            all_passed = False

        # Verify counting resumes from 0 - use same pattern as working counter_bin test
        for i in range(min(10, self.SEQUENCE_LENGTH)):
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break
            await RisingEdge(self.clk)
            await self.wait_time(100)

        await self.wait_clocks('clk', 5)

        # Store result
        result = {
            'test_type': 'reset_behavior',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Reset behavior test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_sequence_properties(self):
        """Test Johnson counter sequence properties"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping sequence properties test for basic level{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing sequence properties{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Collect full sequence
        observed_sequence = []

        for cycle in range(self.SEQUENCE_LENGTH):
            await RisingEdge(self.clk)
            observed_sequence.append(int(self.counter_gray.value))

            # Progress reporting
            if cycle % 10 == 0:
                self.mark_progress(f"Sequence collection cycle {cycle}")

        # Analyze properties
        properties = self.analyze_johnson_properties(observed_sequence)

        # Log detailed analysis
        self.log.info(f"Sequence analysis results:{self.get_time_ns_str()}")
        for prop_name, prop_value in properties.items():
            status = "PASS" if prop_value else "FAIL"
            self.log.info(f"  {prop_name}: {status}")

        # The Johnson counter sequence should be exactly what we observed, not a predetermined pattern
        # Since the basic counting test already passed, the observed sequence IS the correct one
        # Let's just verify the mathematical properties, not a specific walking pattern

        all_passed = all(properties.values())

        # Store result
        result = {
            'test_type': 'sequence_properties',
            'properties': properties,
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Sequence properties test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_wrap_behavior(self):
        """Test wrap-around behavior"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping wrap behavior test for {self.TEST_LEVEL} level{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing wrap behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Test multiple complete sequences
        test_cycles = self.SEQUENCE_LENGTH * 2 + 5

        for cycle in range(test_cycles):
            await RisingEdge(self.clk)

            expected_value = self.expected_sequence[cycle % self.SEQUENCE_LENGTH]

            if not await self.check_counter_value(expected_value, cycle):
                all_passed = False
                break

            # Mark important transitions
            if cycle == self.SEQUENCE_LENGTH - 1:
                self.log.info(f"About to wrap from end of sequence{self.get_time_ns_str()}")
            elif cycle == self.SEQUENCE_LENGTH:
                self.log.info(f"Wrapped back to beginning{self.get_time_ns_str()}")
            elif cycle == self.SEQUENCE_LENGTH * 2 - 1:
                self.log.info(f"About to complete second sequence{self.get_time_ns_str()}")
            elif cycle == self.SEQUENCE_LENGTH * 2:
                self.log.info(f"Started third sequence{self.get_time_ns_str()}")

            # Progress reporting
            if cycle % 20 == 0:
                self.mark_progress(f"Wrap test cycle {cycle}")

        # Store result
        result = {
            'test_type': 'wrap_behavior',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Wrap behavior test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def test_edge_cases(self):
        """Test edge cases and boundary conditions"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping edge case tests for {self.TEST_LEVEL} level{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing edge cases{self.get_time_ns_str()}")

        await self.setup_clock()

        all_passed = True

        # Test multiple rapid resets
        for reset_test in range(3):
            self.log.debug(f"Rapid reset test {reset_test + 1}{self.get_time_ns_str()}")
            await self.reset_dut()
            self.enable.value = 1

            # Count a few cycles
            for i in range(min(8, self.SEQUENCE_LENGTH)):
                await RisingEdge(self.clk)
                expected_value = self.expected_sequence[i]
                if not await self.check_counter_value(expected_value, i):
                    self.log.error(f"Rapid reset test {reset_test + 1} failed{self.get_time_ns_str()}")
                    all_passed = False
                    break

            if not all_passed:
                break

        # Test reset at sequence boundary
        if all_passed:
            self.log.debug(f"Testing reset at sequence boundary{self.get_time_ns_str()}")
            await self.reset_dut()
            self.enable.value = 1

            # Count to just before wrap
            for i in range(self.SEQUENCE_LENGTH - 1):
                await RisingEdge(self.clk)

            # Reset during the cycle that should wrap
            self.rst_n.value = 0
            await RisingEdge(self.clk)
            self.rst_n.value = 1
            await RisingEdge(self.clk)

            # Should be back at 0
            if int(self.counter_gray.value) != 0:
                self.log.error(f"Reset at sequence boundary failed: expected 0, got 0b{int(self.counter_gray.value):0{self.WIDTH}b}{self.get_time_ns_str()}")
                all_passed = False

        # Test enable transitions at various points in sequence
        if all_passed:
            self.log.debug(f"Testing enable transitions{self.get_time_ns_str()}")
            await self.reset_dut()
            self.enable.value = 1

            # Test enable/disable at different points
            test_points = [self.WIDTH // 2, self.WIDTH, self.WIDTH + self.WIDTH // 2]

            for test_point in test_points:
                if test_point >= self.SEQUENCE_LENGTH:
                    continue

                # Count to test point
                for i in range(test_point):
                    await RisingEdge(self.clk)

                # Toggle enable a few times
                for toggle in range(3):
                    self.enable.value = 0
                    await self.wait_time(100)
                    await RisingEdge(self.clk)
                    stored_value = int(self.counter_gray.value)

                    # Wait a few cycles
                    for j in range(3):
                        await RisingEdge(self.clk)
                        await self.wait_time(100)
                        if int(self.counter_gray.value) != stored_value:
                            self.log.error(f"Value changed during disable at test point {test_point}{self.get_time_ns_str()}")
                            all_passed = False
                            break
                        else:
                            self.log.debug(f"Value unchanged ({stored_value=}) during disable at test point {test_point}{self.get_time_ns_str()}")    

                    if not all_passed:
                        break

                    # Re-enable
                    self.enable.value = 1

                if not all_passed:
                    break

            await self.wait_clocks('clk', 5)

        # Store result
        result = {
            'test_type': 'edge_cases',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Edge cases test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running JOHNSON COUNTER tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_counting, "Basic counting"),
            (self.test_enable_disable, "Enable/disable"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_sequence_properties, "Sequence properties"),
            (self.test_wrap_behavior, "Wrap behavior"),
            (self.test_edge_cases, "Edge cases")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}{self.get_time_ns_str()}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED{self.get_time_ns_str()}")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED{self.get_time_ns_str()}")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}{self.get_time_ns_str()}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info(f"TEST RESULTS SUMMARY{self.get_time_ns_str()}")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall JOHNSON COUNTER result: {overall_status}{self.get_time_ns_str()}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}{self.get_time_ns_str()}")
        self.log.info("="*60)

        return all_passed


@cocotb.test(timeout_time=30000, timeout_unit="us")
async def counter_johnson_test(dut):
    """Test for Johnson Counter module"""
    tb = CounterJohnsonTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"JOHNSON COUNTER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Johnson counter test FAILED - {len(tb.test_failures)} failures detected{tb.get_time_ns_str()}"

    return passed


def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (4-bit, basic level)
    REG_LEVEL=FUNC: 4 tests (all widths, basic level) - default
    REG_LEVEL=FULL: 12 tests (all widths, all test levels)

    Returns:
        List of tuples: (width, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    widths = [4, 5, 8, 12]  # Different counter widths
    test_levels = ['basic', 'medium', 'full']  # Test levels

    if reg_level == 'GATE':
        # Quick smoke test: 4-bit, basic only
        params = [(4, 'basic')]

    elif reg_level == 'FUNC':
        # Functional coverage: all widths, basic level only
        params = [(width, 'basic') for width in widths]

    else:  # FULL
        # Comprehensive: all combinations
        params = []
        for width, test_level in product(widths, test_levels):
            params.append((width, test_level))

    return params


params = generate_params()


@pytest.mark.parametrize("width, test_level", params)
def test_counter_johnson(request, width, test_level):
    """
    Parameterized Johnson Counter test with configurable width and test level.

    Test level controls the depth and breadth of testing:
    - basic: Quick verification (1-2 min)
    - medium: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)

    Counter behavior: Johnson counter (twisted ring) with sequence length 2*WIDTH
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "counter_johnson"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_johnson.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    test_name_plus_params = f"test_counter_johnson_w{width}_{test_level}"
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
    width_factor = max(1.0, width / 8.0)  # Larger widths take more time
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
        'TEST_DEBUG': '1',
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
    print(f"Sequence length: {2 * width}")
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
            includes=includes,  # From filelist via get_sources_from_filelist()
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
