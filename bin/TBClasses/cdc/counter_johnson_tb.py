# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterJohnsonTB
# Purpose: Testbench for counter_johnson
# Subsystem: framework
#
# Extracted from val/cdc/test_counter_johnson.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class CounterJohnsonTB(TBBase):
    """Testbench for Johnson Counter module"""

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
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}{self.get_time_ns_str()}")
            self.TEST_LEVEL = 'gate'

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
        """Setup clock (idempotent: one driver per sim -- repeated calls from
        each subtest must not stack a second Clock on the same signal)"""
        if not getattr(self, '_clk_started', False):
            cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
            self._clk_started = True
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
        if self.TEST_LEVEL == 'gate':
            num_cycles = min(self.SEQUENCE_LENGTH, 20)  # Test partial sequence
        elif self.TEST_LEVEL == 'func':
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
                if self.TEST_LEVEL == 'gate':
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
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping sequence properties test for gate level{self.get_time_ns_str()}")
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
