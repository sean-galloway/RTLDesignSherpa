# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterBinTB
# Purpose: Testbench for counter_bin
# Subsystem: framework
#
# Extracted from val/common/test_counter_bin.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class CounterBinTB(TBBase):
    """Testbench for Binary Counter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '5'))
        self.MAX = self.convert_to_int(os.environ.get('TEST_MAX', '10'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}{self.get_time_ns_str()}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"Counter Bin TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}{self.get_time_ns_str()}")
        self.log.info(f"WIDTH={self.WIDTH}, MAX={self.MAX}{self.get_time_ns_str()}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

        # Calculate expected sequence
        self._calculate_expected_sequence()

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.reset_dut()

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.counter_bin = self.dut.counter_bin_curr  # Updated to match new RTL port name
        self.counter_bin_next = self.dut.counter_bin_next

    def _calculate_expected_sequence(self):
        """Calculate the expected counting sequence"""
        self.expected_sequence = []

        # First sequence: 0 to MAX-1
        for i in range(self.MAX):
            self.expected_sequence.append(i)

        # Second sequence: toggle MSB and count 0 to MAX-1 again
        msb_mask = 1 << (self.WIDTH - 1)
        for i in range(self.MAX):
            self.expected_sequence.append(i | msb_mask)

        self.log.info(f"Expected sequence length: {len(self.expected_sequence)}{self.get_time_ns_str()}")
        if self.DEBUG:
            self.log.debug(f"Expected sequence: {[hex(x) for x in self.expected_sequence[:20]]}{self.get_time_ns_str()}")

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
        # Wait a bit more for reset to properly settle
        await Timer(100, units='ps')
        self.log.debug(f"Reset sequence complete{self.get_time_ns_str()}")

    async def check_counter_value(self, expected_value, cycle_num):
        """Check if counter has expected value"""
        actual_value = int(self.counter_bin.value)
        if actual_value != expected_value:
            self.log.error(f"Cycle {cycle_num}: Expected 0x{expected_value:X}, got 0x{actual_value:X}{self.get_time_ns_str()}")
            return False
        else:
            if self.DEBUG or cycle_num % 10 == 0:
                self.log.debug(f"Cycle {cycle_num}: Correct value 0x{actual_value:X}{self.get_time_ns_str()}")
            return True

    async def test_basic_counting(self):
        """Test basic counting functionality"""
        self.log.info(f"Testing basic counting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test based on level
        if self.TEST_LEVEL == 'gate':
            num_cycles = min(20, len(self.expected_sequence))  # Test first 20 cycles
        elif self.TEST_LEVEL == 'func':
            num_cycles = min(len(self.expected_sequence), 100)  # Test up to full sequence
        else:  # full
            num_cycles = len(self.expected_sequence) * 2  # Test two complete sequences

        all_passed = True
        self.enable.value = 1

        for cycle in range(num_cycles):
            await RisingEdge(self.clk)

            expected_value = self.expected_sequence[cycle % len(self.expected_sequence)]

            if not await self.check_counter_value(expected_value, cycle):
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'basic_counting',
                'cycle': cycle,
                'expected_value': expected_value,
                'actual_value': int(self.counter_bin.value),
                'success': int(self.counter_bin.value) == expected_value
            }
            self.test_results.append(result)
            if not result['success']:
                self.test_failures.append(result)

            # Progress reporting
            if cycle % 50 == 0:
                self.mark_progress(f"Basic counting cycle {cycle}")

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
        for i in range(5):
            await RisingEdge(self.clk)
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break

        # Disable and check counter stops
        self.enable.value = 0
        await self.wait_time(100)
        stored_value = int(self.counter_bin.value)
        self.log.debug(f"Disabled counter at value 0x{stored_value:X}{self.get_time_ns_str()}")

        for i in range(10):
            await RisingEdge(self.clk)
            await self.wait_time(100)
            current_value = int(self.counter_bin.value)
            if current_value != stored_value:
                self.log.error(f"Counter changed while disabled: 0x{stored_value:X} -> 0x{current_value:X}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Re-enable and check counting resumes
        self.enable.value = 1
        await RisingEdge(self.clk)
        self.log.debug(f"Re-enabled counter{self.get_time_ns_str()}")
        self.log.debug(f'{self.expected_sequence=}')
        self.log.debug(f'{stored_value=}')

        for i in range(5):
            await RisingEdge(self.clk)  
            expected_idx = (stored_value + 1 + i) % len(self.expected_sequence)
            expected_value = self.expected_sequence[expected_idx]
            if not await self.check_counter_value(expected_value, stored_value + 1 + i):
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
        partial_count = min(self.MAX // 2, 10)

        for i in range(partial_count):
            await RisingEdge(self.clk)
            expected_value = self.expected_sequence[i]
            if not await self.check_counter_value(expected_value, i):
                all_passed = False
                break

        # Apply reset
        self.log.debug(f"Applying reset during counting{self.get_time_ns_str()}")
        await self.wait_time(100)
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await self.wait_time(100)
        self.rst_n.value = 1
        # await RisingEdge(self.clk)
        # await self.wait_time(400)

        # Check counter is reset to 0
        if int(self.counter_bin.value) != 0:
            self.log.error(f"Counter not reset to 0: got 0x{int(self.counter_bin.value):X}{self.get_time_ns_str()}")
            all_passed = False

        # Verify counting resumes from 0
        for i in range(min(10, len(self.expected_sequence))):
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

    async def test_wrap_behavior(self):
        """Test wrap-around behavior"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping wrap behavior test for gate level{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing wrap behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Test full sequence including wrap
        test_cycles = len(self.expected_sequence) + 5  # A bit beyond full cycle

        for cycle in range(test_cycles):
            await RisingEdge(self.clk)

            expected_value = self.expected_sequence[cycle % len(self.expected_sequence)]

            if not await self.check_counter_value(expected_value, cycle):
                all_passed = False
                if cycle < self.MAX * 2:  # Only break early in first two sequences
                    break

            # Mark important transitions
            if cycle == self.MAX - 1:
                self.log.info(f"About to wrap from first sequence{self.get_time_ns_str()}")
            elif cycle == self.MAX:
                self.log.info(f"Wrapped to second sequence{self.get_time_ns_str()}")
            elif cycle == len(self.expected_sequence) - 1:
                self.log.info(f"About to wrap to beginning{self.get_time_ns_str()}")
            elif cycle == len(self.expected_sequence):
                self.log.info(f"Wrapped back to beginning{self.get_time_ns_str()}")

            # Progress reporting
            if cycle % 25 == 0:
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
            for i in range(min(5, self.MAX)):
                await RisingEdge(self.clk)
                expected_value = self.expected_sequence[i]
                if not await self.check_counter_value(expected_value, i):
                    self.log.error(f"Rapid reset test {reset_test + 1} failed{self.get_time_ns_str()}")
                    all_passed = False
                    break

            if not all_passed:
                break

        # Test reset at wrap boundary
        if all_passed:
            self.log.debug(f"Testing reset at wrap boundary{self.get_time_ns_str()}")
            await self.reset_dut()
            self.enable.value = 1

            # Count to just before wrap
            for i in range(self.MAX - 1):
                await RisingEdge(self.clk)

            # Reset during the cycle that should wrap
            self.rst_n.value = 0
            await RisingEdge(self.clk)
            self.rst_n.value = 1
            await RisingEdge(self.clk)

            # Should be back at 0
            if int(self.counter_bin.value) != 0:
                self.log.error(f"Reset at wrap failed: expected 0, got 0x{int(self.counter_bin.value):X}{self.get_time_ns_str()}")
                all_passed = False

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
        self.log.info(f"Running COUNTER_BIN tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_counting, "Basic counting"),
            (self.test_enable_disable, "Enable/disable"),
            (self.test_reset_behavior, "Reset behavior"),
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
        self.log.info(f"Overall COUNTER_BIN result: {overall_status}{self.get_time_ns_str()}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}{self.get_time_ns_str()}")
        self.log.info("="*60)

        return all_passed
