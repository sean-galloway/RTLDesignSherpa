# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterBinGrayTB
# Purpose: Testbench for counter_bingray
# Subsystem: framework
#
# Extracted from val/cdc/test_counter_bingray.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class CounterBinGrayTB(TBBase):
    """Testbench for Binary-Gray Counter module"""

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

        # Calculate max value
        self.MAX_VALUE = (1 << self.WIDTH) - 1

        # Log configuration
        self.log.info(f"Counter BinGray TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}{self.get_time_ns_str()}")
        self.log.info(f"WIDTH={self.WIDTH}, MAX_VALUE={self.MAX_VALUE}{self.get_time_ns_str()}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

        # Calculate expected sequences
        self._calculate_expected_sequences()

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.counter_bin = self.dut.counter_bin
        self.counter_bin_next = self.dut.counter_bin_next
        self.counter_gray = self.dut.counter_gray

    def _binary_to_gray(self, binary_val):
        """Convert binary value to Gray code"""
        return binary_val ^ (binary_val >> 1)

    def _calculate_expected_sequences(self):
        """Calculate the expected binary and Gray sequences"""
        self.expected_bin_sequence = []
        self.expected_gray_sequence = []
        
        for i in range(1 << self.WIDTH):  # 2^WIDTH values
            self.expected_bin_sequence.append(i)
            self.expected_gray_sequence.append(self._binary_to_gray(i))
        
        self.log.info(f"Expected sequence length: {len(self.expected_bin_sequence)}{self.get_time_ns_str()}")
        if self.DEBUG:
            self.log.debug(f"First 16 binary values: {[hex(x) for x in self.expected_bin_sequence[:16]]}{self.get_time_ns_str()}")
            self.log.debug(f"First 16 Gray values: {[hex(x) for x in self.expected_gray_sequence[:16]]}{self.get_time_ns_str()}")

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

    async def check_counter_values(self, expected_bin, expected_gray, cycle_num):
        """Check if counters have expected values"""
        actual_bin = int(self.counter_bin.value)
        actual_gray = int(self.counter_gray.value)
        
        bin_ok = actual_bin == expected_bin
        gray_ok = actual_gray == expected_gray
        
        if not bin_ok:
            self.log.error(f"Cycle {cycle_num}: Binary counter expected 0x{expected_bin:X}, got 0x{actual_bin:X}{self.get_time_ns_str()}")
        
        if not gray_ok:
            self.log.error(f"Cycle {cycle_num}: Gray counter expected 0x{expected_gray:X}, got 0x{actual_gray:X}{self.get_time_ns_str()}")
        
        if bin_ok and gray_ok:
            if self.DEBUG or cycle_num % 20 == 0:
                self.log.debug(f"Cycle {cycle_num}: Correct values - Bin: 0x{actual_bin:X}, Gray: 0x{actual_gray:X}{self.get_time_ns_str()}")
        
        return bin_ok and gray_ok

    async def check_next_value(self, expected_next_bin, cycle_num):
        """Check if counter_bin_next has expected value"""
        actual_next = int(self.counter_bin_next.value)
        
        if actual_next != expected_next_bin:
            self.log.error(f"Cycle {cycle_num}: Next binary expected 0x{expected_next_bin:X}, got 0x{actual_next:X}{self.get_time_ns_str()}")
            return False
        else:
            if self.DEBUG or cycle_num % 20 == 0:
                self.log.debug(f"Cycle {cycle_num}: Correct next value 0x{actual_next:X}{self.get_time_ns_str()}")
            return True

    async def test_basic_counting(self):
        """Test basic counting functionality"""
        self.log.info(f"Testing basic counting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test based on level
        if self.TEST_LEVEL == 'gate':
            num_cycles = min(32, len(self.expected_bin_sequence))  # Test first 32 cycles
        elif self.TEST_LEVEL == 'func':
            num_cycles = min(len(self.expected_bin_sequence), 200)  # Test up to full sequence
        else:  # full
            num_cycles = len(self.expected_bin_sequence) * 2  # Test two complete sequences

        all_passed = True
        self.enable.value = 1

        for cycle in range(num_cycles):
            await RisingEdge(self.clk)
            
            expected_bin = self.expected_bin_sequence[cycle % len(self.expected_bin_sequence)]
            expected_gray = self.expected_gray_sequence[cycle % len(self.expected_gray_sequence)]
            
            if not await self.check_counter_values(expected_bin, expected_gray, cycle):
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Check next value (when enabled)
            next_cycle = (cycle + 1) % len(self.expected_bin_sequence)
            expected_next_bin = self.expected_bin_sequence[next_cycle]
            if not await self.check_next_value(expected_next_bin, cycle):
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'basic_counting',
                'cycle': cycle,
                'expected_bin': expected_bin,
                'expected_gray': expected_gray,
                'actual_bin': int(self.counter_bin.value),
                'actual_gray': int(self.counter_gray.value),
                'success': (int(self.counter_bin.value) == expected_bin and 
                           int(self.counter_gray.value) == expected_gray)
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
        for i in range(8):
            await RisingEdge(self.clk)
            expected_bin = self.expected_bin_sequence[i]
            expected_gray = self.expected_gray_sequence[i]
            if not await self.check_counter_values(expected_bin, expected_gray, i):
                all_passed = False
                break

        # Disable and check counters stop
        self.enable.value = 0
        await self.wait_time(100)
        stored_bin = int(self.counter_bin.value)
        stored_gray = int(self.counter_gray.value)
        self.log.debug(f"Disabled counters at Bin: 0x{stored_bin:X}, Gray: 0x{stored_gray:X}{self.get_time_ns_str()}")

        for i in range(10):
            await RisingEdge(self.clk)
            await self.wait_time(100)
            current_bin = int(self.counter_bin.value)
            current_gray = int(self.counter_gray.value)
            current_next = int(self.counter_bin_next.value)
            
            if current_bin != stored_bin:
                self.log.error(f"Binary counter changed while disabled: 0x{stored_bin:X} -> 0x{current_bin:X}{self.get_time_ns_str()}")
                all_passed = False
                break
                
            if current_gray != stored_gray:
                self.log.error(f"Gray counter changed while disabled: 0x{stored_gray:X} -> 0x{current_gray:X}{self.get_time_ns_str()}")
                all_passed = False
                break
                
            # Next value should equal current when disabled
            if current_next != stored_bin:
                self.log.error(f"Next value wrong when disabled: expected 0x{stored_bin:X}, got 0x{current_next:X}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Re-enable and check counting resumes
        self.enable.value = 1
        await RisingEdge(self.clk)
        self.log.debug(f"Re-enabled counters{self.get_time_ns_str()}")
        
        for i in range(8):
            await RisingEdge(self.clk)
            expected_idx = (stored_bin + 1 + i) % len(self.expected_bin_sequence)
            expected_bin = self.expected_bin_sequence[expected_idx]
            expected_gray = self.expected_gray_sequence[expected_idx]
            if not await self.check_counter_values(expected_bin, expected_gray, stored_bin + 1 + i):
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
        partial_count = min(16, len(self.expected_bin_sequence) // 4)
        
        for i in range(partial_count):
            await RisingEdge(self.clk)
            expected_bin = self.expected_bin_sequence[i]
            expected_gray = self.expected_gray_sequence[i]
            if not await self.check_counter_values(expected_bin, expected_gray, i):
                all_passed = False
                break

        # Apply reset
        self.log.debug(f"Applying reset during counting{self.get_time_ns_str()}")
        await self.wait_time(100)
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await self.wait_time(100)
        self.rst_n.value = 1

        # Check counters are reset to 0
        if int(self.counter_bin.value) != 0:
            self.log.error(f"Binary counter not reset to 0: got 0x{int(self.counter_bin.value):X}{self.get_time_ns_str()}")
            all_passed = False
            
        if int(self.counter_gray.value) != 0:
            self.log.error(f"Gray counter not reset to 0: got 0x{int(self.counter_gray.value):X}{self.get_time_ns_str()}")
            all_passed = False

        # Verify counting resumes from 0
        for i in range(min(16, len(self.expected_bin_sequence))):
            expected_bin = self.expected_bin_sequence[i]
            expected_gray = self.expected_gray_sequence[i]
            if not await self.check_counter_values(expected_bin, expected_gray, i):
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

    async def test_gray_code_properties(self):
        """Test Gray code properties (adjacent values differ by only 1 bit)"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping Gray code properties test for gate level{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing Gray code properties{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        self.enable.value = 1

        # Test a reasonable number of transitions
        test_cycles = min(len(self.expected_gray_sequence), 100 if self.TEST_LEVEL == 'func' else len(self.expected_gray_sequence))
        
        prev_gray = 0  # Start with reset value
        
        for cycle in range(test_cycles):
            await RisingEdge(self.clk)
            
            current_gray = int(self.counter_gray.value)
            
            # Check that adjacent Gray codes differ by exactly 1 bit
            if cycle > 0:  # Skip first cycle
                xor_result = prev_gray ^ current_gray
                bit_count = bin(xor_result).count('1')
                
                if bit_count != 1:
                    self.log.error(f"Cycle {cycle}: Gray code violation - 0x{prev_gray:X} -> 0x{current_gray:X} differs by {bit_count} bits{self.get_time_ns_str()}")
                    all_passed = False
                    if self.TEST_LEVEL == 'func':
                        break
                elif self.DEBUG and cycle % 20 == 0:
                    self.log.debug(f"Cycle {cycle}: Gray transition OK - 0x{prev_gray:X} -> 0x{current_gray:X}{self.get_time_ns_str()}")
            
            prev_gray = current_gray

            # Progress reporting
            if cycle % 50 == 0:
                self.mark_progress(f"Gray code test cycle {cycle}")

        # Store result
        result = {
            'test_type': 'gray_code_properties',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        self.log.info(f"Gray code properties test {'PASSED' if all_passed else 'FAILED'}{self.get_time_ns_str()}")
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

        # Test full sequence plus wrap
        test_cycles = len(self.expected_bin_sequence) + 5

        for cycle in range(test_cycles):
            await RisingEdge(self.clk)
            
            expected_bin = self.expected_bin_sequence[cycle % len(self.expected_bin_sequence)]
            expected_gray = self.expected_gray_sequence[cycle % len(self.expected_gray_sequence)]
            
            if not await self.check_counter_values(expected_bin, expected_gray, cycle):
                all_passed = False
                break

            # Mark important transitions
            if cycle == self.MAX_VALUE:
                self.log.info(f"About to wrap from max value{self.get_time_ns_str()}")
            elif cycle == len(self.expected_bin_sequence):
                self.log.info(f"Wrapped back to beginning{self.get_time_ns_str()}")

            # Progress reporting
            if cycle % 100 == 0:
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
            for i in range(min(10, len(self.expected_bin_sequence) // 8)):
                await RisingEdge(self.clk)
                expected_bin = self.expected_bin_sequence[i]
                expected_gray = self.expected_gray_sequence[i]
                if not await self.check_counter_values(expected_bin, expected_gray, i):
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
            for i in range(self.MAX_VALUE):
                await RisingEdge(self.clk)
            
            # Reset during the cycle that should wrap
            self.rst_n.value = 0
            await RisingEdge(self.clk)
            self.rst_n.value = 1
            await RisingEdge(self.clk)
            
            # Should be back at 0
            if int(self.counter_bin.value) != 0 or int(self.counter_gray.value) != 0:
                self.log.error(f"Reset at wrap failed: Bin=0x{int(self.counter_bin.value):X}, Gray=0x{int(self.counter_gray.value):X}{self.get_time_ns_str()}")
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
        self.log.info(f"Running COUNTER_BINGRAY tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_counting, "Basic counting"),
            (self.test_enable_disable, "Enable/disable"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_gray_code_properties, "Gray code properties"),
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
        self.log.info(f"Overall COUNTER_BINGRAY result: {overall_status}{self.get_time_ns_str()}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}{self.get_time_ns_str()}")
        self.log.info("="*60)

        return all_passed
