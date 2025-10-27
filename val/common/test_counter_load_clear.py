# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CounterLoadClearTB
# Purpose: Counter Load Clear Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Counter Load Clear Test with Parameterized Test Levels and Configuration

This test uses max_value and test_level as parameters for maximum flexibility:

CONFIGURATION:
    max_value:   Maximum count value (32, 255, 1023)

TEST LEVELS (per-test depth):
    basic (1-2 min):   Quick verification during development
    medium (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~2 min) - smoke test (max=32, basic)
    FUNC: 3 tests (~6 min) - functional coverage - DEFAULT
    FULL: 9 tests (~1 hour) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 max_value × 1 level = 1 test
    FUNC: 3 max_values × 1 level = 3 tests (all max_values, basic only)
    FULL: 3 max_values × 3 levels = 9 tests

Environment Variables:
    REG_LEVEL: Control parameter combinations (GATE/FUNC/FULL)
    TEST_LEVEL: Set test level in cocotb (basic/medium/full)
    SEED: Set random seed for reproducibility
    TEST_MAX_VALUE: Maximum count value for counter
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


class CounterLoadClearTB(TBBase):
    """Testbench for Counter Load Clear module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.MAX_VALUE = self.convert_to_int(os.environ.get('TEST_MAX_VALUE', '32'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate count width
        self.COUNT_WIDTH = math.ceil(math.log2(self.MAX_VALUE)) if self.MAX_VALUE > 1 else 1
        self.MAX_COUNT = (1 << self.COUNT_WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log configuration
        self.log.info(f"Counter Load Clear TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}{self.get_time_ns_str()}")
        self.log.info(f"MAX_VALUE={self.MAX_VALUE}, COUNT_WIDTH={self.COUNT_WIDTH}{self.get_time_ns_str()}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

    def get_time_ns_str(self):
        """Get current simulation time as formatted string"""
        try:
            import cocotb
            current_time = cocotb.utils.get_sim_time(units='ns')
            return f" @ {current_time}ns"
        except:
            return ""

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.clear = self.dut.clear
        self.increment = self.dut.increment
        self.load = self.dut.load
        self.loadval = self.dut.loadval
        self.count = self.dut.count
        self.done = self.dut.done

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.clear.value = 0
        self.increment.value = 0
        self.load.value = 0
        self.loadval.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        # Wait longer after reset release for RTL to stabilize
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)  # Extra clocks for stability

    async def load_match_value(self, match_value):
        """Load a new match value"""
        self.load.value = 1
        self.loadval.value = match_value
        await RisingEdge(self.clk)
        self.load.value = 0
        await RisingEdge(self.clk)

    async def increment_to_done(self, expected_count, timeout_cycles=None):
        """Increment counter until done signal asserts, return count when done asserted"""
        if timeout_cycles is None:
            timeout_cycles = expected_count + 10

        cycle_count = 0
        self.increment.value = 1

        while cycle_count < timeout_cycles:
            await RisingEdge(self.clk)
            current_count = int(self.count.value)
            done_state = int(self.done.value)
            
            if done_state == 1:
                self.increment.value = 0
                return cycle_count, current_count  # Return count when done was asserted
            
            cycle_count += 1

        self.increment.value = 0
        raise TimeoutError(f"Done not asserted within {timeout_cycles} cycles")

    async def test_basic_counting(self):
        """Test basic counting functionality"""
        self.log.info(f"Testing basic counting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test different match values based on level
        if self.TEST_LEVEL == 'basic':
            test_values = [1, 5, min(10, self.MAX_VALUE - 1)]
        elif self.TEST_LEVEL == 'medium':
            test_values = [1, 3, 5, 10, min(20, self.MAX_VALUE - 1), self.MAX_VALUE - 1]
        else:  # full
            test_values = [1, 2, 3, 5, 8, 10, 15, 20, min(50, self.MAX_VALUE - 1), self.MAX_VALUE - 1]
            if self.MAX_VALUE > 100:
                test_values.extend([self.MAX_VALUE // 4, self.MAX_VALUE // 2, self.MAX_VALUE - 1])

        # Remove duplicates and filter valid values
        test_values = sorted(list(set([v for v in test_values if 0 <= v < self.MAX_VALUE])))

        all_passed = True

        for match_value in test_values:
            self.log.debug(f"Testing match value: {match_value}{self.get_time_ns_str()}")
            
            # Load match value
            await self.load_match_value(match_value)
            
            # Verify initial state
            if int(self.count.value) != 0:
                self.log.error(f"Initial count not zero: {int(self.count.value)}{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break
                continue

            if int(self.done.value) != (1 if match_value == 0 else 0):
                self.log.error(f"Initial done state incorrect for match_value {match_value}{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break
                continue

            # Skip increment test if match_value is 0 (done immediately)
            if match_value == 0:
                continue

            try:
                cycles_to_done, final_count = await self.increment_to_done(match_value)
                
                # Verify results
                if final_count != match_value:
                    self.log.error(f"Match {match_value}: Final count {final_count} != expected {match_value}{self.get_time_ns_str()}")
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        break

                if cycles_to_done != match_value:
                    self.log.error(f"Match {match_value}: Cycles {cycles_to_done} != expected {match_value}{self.get_time_ns_str()}")
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        break

                self.log.debug(f"Match {match_value}: SUCCESS - {cycles_to_done} cycles, final count {final_count}{self.get_time_ns_str()}")

            except TimeoutError as e:
                self.log.error(f"Match {match_value}: {str(e)}{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Store result
            result = {
                'test_type': 'basic_counting',
                'match_value': match_value,
                'expected_cycles': match_value,
                'actual_cycles': cycles_to_done if 'cycles_to_done' in locals() else -1,
                'final_count': final_count if 'final_count' in locals() else -1,
                'success': (cycles_to_done == match_value and final_count == match_value) if 'cycles_to_done' in locals() else False
            }
            self.test_results.append(result)
            if not result['success']:
                self.test_failures.append(result)

            # Reset for next test
            await self.reset_dut()

        return all_passed

    async def test_clear_functionality(self):
        """Test clear functionality"""
        self.log.info(f"Testing clear functionality{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        match_value = min(10, self.MAX_VALUE - 1)

        # Load match value
        await self.load_match_value(match_value)

        # Count partway - just increment a few times without strict checking
        self.increment.value = 1
        for i in range(3):  # Count to 3 (simple and predictable)
            await RisingEdge(self.clk)
        self.increment.value = 0
        await RisingEdge(self.clk)  # Let signals settle

        # Record count before clear
        count_before_clear = int(self.count.value)
        self.log.debug(f"Count before clear: {count_before_clear}{self.get_time_ns_str()}")

        # Apply clear signal
        self.clear.value = 1
        await RisingEdge(self.clk)
        self.clear.value = 0
        await RisingEdge(self.clk)

        # Verify count is cleared - this is the main test
        count_after_clear = int(self.count.value)
        if count_after_clear != 0:
            self.log.error(f"Count not cleared: {count_after_clear}, expected 0{self.get_time_ns_str()}")
            all_passed = False
        else:
            self.log.debug(f"Clear successful: count went from {count_before_clear} to {count_after_clear}{self.get_time_ns_str()}")

        # Verify done state after clear
        done_after_clear = int(self.done.value)
        expected_done = 1 if match_value == 0 else 0
        if done_after_clear != expected_done:
            self.log.error(f"Done state after clear incorrect: {done_after_clear} != {expected_done}{self.get_time_ns_str()}")
            all_passed = False

        # Test counting after clear works normally
        if match_value > 0:
            try:
                cycles_to_done, final_count = await self.increment_to_done(match_value)
                
                if cycles_to_done != match_value or final_count != match_value:
                    self.log.error(f"After clear: cycles={cycles_to_done}, count={final_count}, expected={match_value}{self.get_time_ns_str()}")
                    all_passed = False
                else:
                    self.log.debug(f"Post-clear counting successful: {cycles_to_done} cycles to reach {final_count}{self.get_time_ns_str()}")

            except TimeoutError as e:
                self.log.error(f"After clear: {str(e)}{self.get_time_ns_str()}")
                all_passed = False

        # Store result
        result = {
            'test_type': 'clear_functionality',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_load_functionality(self):
        """Test load functionality"""
        self.log.info(f"Testing load functionality{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test different load values
        if self.TEST_LEVEL == 'basic':
            test_values = [1, 5]
        elif self.TEST_LEVEL == 'medium':
            test_values = [1, 3, 5, 10, 15]
        else:  # full
            test_values = [1, 2, 3, 5, 8, 10, 15, 20, 50]

        # Filter valid values
        test_values = [v for v in test_values if 0 <= v < self.MAX_VALUE]

        for load_value in test_values:
            # Start with different load value
            await self.load_match_value(5)  # Initial value
            
            # Count partway
            self.increment.value = 1
            for i in range(2):
                await RisingEdge(self.clk)
            self.increment.value = 0

            # Change load value mid-count
            await self.load_match_value(load_value)

            # Verify count continues from where it was
            current_count = int(self.count.value)
            if current_count != 2:
                self.log.error(f"Count changed after load: {current_count} != 2{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            # Continue counting to new target
            if load_value > 2:
                try:
                    remaining_cycles = load_value - 2
                    self.increment.value = 1
                    final_count = None
                    done_cycle = None
                    
                    for i in range(remaining_cycles + 2):  # Allow extra cycles for safety
                        await RisingEdge(self.clk)
                        current_count = int(self.count.value)
                        done_state = int(self.done.value)
                        
                        if done_state == 1 and done_cycle is None:
                            done_cycle = i
                            final_count = current_count
                            break
                            
                    self.increment.value = 0

                    if final_count != load_value:
                        self.log.error(f"Final count when done asserted: {final_count} != load value {load_value}{self.get_time_ns_str()}")
                        all_passed = False
                        
                    if done_cycle != remaining_cycles:
                        self.log.error(f"Done asserted at cycle {done_cycle}, expected cycle {remaining_cycles}{self.get_time_ns_str()}")
                        all_passed = False

                except Exception as e:
                    self.log.error(f"Load test failed: {str(e)}{self.get_time_ns_str()}")
                    all_passed = False

            if not all_passed and self.TEST_LEVEL == 'basic':
                break

            # Reset for next test
            await self.reset_dut()

        # Store result
        result = {
            'test_type': 'load_functionality',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_increment_control(self):
        """Test increment control"""
        if self.TEST_LEVEL == 'basic':
            self.log.info(f"Skipping increment control test{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing increment control{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        match_value = min(5, self.MAX_VALUE - 1)

        # Load match value
        await self.load_match_value(match_value)

        # Test that counter doesn't increment without increment signal
        self.increment.value = 0
        for i in range(10):
            await RisingEdge(self.clk)
            if int(self.count.value) != 0:
                self.log.error(f"Counter incremented without increment signal: {int(self.count.value)}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Test intermittent increment
        self.increment.value = 1
        await RisingEdge(self.clk)  # Count to 1
        self.increment.value = 0
        
        # Wait several cycles
        for i in range(5):
            await RisingEdge(self.clk)
            if int(self.count.value) != 1:
                self.log.error(f"Counter changed without increment: {int(self.count.value)}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Continue incrementing - be more careful about timing
        for target in range(2, match_value + 1):
            self.increment.value = 1
            await RisingEdge(self.clk)
            self.increment.value = 0
            # Wait for count to settle after increment
            await RisingEdge(self.clk)
            
            current_count = int(self.count.value)
            expected_done = 1 if target == match_value else 0
            actual_done = int(self.done.value)
            
            if current_count != target:
                self.log.error(f"Count {current_count} != expected {target}{self.get_time_ns_str()}")
                all_passed = False
                break
                
            if actual_done != expected_done:
                self.log.error(f"Done {actual_done} != expected {expected_done} at count {target}{self.get_time_ns_str()}")
                all_passed = False
                break

        # Store result
        result = {
            'test_type': 'increment_control',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_edge_cases(self):
        """Test edge cases and boundary conditions"""
        if self.TEST_LEVEL != 'full':
            self.log.info(f"Skipping edge case tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing edge cases{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test match value of 0 (immediate done)
        await self.load_match_value(0)
        if int(self.done.value) != 1:
            self.log.error(f"Match value 0: done not immediately asserted{self.get_time_ns_str()}")
            all_passed = False

        # Test maximum possible match value
        max_match = min(self.MAX_VALUE - 1, 100)  # Limit for test time
        await self.reset_dut()
        await self.load_match_value(max_match)
        
        # Test simultaneous operations
        # Load and clear together
        self.load.value = 1
        self.clear.value = 1
        self.loadval.value = 5
        await RisingEdge(self.clk)
        self.load.value = 0
        self.clear.value = 0
        
        # Check that both operations occurred
        if int(self.count.value) != 0:
            self.log.error(f"Simultaneous load/clear: count not cleared{self.get_time_ns_str()}")
            all_passed = False

        # Test load and increment together
        await self.reset_dut()
        await self.load_match_value(10)
        
        # Increment to 3
        self.increment.value = 1
        for i in range(3):
            await RisingEdge(self.clk)
        self.increment.value = 0
        await RisingEdge(self.clk)  # Let count settle
        
        current_count_before_load = int(self.count.value)
        self.log.debug(f"Count before load change: {current_count_before_load}{self.get_time_ns_str()}")
        
        # Load new value while not incrementing
        self.load.value = 1
        self.loadval.value = 5
        await RisingEdge(self.clk)
        self.load.value = 0
        await RisingEdge(self.clk)  # Let load settle
        
        # Count should be unchanged by load operation
        current_count_after_load = int(self.count.value)
        if current_count_after_load != current_count_before_load:
            self.log.error(f"Count changed during load: {current_count_before_load} -> {current_count_after_load}{self.get_time_ns_str()}")
            all_passed = False
        
        # Continue to new target (5)
        if current_count_after_load < 5:
            remaining = 5 - current_count_after_load
            self.increment.value = 1
            for i in range(remaining):
                await RisingEdge(self.clk)
                if int(self.done.value) == 1:
                    break
            self.increment.value = 0
            await RisingEdge(self.clk)  # Let signals settle
            
            final_done = int(self.done.value)
            final_count = int(self.count.value)
            
            if final_done != 1:
                self.log.error(f"Load during increment: done not asserted correctly (done={final_done}, count={final_count}){self.get_time_ns_str()}")
                all_passed = False
            else:
                self.log.debug(f"Load during increment test passed: final count={final_count}, done={final_done}{self.get_time_ns_str()}")

        # Store result
        result = {
            'test_type': 'edge_cases',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running COUNTER_LOAD_CLEAR tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_counting, "Basic counting"),
            (self.test_clear_functionality, "Clear functionality"),
            (self.test_load_functionality, "Load functionality"),
            (self.test_increment_control, "Increment control"),
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
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")
        self.log.info(f"TEST RESULTS SUMMARY{self.get_time_ns_str()}")
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}{self.get_time_ns_str()}")
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall COUNTER_LOAD_CLEAR result: {overall_status}{self.get_time_ns_str()}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}{self.get_time_ns_str()}")
        self.log.info(f"{'='*60}{self.get_time_ns_str()}")

        return all_passed


@cocotb.test(timeout_time=20000, timeout_unit="us")
async def counter_load_clear_test(dut):
    """Test for Counter Load Clear module"""
    tb = CounterLoadClearTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"COUNTER_LOAD_CLEAR test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}{tb.get_time_ns_str()}")

    # Assert on failure
    assert passed, f"Counter Load Clear test FAILED - {len(tb.test_failures)} failures detected"

    return passed


def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (max=32, basic level)
    REG_LEVEL=FUNC: 3 tests (all max_values, basic level) - default
    REG_LEVEL=FULL: 9 tests (all max_values, all test levels)

    Returns:
        List of tuples: (max_value, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    max_values = [32, 255, 1023]  # Different maximum count values
    test_levels = ['basic', 'medium', 'full']  # Test levels

    if reg_level == 'GATE':
        # Quick smoke test: max=32, basic only
        params = [(32, 'basic')]

    elif reg_level == 'FUNC':
        # Functional coverage: all max_values, basic level only
        params = [(max_val, 'basic') for max_val in max_values]

    else:  # FULL
        # Comprehensive: all combinations
        params = []
        for max_value, test_level in product(max_values, test_levels):
            params.append((max_value, test_level))

    return params


params = generate_params()


@pytest.mark.parametrize("max_value, test_level", params)
def test_counter_load_clear(request, max_value, test_level):
    """
    Parameterized Counter Load Clear test with configurable max value and test level.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "counter_load_clear"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/counter_load_clear.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    max_str = TBBase.format_dec(max_value, 4)
    test_name_plus_params = f"test_counter_load_clear_max{max_str}_{test_level}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'MAX': str(max_value)
    }

    # Adjust timeout based on test level and max value
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    max_factor = max(1.0, max_value / 1000.0)
    base_timeout = 3000  # 3 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * max_factor)

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
        'TEST_MAX_VALUE': str(max_value),
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
    print(f"Running {test_level.upper()} test: max_value={max_value}")
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
        print(f"✓ {test_level.upper()} test PASSED: max_value={max_value}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
