# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterLoadClearTB
# Purpose: Testbench for counter_load_clear
# Subsystem: framework
#
# Extracted from val/common/test_counter_load_clear.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import math
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class CounterLoadClearTB(TBBase):
    """Testbench for Counter Load Clear module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.MAX_VALUE = self.convert_to_int(os.environ.get('TEST_MAX_VALUE', '32'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate count width
        self.COUNT_WIDTH = math.ceil(math.log2(self.MAX_VALUE)) if self.MAX_VALUE > 1 else 1
        self.MAX_COUNT = (1 << self.COUNT_WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

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
        if self.TEST_LEVEL == 'gate':
            test_values = [1, 5, min(10, self.MAX_VALUE - 1)]
        elif self.TEST_LEVEL == 'func':
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
                if self.TEST_LEVEL == 'gate':
                    break
                continue

            if int(self.done.value) != (1 if match_value == 0 else 0):
                self.log.error(f"Initial done state incorrect for match_value {match_value}{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'gate':
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
                    if self.TEST_LEVEL == 'gate':
                        break

                if cycles_to_done != match_value:
                    self.log.error(f"Match {match_value}: Cycles {cycles_to_done} != expected {match_value}{self.get_time_ns_str()}")
                    all_passed = False
                    if self.TEST_LEVEL == 'gate':
                        break

                self.log.debug(f"Match {match_value}: SUCCESS - {cycles_to_done} cycles, final count {final_count}{self.get_time_ns_str()}")

            except TimeoutError as e:
                self.log.error(f"Match {match_value}: {str(e)}{self.get_time_ns_str()}")
                all_passed = False
                if self.TEST_LEVEL == 'gate':
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
        if self.TEST_LEVEL == 'gate':
            test_values = [1, 5]
        elif self.TEST_LEVEL == 'func':
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
                if self.TEST_LEVEL == 'gate':
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

            if not all_passed and self.TEST_LEVEL == 'gate':
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
        if self.TEST_LEVEL == 'gate':
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
