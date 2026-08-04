# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: CounterTB
# Purpose: Testbench for counter
# Subsystem: framework
#
# Extracted from val/common/test_counter.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class CounterTB(TBBase):
    """Testbench for Generic Counter module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.MAX_VALUE = self.convert_to_int(os.environ.get('TEST_MAX_VALUE', '32767'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"Counter TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"MAX_VALUE={self.MAX_VALUE}")
        self.log.info(f"Expected cycles before tick: {self.MAX_VALUE}")

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

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.tick = self.dut.tick

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    async def wait_for_tick(self, timeout_cycles=None):
        """Wait for tick signal to go high"""
        if timeout_cycles is None:
            timeout_cycles = self.MAX_VALUE + 20

        cycle_count = 0
        while cycle_count < timeout_cycles:
            cycle_count += 1
            await RisingEdge(self.clk)
            if self.tick.value == 1:
                return cycle_count
        
        raise TimeoutError(f"Tick not received within {timeout_cycles} cycles")

    async def test_basic_counting(self):
        """Test basic counting functionality"""
        self.log.info("=== Scenario CTR-01: Basic counting ===")
        self.log.info(f"Testing basic counting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test based on level
        if self.TEST_LEVEL == 'gate':
            num_cycles = 2  # Test 2 complete cycles
        elif self.TEST_LEVEL == 'func':
            num_cycles = 5  # Test 5 complete cycles
        else:  # full
            num_cycles = 10  # Test 10 complete cycles

        all_passed = True
        expected_cycles = self.MAX_VALUE  # Continuous cycles should also be MAX  # After reset, counter takes MAX cycles to reach MAX  # RTL takes exactly MAX cycles to go from 0 to MAX

        for cycle in range(num_cycles):
            self.log.debug(f"Starting cycle {cycle + 1}")
            
            # Wait for tick
            try:
                cycles_to_tick = await self.wait_for_tick()
                
                if cycles_to_tick != expected_cycles:
                    self.log.error(f"Cycle {cycle + 1}: Expected {expected_cycles} cycles, got {cycles_to_tick}")
                    all_passed = False
                    if self.TEST_LEVEL == 'gate':
                        break
                else:
                    self.log.debug(f"Cycle {cycle + 1}: Correct timing - {cycles_to_tick} cycles{self.get_time_ns_str()}")

                # Verify tick is only high for one cycle
                await RisingEdge(self.clk)
                if self.tick.value != 0:
                    self.log.error(f"Cycle {cycle + 1}: Tick should be low after one cycle")
                    all_passed = False
                    if self.TEST_LEVEL == 'gate':
                        break

            except TimeoutError as e:
                self.log.error(f"Cycle {cycle + 1}: {str(e)}{self.get_time_ns_str()}")
                all_passed = False
                break

            # Store result
            result = {
                'test_type': 'basic_counting',
                'cycle': cycle + 1,
                'expected_cycles': expected_cycles,
                'actual_cycles': cycles_to_tick if 'cycles_to_tick' in locals() else -1,
                'success': cycles_to_tick == expected_cycles if 'cycles_to_tick' in locals() else False
            }
            self.test_results.append(result)
            if not result['success']:
                self.test_failures.append(result)

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info("=== Scenario CTR-02: Reset behavior ===")
        self.log.info(f"Testing reset behavior{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True
        expected_cycles = self.MAX_VALUE

        # Count partway through cycle
        partial_count = self.MAX_VALUE // 2 if self.MAX_VALUE > 4 else 2
        
        for i in range(partial_count):
            await RisingEdge(self.clk)
            if self.tick.value == 1:
                self.log.error(f"Unexpected tick at cycle {i}")
                all_passed = False
                break

        # Apply reset
        self.rst_n.value = 0
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

        # Now count full cycle and verify timing
        try:
            cycles_to_tick = await self.wait_for_tick()
            if cycles_to_tick != expected_cycles:
                self.log.error(f"After reset: Expected {expected_cycles} cycles, got {cycles_to_tick}")
                all_passed = False
            else:
                self.log.debug(f"After reset: Correct timing - {cycles_to_tick} cycles{self.get_time_ns_str()}")
        except TimeoutError as e:
            self.log.error(f"After reset: {str(e)}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'reset_behavior',
            'expected_cycles': expected_cycles,
            'actual_cycles': cycles_to_tick if 'cycles_to_tick' in locals() else -1,
            'success': cycles_to_tick == expected_cycles if 'cycles_to_tick' in locals() else False
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_continuous_operation(self):
        """Test continuous operation over multiple cycles"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping continuous operation test{self.get_time_ns_str()}")
            return True

        self.log.info("=== Scenario CTR-03: Continuous operation ===")
        self.log.info(f"Testing continuous operation{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        # Test multiple cycles
        if self.TEST_LEVEL == 'func':
            num_cycles = 3
        else:  # full
            num_cycles = 5

        all_passed = True
        cycle_times = []
        expected_cycles = self.MAX_VALUE\
        

        for cycle in range(num_cycles):
            if cycle > 0:
                expected_cycles = self.MAX_VALUE+1
            try:
                cycles_to_tick = await self.wait_for_tick()
                cycle_times.append(cycles_to_tick)
                
                if cycles_to_tick != expected_cycles:
                    self.log.error(f"Continuous cycle {cycle + 1}: Expected {expected_cycles}, got {cycles_to_tick}")
                    all_passed = False
                    break
                    
            except TimeoutError as e:
                self.log.error(f"Continuous cycle {cycle + 1}: {str(e)}")
                all_passed = False
                break

        # Store result
        result = {
            'test_type': 'continuous_operation',
            'num_cycles': len(cycle_times),
            'cycle_times': cycle_times,
            'success': all_passed and len(cycle_times) == num_cycles
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

        self.log.info("=== Scenario CTR-04: Edge cases ===")
        self.log.info(f"Testing edge cases{self.get_time_ns_str()}")

        await self.setup_clock()
        
        all_passed = True
        expected_cycles = self.MAX_VALUE  # Edge case should also expect MAX cycles

        # Test multiple rapid resets
        for reset_test in range(3):
            await self.reset_dut()
            
            # Count a few cycles
            for i in range(min(5, self.MAX_VALUE // 4)):
                await RisingEdge(self.clk)
                if self.tick.value == 1 and i < expected_cycles - 1:
                    self.log.error(f"Unexpected early tick in reset test {reset_test}")
                    all_passed = False
                    break

            if not all_passed:
                break

        # Test reset during tick. Disabled with `if False:` from 2025 until
        # COMMON-011; tick is a registered output now.
        #
        # Sampling uses wait_clocks, never a bare RisingEdge: the framework's
        # wait_clocks always delays past the edge before returning, so the
        # value read is the settled one. Sampling inside that window reads the
        # pre-edge value and reports a tick that has already gone -- which is
        # what an earlier version of this check tripped on.
        if True:
            await self.reset_dut()

            # Wait until just before tick
            for i in range(expected_cycles - 1):
                await self.wait_clocks('clk', 1)

            # Assert reset on the cycle that would have produced tick.
            self.rst_n.value = 0
            await self.wait_clocks('clk', 1)

            # tick must stay low for as long as reset is held.
            for _ in range(3):
                if self.tick.value == 1:
                    self.log.error("Tick occurred during reset")
                    all_passed = False
                    break
                await self.wait_clocks('clk', 1)

            self.rst_n.value = 1
            await RisingEdge(self.clk)

            # Now should start counting from 0 again
            try:
                cycles_to_tick = await self.wait_for_tick()
                if cycles_to_tick != expected_cycles:
                    self.log.error(f"After reset during tick: Expected {expected_cycles}, got {cycles_to_tick}")
                    all_passed = False
            except TimeoutError:
                all_passed = False


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
        self.log.info(f"Running COUNTER tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_counting, "Basic counting"),
            (self.test_reset_behavior, "Reset behavior"),
            (self.test_continuous_operation, "Continuous operation"),
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
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall COUNTER result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
