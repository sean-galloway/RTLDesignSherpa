# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ClockGateCtrlConfig
# Purpose: Configuration class for clock gate controller tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random
import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from conftest import get_coverage_compile_args

class ClockGateCtrlConfig:
    """Configuration class for clock gate controller tests"""
    def __init__(self, name, counter_width):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            counter_width: Counter width in bits
        """
        self.name = name
        self.counter_width = counter_width

class ClockGateCtrlTB(TBBase):
    """
    Testbench for the clock_gate_ctrl module
    Features:
    - Clock gating behavior verification
    - Counter timeout testing
    - Enable/disable functionality
    - Wake signal handling
    - Randomized test scenarios using FlexRandomizer
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '4'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Derived parameters
        self.max_count = (2**self.N) - 1
        self.last_idle_count = self.max_count

        # Clock and reset signals
        self.clock = self.dut.clk_in
        self.reset_n = self.dut.aresetn

        # Setup FlexRandomizer with multiple constraint types
        randomizer_constraints = {
            # Idle count values - full range with bias toward interesting values
            'idle_count': ([(0, 1), (2, self.max_count//4), (self.max_count//2, self.max_count)], [2, 3, 1]),
            
            # Wait cycles between operations - mostly short with occasional longer waits
            'wait_cycles': ([(1, 5), (6, 15), (20, 30)], [6, 3, 1]),
            
            # Verification cycles - how long to verify each state
            'verify_cycles': ([(3, 8), (10, 15)], [7, 3]),
            
            # Wake timing offsets for timeout tests
            'wake_offset': ([(-5, -1), (0, 2), (3, 8)], [2, 4, 1]),
            
            # Boolean choice using object bins (weighted toward enabled)
            'enable_choice': ([(True,), (False,)], [3, 1]),
            
            # Alternative: Use integer 0/1 for boolean choice
            'enable_int': ([(0, 0), (1, 1)], [1, 3]),  # 0=disabled, 1=enabled
            
            # Test pattern selection using sequences
            'test_pattern': ['incremental', 'random', 'edge_cases', 'stress']
        }

        self.randomizer = FlexRandomizer(randomizer_constraints)

        # Log configuration
        self.log.info(f"Clock Gate Ctrl TB initialized with N={self.N}")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"Max count value: {self.max_count}")

    def get_random_idle_count(self):
        """Get a randomized idle count value"""
        values = self.randomizer.next()
        return values['idle_count']

    def get_random_wait_cycles(self):
        """Get randomized wait cycles"""
        values = self.randomizer.next()
        return values['wait_cycles']

    def get_random_verify_cycles(self):
        """Get randomized verification cycles"""
        values = self.randomizer.next()
        return values['verify_cycles']

    def get_random_wake_offset(self):
        """Get randomized wake timing offset"""
        values = self.randomizer.next()
        return values['wake_offset']

    def get_random_enable_choice(self):
        """Get randomized enable choice (returns boolean)"""
        values = self.randomizer.next()
        return values['enable_choice']

    def get_random_enable_int(self):
        """Get randomized enable choice as integer (0 or 1)"""
        values = self.randomizer.next()
        return bool(values['enable_int'])  # Convert 0/1 to False/True

    def get_next_test_pattern(self):
        """Get next test pattern from sequence"""
        values = self.randomizer.next()
        return values['test_pattern']

    def assert_reset(self):
        """Reset the DUT to known state"""
        self.reset_n.value = 0
        self.dut.cfg_cg_enable.value = 0
        self.dut.cfg_cg_idle_count.value = self.max_count
        self.last_idle_count = self.max_count
        self.dut.wakeup.value = 0
        self.log.info('Assert reset done.')

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.assert_reset()

        # Hold reset for random number of cycles
        reset_cycles = self.get_random_wait_cycles()
        await self.wait_clocks('clk_in', reset_cycles)

        # Release reset
        self.reset_n.value = 1

        # Wait for stabilization with random cycles
        stab_cycles = self.get_random_wait_cycles()
        await self.wait_clocks('clk_in', stab_cycles)

        self.log.debug(f'Reset completed after {reset_cycles + stab_cycles} cycles')

    async def verify_clock_gating(self, cycles, expected_enabled, description=None):
        """
        Verify clock gating behavior for specified cycles

        Args:
            cycles: Number of cycles to verify (can be randomized)
            expected_enabled: Expected clock enable state
            description: Optional description for logging
        """
        # Allow cycles to be randomized if not specified
        if cycles == 'random':
            cycles = self.get_random_verify_cycles()

        msg_prefix = f"{description}: " if description else ""
        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Verifying clock for {cycles} cycles, expected enabled: {expected_enabled} @ {time_ns}ns")

        failures = 0
        for i in range(cycles):
            await self.wait_clocks('clk_in', 1)

            if expected_enabled:
                # When enabled, clock output should match input on rising edge
                if self.dut.clk_in.value == 1 and self.dut.clk_out.value != 1:
                    failures += 1
                    self.log.warning(f"{msg_prefix}Cycle {i}: Clock should be enabled but was gated @ {get_sim_time('ns')}ns")
            else:
                # When gated, clock output should always be 0
                if self.dut.clk_out.value != 0:
                    failures += 1
                    self.log.warning(f"{msg_prefix}Cycle {i}: Clock should be gated but was enabled @ {get_sim_time('ns')}ns")

            # Only assert after all cycles checked, to collect comprehensive failure data
            if failures > 3:  # Limit excessive logging
                self.log.error(f"{msg_prefix}Too many failures, aborting verification @ {get_sim_time('ns')}ns")
                assert False, f"{msg_prefix}Clock gating verification failed in {failures} cycles"

        if failures > 0:
            assert False, f"{msg_prefix}Clock gating verification failed in {failures} cycles"

        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Clock verification passed @ {time_ns}ns")

    async def wait_for_counter_expiration(self, count_value, description=None):
        """
        Wait for the idle counter to expire

        Args:
            count_value: Value to count down from
            description: Optional description for logging
            
        Note: This waits for the full counter duration plus margin.
        The clock should remain enabled during countdown and get gated
        after the counter reaches 0.
        """
        msg_prefix = f"{description}: " if description else ""
        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Waiting for counter to expire from {count_value} @ {time_ns}ns")

        # Wait for full counter duration plus margin for initialization delays
        # The counter needs count_value cycles to reach 0, then gating occurs
        wait_cycles = count_value + random.randint(2, 4)
        await self.wait_clocks('clk_in', wait_cycles)

        time_ns = get_sim_time('ns')
        self.log.debug(f"{msg_prefix}Counter should have expired after {wait_cycles} cycles @ {time_ns}ns")

    async def run_systematic_enable_test(self):
        """Test all combinations of wake with cfg_enable=1"""
        time_ns = get_sim_time('ns')
        self.log.info("=== Scenario CLK-01: Systematic enable test ===")
        self.log.info(f"Starting systematic enable test @ {time_ns}ns")

        self.dut.cfg_cg_enable.value = 1
        self.dut.cfg_cg_idle_count.value = self.max_count  # Set max count to focus on wake

        # Test wake=1 scenario (clock should be enabled immediately)
        self.log.info(f"Testing wake=1 @ {get_sim_time('ns')}ns")
        self.dut.wakeup.value = 1
        await self.verify_clock_gating('random', True, "Wake=1")

        # Test wake=0 scenario (clock should be gated after counter expires)
        self.log.info(f"Testing wake=0 @ {get_sim_time('ns')}ns")
        self.dut.wakeup.value = 0

        # First verify clock remains active during countdown
        await self.verify_clock_gating('random', True, "Wake=0 during countdown")

        # Wait for counter to expire (max_count cycles plus margin)
        self.log.info(f"Waiting for counter to expire (max_count={self.max_count}) @ {get_sim_time('ns')}ns")
        await self.wait_for_counter_expiration(self.max_count, "Wake=0")

        # Verify clock is now gated
        await self.verify_clock_gating('random', False, "Wake=0 after expiration")

        time_ns = get_sim_time('ns')
        self.log.info(f"Systematic enable test completed @ {time_ns}ns")

    async def run_concurrent_wake_test(self):
        """Test concurrent assertion of wake signals"""
        time_ns = get_sim_time('ns')
        self.log.info("=== Scenario CLK-02: Concurrent wake test ===")
        self.log.info(f"Starting concurrent wake test @ {time_ns}ns")

        # Use randomized count for this test, but avoid 0 which needs special handling
        count = self.get_random_idle_count()
        if count == 0:
            count = 1  # Use minimum meaningful count for this test
            
        self.log.info(f"Using count={count} for concurrent wake test")
        self.dut.cfg_cg_enable.value = 1
        self.dut.cfg_cg_idle_count.value = count

        # Test concurrent assertion
        self.dut.wakeup.value = 1
        await self.verify_clock_gating('random', True, "Concurrent wake")  # Wake should dominate

        # Deassert wake, verify counter starts
        self.dut.wakeup.value = 0
        # Verify clock remains enabled during countdown (early part only)
        if count > 3:
            verify_cycles = min(count // 3, 5)  # Check early countdown only
            await self.verify_clock_gating(verify_cycles, True, "After wake, during countdown")

        # Wait for counter to fully expire
        await self.wait_for_counter_expiration(count, "Concurrent wake test")

        # After counter expires, clock should be gated
        await self.verify_clock_gating('random', False, "After counter expires")

        time_ns = get_sim_time('ns')
        self.log.info(f"Concurrent wake test completed @ {time_ns}ns")

    async def run_systematic_counter_test(self):
        """Test various idle counter values using randomization"""
        time_ns = get_sim_time('ns')
        self.log.info("=== Scenario CLK-03: Systematic counter test ===")
        self.log.info(f"Starting systematic counter test @ {time_ns}ns")

        self.dut.cfg_cg_enable.value = 1
        
        # Generate a mix of fixed and random test values
        test_values = [
            self.max_count,                # Max
            self.max_count * 3 // 4,       # Max-1/4
            self.max_count // 2,           # Max-1/2
            self.max_count // 4,           # Max-3/4
        ]
        
        # Add some random values
        for _ in range(3):
            test_values.append(self.get_random_idle_count())

        for count in test_values:
            time_ns = get_sim_time('ns')
            msg = f"Testing idle count: {count} @ {time_ns}ns"
            self.log.info(msg)

            self.dut.cfg_cg_idle_count.value = count
            self.last_idle_count = count

            # Trigger wake with random timing
            self.dut.wakeup.value = 1
            wake_time = self.get_random_wait_cycles()
            await self.wait_clocks('clk_in', wake_time)
            
            # Special handling for count=0 edge case
            if count == 0:
                # For count=0, clock should gate immediately when wake is deasserted
                self.log.info(f"Special case: count=0 - expecting immediate gating")
                self.dut.wakeup.value = 0
                
                # Wait a couple cycles for gating to occur
                await self.wait_clocks('clk_in', 2)
                
                # Verify clock is gated immediately
                await self.verify_clock_gating('random', False, f"Count={count} immediate gating")
                
            else:
                # Normal case: count > 0
                self.dut.wakeup.value = 0

                # Test strategy:
                # 1. Verify clock is active during early countdown (safe timing)
                # 2. Wait for full counter expiration 
                # 3. Verify clock is gated after expiration
                
                # Verify clock runs during the countdown (but not the full count to avoid timing issues)
                verify_cycles = max(1, min(count // 2, 5)) if count > 2 else 1
                await self.verify_clock_gating(verify_cycles, True, f"Count={count} active")

                # Wait for the full counter expiration plus margin
                await self.wait_for_counter_expiration(count, f"Count={count}")

                # Add a few more cycles to ensure gating has occurred
                await self.wait_clocks('clk_in', 3)

                # Verify clock is gated after timeout
                await self.verify_clock_gating('random', False, f"Count={count} gated")

            # Add a brief pause between iterations
            self.dut.wakeup.value = 1
            pause_cycles = self.get_random_wait_cycles()
            await self.wait_clocks('clk_in', pause_cycles)

        time_ns = get_sim_time('ns')
        self.log.info(f"Systematic counter test completed @ {time_ns}ns")

    async def run_counter_timeout_sweep_test(self):
        """Test wakeup assertion around counter timeout with randomization"""
        time_ns = get_sim_time('ns')
        self.log.info("=== Scenario CLK-04: Counter timeout sweep ===")
        self.log.info(f"Starting counter timeout sweep test @ {time_ns}ns")

        timeout_value = self.get_random_idle_count()  # Use random timeout for sweep test
        self.dut.cfg_cg_enable.value = 1
        self.dut.cfg_cg_idle_count.value = timeout_value

        # Test wakeup assertions with random offsets
        for _ in range(8):  # Test multiple random scenarios
            offset = self.get_random_wake_offset()
            time_ns = get_sim_time('ns')
            msg = f"Testing wakeup at timeout {offset:+d} cycles @ {time_ns}ns"
            self.log.info(msg)

            # Start countdown
            self.dut.wakeup.value = 1
            initial_wait = self.get_random_wait_cycles()
            await self.wait_clocks('clk_in', initial_wait)
            self.dut.wakeup.value = 0

            # Wait until just before the test point
            if offset < 0:
                # For negative offsets, assert wakeup before timeout
                await self.wait_clocks('clk_in', timeout_value + offset - 1)
                self.dut.wakeup.value = 1
                await self.verify_clock_gating('random', True, f"Offset={offset}")
            else:
                # For zero or positive offsets, wait for timeout then assert wakeup
                await self.wait_for_counter_expiration(timeout_value, f"Offset={offset}")
                # For positive offsets, wait additional cycles after timeout
                if offset > 0:
                    # Verify clock is gated after timeout
                    await self.verify_clock_gating('random', False, f"Offset={offset} (gated)")
                    # Wait additional offset cycles
                    await self.wait_clocks('clk_in', offset - 1)
                # Assert wakeup and verify clock becomes enabled
                self.dut.wakeup.value = 1
                await self.verify_clock_gating('random', True, f"Offset={offset} (rewake)")

            # Cleanup with random timing
            self.dut.wakeup.value = 0
            cleanup_cycles = self.get_random_wait_cycles()
            await self.wait_clocks('clk_in', cleanup_cycles)

        time_ns = get_sim_time('ns')
        self.log.info(f"Counter timeout sweep test completed @ {time_ns}ns")

    async def run_edge_case_test(self):
        """Test additional edge cases with randomization"""
        time_ns = get_sim_time('ns')
        self.log.info("=== Scenario CLK-05: Edge case test ===")
        self.log.info(f"Starting edge case tests @ {time_ns}ns")

        # Test 1: Zero idle count behavior
        time_ns = get_sim_time('ns')
        self.log.info(f"Testing zero idle count @ {time_ns}ns")
        self.dut.cfg_cg_enable.value = 1
        self.dut.cfg_cg_idle_count.value = 0

        # First, make sure clock is running with wake=1
        self.dut.wakeup.value = 1
        await self.verify_clock_gating('random', True, "Zero count, wake=1")

        # Then, deassert wake and check immediate gating behavior
        self.log.info("Zero count: expecting immediate gating when wake deasserted")
        self.dut.wakeup.value = 0
        
        # With zero count, gating should happen immediately - wait for it to settle
        await self.wait_clocks('clk_in', 2)
        await self.verify_clock_gating('random', False, "Zero count, wake=0")

        # Test 2: Rapid wake toggles with minimum idle count
        time_ns = get_sim_time('ns')
        self.log.info(f"Testing rapid toggles with min idle count @ {time_ns}ns")
        self.dut.cfg_cg_idle_count.value = 1

        # Random number of toggle iterations
        toggle_count = random.randint(3, 8)
        for i in range(toggle_count):
            time_ns = get_sim_time('ns')
            self.log.debug(f"Toggle {i} @ {time_ns}ns")

            # Assert wake, verify clock enabled
            self.dut.wakeup.value = 1
            await self.verify_clock_gating(1, True, f"Toggle {i}, wake=1")

            # Deassert wake, verify clock stays enabled for 1 cycle
            self.dut.wakeup.value = 0
            await self.verify_clock_gating(1, True, f"Toggle {i}, wake=0, counting")

            # Wait one more cycle and verify clock gating
            await self.wait_clocks('clk_in', 1)
            await self.verify_clock_gating(1, False, f"Toggle {i}, wake=0, gated")

        time_ns = get_sim_time('ns')
        self.log.info(f"Edge case tests completed @ {time_ns}ns")

    async def run_global_enable_test(self):
        """Test global enable/disable functionality with randomization"""
        time_ns = get_sim_time('ns')
        self.log.info("=== Scenario CLK-06: Global enable test ===")
        self.log.info(f"Starting global enable test @ {time_ns}ns")

        # Verify clock enabled when global enable is off
        self.dut.cfg_cg_enable.value = 0
        self.dut.wakeup.value = 0
        await self.verify_clock_gating('random', True, "Enable=0")

        # Configure idle count with global enable OFF (use random value but avoid 0)
        test_count = self.get_random_idle_count()
        if test_count == 0:
            test_count = 1  # Use minimum meaningful count for this test
            
        self.log.info(f"Using test_count={test_count} for global enable test")
        self.dut.cfg_cg_idle_count.value = test_count
        settle_cycles = self.get_random_wait_cycles()
        await self.wait_clocks('clk_in', settle_cycles)  # Wait for value to settle

        # Verify wake still works when global enable is on
        self.dut.cfg_cg_enable.value = 1
        self.dut.wakeup.value = 1
        await self.verify_clock_gating('random', True, "Enable=1, Wake=1")

        # Turn off wake signal to start countdown
        self.dut.wakeup.value = 0

        # Verify clock remains enabled during early countdown
        if test_count > 3:
            countdown_verify = min(test_count // 3, 5)  # Check early countdown only
            await self.verify_clock_gating(countdown_verify, True, "Enable=1, During Countdown")

        # Wait for counter to fully expire
        await self.wait_for_counter_expiration(test_count, "Global enable test")

        # Now verify the clock is gated after counter expires
        await self.verify_clock_gating('random', False, "Enable=1, After Expiration")

        # Verify clock immediately enabled when global enable turned off
        self.dut.cfg_cg_enable.value = 0
        await self.verify_clock_gating('random', True, "Enable=0 after gating")

        time_ns = get_sim_time('ns')
        self.log.info(f"Global enable test completed @ {time_ns}ns")

    async def run_randomized_stress_test(self):
        """Run additional randomized stress test scenarios"""
        time_ns = get_sim_time('ns')
        self.log.info("=== Scenario CLK-07: Randomized stress test ===")
        self.log.info(f"Starting randomized stress test @ {time_ns}ns")

        # Perform multiple iterations with random configurations
        stress_iterations = random.randint(5, 10)
        
        for iteration in range(stress_iterations):
            self.log.info(f"Stress iteration {iteration + 1}/{stress_iterations}")
            
            # Random configuration - demonstrate both boolean approaches
            if iteration % 2 == 0:
                enable_state = self.get_random_enable_choice()  # Object bin approach
            else:
                enable_state = self.get_random_enable_int()     # Integer approach
            
            idle_count = self.get_random_idle_count()
            
            self.dut.cfg_cg_enable.value = int(enable_state)
            self.dut.cfg_cg_idle_count.value = idle_count
            
            # Random sequence of wake assertions
            wake_sequence_length = random.randint(3, 8)
            for wake_step in range(wake_sequence_length):
                wake_state = random.choice([0, 1])
                self.dut.wakeup.value = wake_state
                
                wait_time = self.get_random_wait_cycles()
                await self.wait_clocks('clk_in', wait_time)
                
                # Verify clock state based on configuration
                if enable_state:
                    # When clock gating is enabled, behavior depends on wake and counter
                    if wake_state:
                        expected_enabled = True
                    else:
                        # Clock state depends on whether counter has expired
                        # For simplicity in stress test, just log the state
                        current_clk = int(self.dut.clk_out.value)
                        self.log.debug(f"Iteration {iteration}, step {wake_step}: "
                                     f"wake={wake_state}, clk_out={current_clk}")
                else:
                    # When clock gating is disabled, clock should always be enabled
                    expected_enabled = True
                    await self.verify_clock_gating(2, expected_enabled, 
                                                 f"Stress iter {iteration}, step {wake_step}")

        time_ns = get_sim_time('ns')
        self.log.info(f"Randomized stress test completed @ {time_ns}ns")

    async def monitor_clock_output(self):
        """Monitor clock output and log transitions"""
        prev_clk = 0
        edges_count = 0

        while True:
            await self.wait_clocks('clk_in', 1)
            curr_clk = int(self.dut.clk_out.value)

            if prev_clk != curr_clk:
                edges_count += 1
                time_ns = get_sim_time('ns')
                msg = f"Clock output changed to {curr_clk} at edge {edges_count} @ {time_ns}ns"
                self.log.debug(msg)

            prev_clk = curr_clk

    async def monitor_idle_counter(self):
        """Monitor idle counter value for debugging"""
        prev_count = 0

        while True:
            await self.wait_clocks('clk_in', 1)
            curr_count = int(self.dut.r_idle_counter.value)

            if prev_count != curr_count:
                time_ns = get_sim_time('ns')
                msg = f"Idle counter changed to 0x{curr_count:X} @ {time_ns}ns"
                self.log.debug(msg)

            prev_count = curr_count

    async def run_test(self):
        """Run all test sequences with randomization"""
        # Start monitoring functions
        cocotb.start_soon(self.monitor_clock_output())
        cocotb.start_soon(self.monitor_idle_counter())

        # Log randomizer state for debugging
        self.log.info(f"FlexRandomizer configuration: {self.randomizer}")

        # Run all test sequences
        await self.run_systematic_enable_test()
        await self.run_concurrent_wake_test()
        await self.run_systematic_counter_test()
        await self.run_counter_timeout_sweep_test()
        await self.run_edge_case_test()
        await self.run_global_enable_test()
        await self.run_randomized_stress_test()

        # Wait for any pending operations
        final_wait = self.get_random_wait_cycles()
        await self.wait_clocks('clk_in', final_wait)

        time_ns = get_sim_time('ns')
        self.log.info(f"All test sequences completed successfully @ {time_ns}ns")

@cocotb.test(timeout_time=2, timeout_unit="ms")  # Increased timeout for randomized tests
async def clock_gate_ctrl_test(dut):
    """Test the clock gate control block with FlexRandomizer"""
    tb = ClockGateCtrlTB(dut)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    msg = f'Using seed: {seed}'
    tb.log.info(msg)

    # Start the clock
    await tb.start_clock('clk_in', 10, 'ns')

    # Reset the DUT
    await tb.reset_dut()

    try:
        # Run all test sequences
        time_ns = get_sim_time('ns')
        tb.log.info(f"=== Starting clock gate controller tests with FlexRandomizer @ {time_ns}ns ===")
        await tb.run_test()

        time_ns = get_sim_time('ns')
        tb.log.info(f"All tests completed successfully @ {time_ns}ns")

    except AssertionError as e:
        tb.log.error(f"Test failed: {str(e)}")
        raise
    finally:
        # Wait for any pending tasks
        await tb.wait_clocks('clk_in', 10)

def generate_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (4-bit)
    REG_LEVEL=FUNC: 2 tests (4, 8-bit) - default
    REG_LEVEL=FULL: 2 tests (same as FUNC)

    Returns:
        List of counter widths
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [4]
    else:  # FUNC or FULL (same for this test)
        return [4, 8]

@pytest.mark.parametrize("counter_width", generate_test_params())
def test_clock_gate_ctrl(request, counter_width):
    """Run the test with pytest"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths(
        {
            'rtl_cmn': 'rtl/common'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "clock_gate_ctrl"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/clock_gate_ctrl.f'
    )

    # Create a human readable test identifier
    n_str = TBBase.format_dec(counter_width, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_n{n_str}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # RTL parameters
    parameters = {'IDLE_CNTR_WIDTH': counter_width}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',  # Enable tracing
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    # Add parameter values to environment variables
    # sourcery skip: no-loop-in-tests
    for k, v in parameters.items():
        extra_env[f'PARAM_{k}'] = str(v)

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    sim_args = [
                "--trace",  # Tell Verilator to use FST
                "--trace-structs",
                "--trace-depth", "99",
    ]

    plusargs = [
        "+trace",
    ]

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
            keep_files=True
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure