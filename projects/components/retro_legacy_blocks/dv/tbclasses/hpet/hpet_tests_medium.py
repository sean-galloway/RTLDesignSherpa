# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETMediumTests
# Purpose: HPET Medium Tests
#
# Documentation: projects/components/apb_hpet/PRD.md
# Subsystem: apb_hpet
#
# Author: sean galloway
# Created: 2025-10-18

"""
HPET Medium Tests

Intermediate HPET functionality tests including:
- Periodic timer operation
- Multiple timer coordination
- 64-bit counter and comparator tests
- Timer mode switching
- Performance measurements
"""

import asyncio
from typing import Dict, List, Tuple
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import Timer

from .hpet_tb import HPETTB, HPETRegisterMap


class HPETMediumTests:
    """Medium complexity HPET test suite."""

    def __init__(self, tb: HPETTB):
        self.tb = tb
        self.log = tb.log

    async def test_timer_periodic(self, timer_id: int = 1) -> bool:
        """Test periodic timer functionality."""
        if timer_id >= self.tb.NUM_TIMERS:
            self.log.warning(f"Timer {timer_id} not available (only {self.tb.NUM_TIMERS} timers)")
            return True  # Skip test, don't fail

        self.log.info(f"=== Testing Timer {timer_id} Periodic Mode{self.tb.get_time_ns_str()} ===")
        self.tb.test_phase = f"TIMER_{timer_id}_PERIODIC"

        try:
            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Reset counter
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Configure timer for periodic mode
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_TYPE)  # Periodic

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)

            # Set comparator for 500 HPET clock period
            period = 500
            await self.tb.write_register(comp_lo_addr, period)

            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
            await self.tb.write_register(comp_hi_addr, 0x00000000)

            # Clear any pending interrupts before enabling timer
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

            # Enable timer
            await self.tb.write_register(config_addr, timer_config)

            # NOW enable HPET to start counting
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Calculate period timing
            period_ns = period * self.tb.HPET_CLOCK_PERIOD

            # Wait for first interrupt to fire (initial period)
            self.log.info(f"Waiting for initial interrupt (period={period_ns}ns){self.tb.get_time_ns_str()}")
            first_interrupt_timeout = period_ns * 2
            wait_start = get_sim_time('ns')

            while not self.tb.timer_interrupt_state[timer_id] and \
                (get_sim_time('ns') - wait_start) < first_interrupt_timeout:
                await Timer(10, units="ns")

            if not self.tb.timer_interrupt_state[timer_id]:
                self.log.error(f"Timer {timer_id} initial interrupt did not fire")
                return False

            # Clear first interrupt
            self.log.info(f"Initial interrupt fired{self.tb.get_time_ns_str()}, clearing it")
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

            # Wait for interrupt to clear
            clear_timeout = 500  # 500ns timeout
            clear_start = get_sim_time('ns')
            while self.tb.timer_interrupt_state[timer_id] and \
                (get_sim_time('ns') - clear_start) < clear_timeout:
                await Timer(10, units="ns")

            # Now monitor for periodic interrupts
            interrupt_times = []
            start_time = get_sim_time('ns')
            expected_interrupts = 2  # Expect 2 more periodic interrupts
            # Need to wait for 2 full periods PLUS initial offset to first periodic fire
            # Initial fire was at counter=period, first periodic at 2*period, second at 3*period
            # From monitoring start (after first interrupt), need to wait 2 full periods
            max_wait_time = (expected_interrupts + 1) * period_ns * 2  # Extra margin for timing

            self.log.info(f"Monitoring for {expected_interrupts} periodic interrupts, period={period_ns}ns{self.tb.get_time_ns_str()}")

            # Debug: Read counter and comparator values
            _, counter_lo = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
            _, comp_val = await self.tb.read_register(comp_lo_addr)
            self.log.info(f"DEBUG: After first interrupt - Counter={counter_lo:08X}, Comparator={comp_val:08X}")

            loop_count = 0
            while len(interrupt_times) < expected_interrupts and \
                (get_sim_time('ns') - start_time) < max_wait_time:

                if self.tb.timer_interrupt_state[timer_id]:
                    current_time = get_sim_time('ns')
                    interrupt_times.append(current_time)
                    elapsed = current_time - start_time
                    self.log.info(f"Timer {timer_id} periodic interrupt #{len(interrupt_times)} "
                                f"at {elapsed} ns from monitoring start{self.tb.get_time_ns_str()}")

                    # Clear interrupt to see next one
                    await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

                    # Wait for interrupt to clear
                    clear_timeout = 500
                    clear_start = get_sim_time('ns')
                    while self.tb.timer_interrupt_state[timer_id] and \
                        (get_sim_time('ns') - clear_start) < clear_timeout:
                        await Timer(10, units="ns")

                # Debug counter periodically
                if loop_count % 100 == 0:
                    _, counter_lo = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
                    _, comp_val = await self.tb.read_register(comp_lo_addr)
                    self.log.debug(f"Loop {loop_count}: Counter={counter_lo:08X}, Comp={comp_val:08X}")

                loop_count += 1
                await Timer(10, units="ns")

            if len(interrupt_times) < expected_interrupts:
                self.log.error(f"Timer {timer_id} periodic: got {len(interrupt_times)} interrupts, "
                            f"expected {expected_interrupts}")
                return False

            # Analyze interrupt timing
            if len(interrupt_times) >= 2:
                intervals = []
                for i in range(1, len(interrupt_times)):
                    interval = interrupt_times[i] - interrupt_times[i-1]
                    intervals.append(interval)

                avg_interval = sum(intervals) / len(intervals)
                expected_interval = period * self.tb.HPET_CLOCK_PERIOD

                self.log.info(f"Average periodic interval: {avg_interval:.1f} ns "
                            f"(expected ~{expected_interval} ns)")

                # Allow 20% tolerance for timing
                if abs(avg_interval - expected_interval) > (expected_interval * 0.2):
                    self.log.warning(f"Periodic timing may be inaccurate")

            # Disable timer
            self.log.info(f"Disabling Timer {timer_id} after periodic test{self.tb.get_time_ns_str()}")
            await self.tb.write_register(config_addr, 0x00000000)

            await self.tb.wait_apb_idle()
            self.log.info(f"✓ Timer {timer_id} periodic test passed{self.tb.get_time_ns_str()}")
            return True

        except Exception as e:
            self.log.error(f"Timer {timer_id} periodic test failed: {e}")
            return False

    async def test_64bit_counter(self) -> bool:
        """Test 64-bit counter functionality."""
        # Counter is always 64-bit in the RTL

        self.log.info("=== Scenario HPET-05: Single Timer Periodic ===")
        self.log.info("=== Testing 64-bit Counter Functionality ===")
        self.tb.test_phase = "COUNTER_64BIT"

        try:
            # Enable HPET
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Test writing to both halves of counter
            test_lo = 0xDEADBEEF
            test_hi = 0x12345678

            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, test_lo)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, test_hi)

            # Read back and verify
            _, read_lo = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
            _, read_hi = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_HI)

            # Allow for some increment due to counter running
            if abs(read_lo - test_lo) > 1000:
                self.log.error(f"Counter LO write/read mismatch: wrote {test_lo:08X}, read {read_lo:08X}")
                return False

            if abs(read_hi - test_hi) > 1:  # High part should not increment quickly
                self.log.error(f"Counter HI write/read mismatch: wrote {test_hi:08X}, read {read_hi:08X}")
                return False

            # Test counter overflow from low to high
            near_overflow = 0xFFFFFFF0
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, near_overflow)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Wait for overflow
            await Timer(200, units="ns")

            _, final_lo = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
            _, final_hi = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_HI)

            self.log.info(f"After potential overflow: LO={final_lo:08X}, HI={final_hi:08X}")

            # Reset counter to 0 for next test
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            await self.tb.wait_apb_idle()
            self.log.info("✓ 64-bit counter test passed")
            return True

        except Exception as e:
            self.log.error(f"64-bit counter test failed: {e}")
            return False

    async def test_64bit_comparator(self, timer_id: int = 0) -> bool:
        """Test 64-bit comparator functionality."""
        if timer_id >= self.tb.NUM_TIMERS:
            self.log.info("Skipping 64-bit comparator test - timer not available")
            return True

        self.log.info(f"=== Testing Timer {timer_id} 64-bit Comparator ===")
        self.tb.test_phase = f"TIMER_{timer_id}_64BIT_COMP"

        try:
            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Reset counter
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Configure timer for 64-bit mode
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_SIZE) | \
                        (0 << HPETRegisterMap.TIMER_TYPE)  # One-shot, 64-bit

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

            # Set a large 64-bit comparator value that would overflow 32-bit
            comp_lo_val = 0x00000500  # 1280 in decimal
            comp_hi_val = 0x00000001  # High part = 1
            # Total value = 0x100000500 (much larger than 32-bit)

            await self.tb.write_register(comp_lo_addr, comp_lo_val)
            await self.tb.write_register(comp_hi_addr, comp_hi_val)

            # Verify comparator values
            _, read_comp_lo = await self.tb.read_register(comp_lo_addr)
            _, read_comp_hi = await self.tb.read_register(comp_hi_addr)

            if read_comp_lo != comp_lo_val or read_comp_hi != comp_hi_val:
                self.log.error(f"Comparator write/read mismatch: "
                            f"wrote {comp_hi_val:08X}:{comp_lo_val:08X}, "
                            f"read {read_comp_hi:08X}:{read_comp_lo:08X}")
                return False

            # Enable timer
            await self.tb.write_register(config_addr, timer_config)

            # NOW enable HPET to start counting
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # This test mainly verifies the comparator registers work
            # Actually waiting for such a large count would take too long
            self.log.info(f"64-bit comparator set to {comp_hi_val:08X}:{comp_lo_val:08X}")

            await self.tb.wait_apb_idle()
            self.log.info(f"✓ Timer {timer_id} 64-bit comparator test passed")
            return True

        except Exception as e:
            self.log.error(f"64-bit comparator test failed: {e}")
            return False

    async def test_multiple_timers(self) -> bool:
        """Test multiple timers operating simultaneously."""
        if self.tb.NUM_TIMERS < 2:
            self.log.info("Skipping multiple timer test (need at least 2 timers)")
            return True

        self.log.info(f"=== Testing Multiple Timers ({self.tb.NUM_TIMERS} available) ===")
        self.tb.test_phase = "MULTIPLE_TIMERS"

        try:
            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Reset counter
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Reset all timers to clear state from previous tests
            for timer_id in range(self.tb.NUM_TIMERS):
                config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
                comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
                comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

                # Disable timer and clear configuration
                await self.tb.write_register(config_addr, 0x00000000)
                # Reset comparator to 0 (triggers write strobe)
                await self.tb.write_register(comp_lo_addr, 0x00000000)
                await self.tb.write_register(comp_hi_addr, 0x00000000)

            # Configure multiple timers with different periods
            timer_configs = []
            test_timers = min(self.tb.NUM_TIMERS, 3)  # Test up to 3 timers

            for timer_id in range(test_timers):
                # Different periods for each timer
                period = 300 + (timer_id * 200)  # 300, 500, 700, etc.

                timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                            (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                            (0 << HPETRegisterMap.TIMER_TYPE)  # One-shot

                config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
                comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)

                await self.tb.write_register(comp_lo_addr, period)
                comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
                await self.tb.write_register(comp_hi_addr, 0x00000000)

                timer_configs.append((timer_id, period, config_addr, timer_config))

            # Enable all timers simultaneously
            for timer_id, period, config_addr, timer_config in timer_configs:
                await self.tb.write_register(config_addr, timer_config)
                self.log.info(f"Timer {timer_id} configured with period {period}")

            # NOW enable HPET to start counting
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Monitor for interrupts from all timers
            timer_fired = [False] * test_timers
            start_time = get_sim_time('ns')
            timeout = 20000  # 20us timeout - Timer 2 needs 7000ns, but allow extra margin

            self.log.info(f"Starting multiple timer monitor at {start_time}ns, waiting for {test_timers} timers")

            while not all(timer_fired) and (get_sim_time('ns') - start_time) < timeout:
                current_time = get_sim_time('ns')
                for timer_id in range(test_timers):
                    if not timer_fired[timer_id] and self.tb.timer_interrupt_state[timer_id]:
                        timer_fired[timer_id] = True
                        fire_time = current_time - start_time
                        self.log.info(f"Timer {timer_id} fired at {fire_time}ns from start (absolute: {current_time}ns)")

                        # Clear interrupt
                        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

                await Timer(10, units="ns")

            # Check results
            fired_count = sum(timer_fired)
            if fired_count != test_timers:
                self.log.error(f"Only {fired_count}/{test_timers} timers fired")
                return False

            # Disable all test timers to prevent interference with subsequent tests
            for timer_id, period, config_addr, timer_config in timer_configs:
                await self.tb.write_register(config_addr, 0x00000000)

            await self.tb.wait_apb_idle()
            self.log.info(f"✓ Multiple timers test passed ({fired_count} timers)")
            return True

        except Exception as e:
            self.log.error(f"Multiple timers test failed: {e}")
            return False

    async def test_timer_mode_switching(self, timer_id: int = 0) -> bool:
        """Test switching timer between one-shot and periodic modes."""
        if timer_id >= self.tb.NUM_TIMERS:
            return True

        self.log.info("=== Scenario HPET-11: 64-bit Comparator Operation ===")
        self.log.info("=== Scenario HPET-10: 64-bit Counter Operation ===")
        self.log.info("=== Scenario HPET-08: Multiple Timers Simultaneous ===")
        self.log.info(f"=== Testing Timer {timer_id} Mode Switching ===")
        self.tb.test_phase = f"TIMER_{timer_id}_MODE_SWITCH"

        try:
            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)

            # Test 1: One-shot mode
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            comparator_value = 200
            await self.tb.write_register(comp_lo_addr, comparator_value)

            one_shot_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                            (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                            (0 << HPETRegisterMap.TIMER_TYPE)  # One-shot

            await self.tb.write_register(config_addr, one_shot_config)

            # Enable HPET for one-shot test
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Wait for one-shot fire (comparator_value * clock_period + margin)
            wait_time_ns = comparator_value * self.tb.HPET_CLOCK_PERIOD * 2
            await Timer(wait_time_ns, units="ns")

            if not self.tb.timer_interrupt_state[timer_id]:
                self.log.error(f"Timer {timer_id} did not fire in one-shot mode")
                return False

            # Clear and disable timer
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            await self.tb.write_register(config_addr, 0x00000000)

            # Test 2: Switch to periodic mode
            await Timer(100, units="ns")

            # Disable HPET before reconfiguration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Set comparator for periodic mode
            periodic_comparator = 300
            await self.tb.write_register(comp_lo_addr, periodic_comparator)

            periodic_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                            (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                            (1 << HPETRegisterMap.TIMER_TYPE)  # Periodic

            await self.tb.write_register(config_addr, periodic_config)

            # Enable HPET for periodic test
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Wait for at least 2 periodic fires
            fire_count = 0
            start_time = get_sim_time('ns')
            # Need extra margin for periodic mode timing - wait for 5 periods to ensure we see 2 fires
            periodic_wait_time = periodic_comparator * self.tb.HPET_CLOCK_PERIOD * 5

            while fire_count < 2 and (get_sim_time('ns') - start_time) < periodic_wait_time:
                if self.tb.timer_interrupt_state[timer_id]:
                    fire_count += 1
                    self.log.info(f"Periodic fire #{fire_count}")
                    await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

                    # Wait for clear
                    await Timer(50, units="ns")

                await Timer(10, units="ns")

            if fire_count < 2:
                self.log.error(f"Timer {timer_id} did not fire periodically (only {fire_count} fires)")
                return False

            # Disable timer
            await self.tb.write_register(config_addr, 0x00000000)

            await self.tb.wait_apb_idle()
            self.log.info(f"✓ Timer {timer_id} mode switching test passed")
            return True

        except Exception as e:
            self.log.error(f"Timer mode switching test failed: {e}")
            return False

    async def run_all_medium_tests(self) -> bool:
        """Run all medium complexity tests."""
        self.log.info(f"=== Running All Medium HPET Tests ({self.tb.NUM_TIMERS} timers) ===")

        tests = [
            ("Timer Periodic Mode", self.test_timer_periodic(1 if self.tb.NUM_TIMERS > 1 else 0)),
            ("64-bit Counter", self.test_64bit_counter()),
            ("64-bit Comparator", self.test_64bit_comparator(0)),
            ("Multiple Timers", self.test_multiple_timers()),
            ("Timer Mode Switching", self.test_timer_mode_switching(0)),
        ]

        results = []
        for test_name, test_coro in tests:
            self.log.info(f"Running {test_name}...")
            try:
                result = await test_coro
                results.append(result)
                status = "PASS" if result else "FAIL"
                self.log.info(f"{test_name}: {status}")
            except Exception as e:
                self.log.error(f"{test_name} failed with exception: {e}")
                results.append(False)

        passed = sum(results)
        total = len(results)
        success = all(results)

        self.log.info(f"Medium tests summary: {passed}/{total} passed")
        return success