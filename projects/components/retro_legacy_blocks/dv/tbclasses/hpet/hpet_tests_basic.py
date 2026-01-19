# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETBasicTests
# Purpose: HPET Basic Tests
#
# Documentation: projects/components/apb_hpet/PRD.md
# Subsystem: apb_hpet
#
# Author: sean galloway
# Created: 2025-10-18

"""
HPET Basic Tests

Essential HPET functionality tests including:
- Register read/write access
- Main counter functionality
- Basic timer one-shot operation
- Interrupt generation and clearing
"""

import asyncio
from typing import Dict, List, Tuple
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import Timer

from .hpet_tb import HPETTB, HPETRegisterMap


class HPETBasicTests:
    """Basic HPET test suite."""

    def __init__(self, tb: HPETTB):
        self.tb = tb
        self.log = tb.log

    async def test_register_access(self) -> bool:
        """Test basic register read/write access."""
        self.log.info("=== Scenario HPET-01: Register Access ===")
        self.log.info(f"=== Testing HPET Register Access ({self.tb.NUM_TIMERS} timers) ===")
        self.tb.test_phase = "REGISTER_ACCESS"

        try:
            # Test ID register (read-only)
            _, id_value = await self.tb.read_register(HPETRegisterMap.HPET_ID)
            self.log.info(f"HPET ID: 0x{id_value:08X}")

            # Validate ID register shows correct timer count
            timer_count_field = (id_value >> 8) & 0x1F  # Bits 12:8
            expected_timer_count = self.tb.NUM_TIMERS - 1  # HW reports N-1
            if timer_count_field != expected_timer_count:
                self.log.error(f"ID register timer count mismatch: got {timer_count_field}, expected {expected_timer_count}")
                return False

            # Test configuration register
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)  # Disable
            _, config_value = await self.tb.read_register(HPETRegisterMap.HPET_CONFIG)

            if config_value & 0x1:
                self.log.error("HPET should be disabled after writing 0")
                return False

            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)  # Enable
            _, config_value = await self.tb.read_register(HPETRegisterMap.HPET_CONFIG)

            if not (config_value & 0x1):
                self.log.error("HPET should be enabled after writing 1")
                return False

            # Test timer configuration registers (all available timers)
            for timer_id in range(self.tb.NUM_TIMERS):
                config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
                await self.tb.write_register(config_addr, 0x00000000)  # Disable timer
                _, timer_config = await self.tb.read_register(config_addr)

                self.log.info(f"Timer {timer_id} config: 0x{timer_config:08X}")

            # Test status register
            _, status_value = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            self.log.info(f"HPET Status: 0x{status_value:08X}")

            await self.tb.wait_apb_idle()
            self.log.info("✓ Register access test passed")
            return True

        except Exception as e:
            self.log.error(f"Register access test failed: {e}")
            return False

    async def test_counter_functionality(self) -> bool:
        """Test main counter functionality."""
        self.log.info("=== Scenario HPET-02: Counter Enable/Disable ===")
        self.log.info("=== Scenario HPET-03: Counter Increment ===")
        self.log.info("=== Testing HPET Counter Functionality ===")
        self.tb.test_phase = "COUNTER_TEST"

        try:
            # Enable HPET
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Read initial counter value (low part)
            _, counter_low_1 = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)

            # Wait some HPET clock cycles
            await Timer(1000, units="ns")  # Wait 1us

            # Read counter again (low part)
            _, counter_low_2 = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)

            # Counter should have incremented
            if counter_low_2 <= counter_low_1:
                self.log.error(f"Counter did not increment: {counter_low_1} -> {counter_low_2}")
                return False

            increment = counter_low_2 - counter_low_1
            expected_min = 1000 // self.tb.HPET_CLOCK_PERIOD  # Approximate expected increment

            self.log.info(f"Counter increment: {increment} (expected ~{expected_min})")

            # Test counter write (low part)
            test_value = 0x12345678
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, test_value)
            _, readback = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)

            # Allow for small increment due to write delay
            if abs(readback - test_value) > 100:
                self.log.error(f"Counter write failed: wrote {test_value:08X}, read {readback:08X}")
                return False

            # Test high counter register (counter is always 64-bit)
            test_value_hi = 0x87654321
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, test_value_hi)
            _, readback_hi = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_HI)

            if abs(readback_hi - test_value_hi) > 10:  # Allow for small increment
                self.log.error(f"Counter HI write failed: wrote {test_value_hi:08X}, read {readback_hi:08X}")
                return False

            await self.tb.wait_apb_idle()
            self.log.info("✓ Counter functionality test passed")
            return True

        except Exception as e:
            self.log.error(f"Counter functionality test failed: {e}")
            return False

    async def test_timer_one_shot(self, timer_id: int = 0) -> bool:
        """Test one-shot timer functionality."""
        if timer_id >= self.tb.NUM_TIMERS:
            self.log.warning(f"Timer {timer_id} not available (only {self.tb.NUM_TIMERS} timers)")
            return True  # Skip test, don't fail

        self.log.info("=== Scenario HPET-04: Single Timer One-Shot ===")
        self.log.info(f"=== Testing Timer {timer_id} One-Shot Mode{self.tb.get_time_ns_str()} ===")
        self.tb.test_phase = f"TIMER_{timer_id}_ONE_SHOT"

        try:
            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Reset counter to known value
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Configure timer for one-shot mode
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (0 << HPETRegisterMap.TIMER_TYPE)  # One-shot

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

            # Set comparator to fire after 1000 HPET clock cycles
            compare_value = 1000
            await self.tb.write_register(comp_lo_addr, compare_value)
            await self.tb.write_register(comp_hi_addr, 0x00000000)

            # Enable timer
            await self.tb.write_register(config_addr, timer_config)

            # NOW enable HPET to start counting
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Wait for interrupt
            start_time = get_sim_time('ns')
            interrupt_occurred = False

            # Monitor for interrupt with timeout
            timeout_ns = self.tb.INTERRUPT_TIMEOUT
            self.log.info(f"DEBUG: Starting interrupt wait at {start_time}ns, timeout={timeout_ns}ns, will wait until {start_time + timeout_ns}ns")
            while (get_sim_time('ns') - start_time) < timeout_ns:
                if self.tb.timer_interrupt_state[timer_id]:
                    interrupt_occurred = True
                    interrupt_time = get_sim_time('ns') - start_time
                    self.log.info(f"Timer {timer_id} one-shot interrupt after {interrupt_time} ns{self.tb.get_time_ns_str()}")
                    break
                await Timer(10, units="ns")

            if not interrupt_occurred:
                end_time = get_sim_time('ns')
                self.log.error(f"Timer {timer_id} one-shot interrupt timeout at {end_time}ns (waited {end_time - start_time}ns)")
                return False

            # Clear interrupt
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

            # Verify interrupt clears
            clear_timeout = 100  # ns
            clear_start = get_sim_time('ns')
            while (get_sim_time('ns') - clear_start) < clear_timeout:
                if not self.tb.timer_interrupt_state[timer_id]:
                    break
                await Timer(5, units="ns")

            if self.tb.timer_interrupt_state[timer_id]:
                self.log.warning(f"Timer {timer_id} interrupt did not clear promptly")

            await self.tb.wait_apb_idle()
            self.log.info(f"✓ Timer {timer_id} one-shot test passed{self.tb.get_time_ns_str()}")
            return True

        except Exception as e:
            self.log.error(f"Timer {timer_id} one-shot test failed: {e}")
            return False

    async def test_interrupt_clearing(self) -> bool:
        """Test interrupt status and clearing mechanisms."""
        self.log.info("=== Scenario HPET-06: Interrupt Status Read ===")
        self.log.info("=== Scenario HPET-07: Interrupt Clear (W1C) ===")
        self.log.info("=== Testing Interrupt Clearing ===")
        self.tb.test_phase = "INTERRUPT_CLEARING"

        try:
            # Use first available timer
            timer_id = 0

            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Reset counter
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Configure timer for quick interrupt
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (0 << HPETRegisterMap.TIMER_TYPE)  # One-shot

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

            await self.tb.write_register(comp_lo_addr, 100)  # Quick fire
            await self.tb.write_register(comp_hi_addr, 0x00000000)
            await self.tb.write_register(config_addr, timer_config)

            # NOW enable HPET to start counting
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Wait for interrupt
            await Timer(2000, units="ns")

            # Check status register
            _, status_before = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if not (status_before & (1 << timer_id)):
                self.log.error("Interrupt status bit not set")
                return False

            # Clear specific interrupt
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

            # Check status after clear
            await Timer(100, units="ns")
            _, status_after = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if status_after & (1 << timer_id):
                self.log.error("Interrupt status bit not cleared")
                return False

            self.log.info("✓ Interrupt clearing test passed")
            return True

        except Exception as e:
            self.log.error(f"Interrupt clearing test failed: {e}")
            return False

    async def run_all_basic_tests(self) -> bool:
        """Run all basic tests."""
        self.log.info("=== Scenario HPET-07: Interrupt Clear (W1C) ===")
        self.log.info("=== Scenario HPET-04: Single Timer One-Shot ===")
        self.log.info("=== Scenario HPET-02: Counter Enable/Disable ===")
        self.log.info(f"=== Running All Basic HPET Tests ({self.tb.NUM_TIMERS} timers) ===")

        tests = [
            ("Register Access", self.test_register_access()),
            ("Counter Functionality", self.test_counter_functionality()),
            ("Timer 0 One-Shot", self.test_timer_one_shot(0)),
            ("Interrupt Clearing", self.test_interrupt_clearing()),
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

        self.log.info(f"Basic tests summary: {passed}/{total} passed")
        return success
