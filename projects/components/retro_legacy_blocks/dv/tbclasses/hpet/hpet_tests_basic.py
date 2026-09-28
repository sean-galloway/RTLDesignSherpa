# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETBasicTests
# Purpose: HPET Basic Tests
#
# Documentation: projects/components/apb4_hpet/PRD.md
# Subsystem: apb4_hpet
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
            self.log.info("Register access test passed")
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
            self.log.info("Counter functionality test passed")
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
            timer_config = (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
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
            self.log.info(f"Timer {timer_id} one-shot test passed{self.tb.get_time_ns_str()}")
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
            timer_config = (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
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

            self.log.info("Interrupt clearing test passed")
            return True

        except Exception as e:
            self.log.error(f"Interrupt clearing test failed: {e}")
            return False

    async def test_spec_register_layout(self) -> bool:
        """RLB/hpet TASK-006: the register interface must match the published spec.

        Asserts the fields that MOVED, which is the point -- test_register_access
        checks num_tim_cap[12:8], the one field whose position did not change, so
        it would pass against either layout and proves nothing here.

        GCAP_ID[31:0] (HPET_ID, 0x000):
            [31:16] vendor_id        full 16 bits, not the old truncated byte
            [15]    leg_rt_cap       1 -- LegacyReplacement Route implemented
                                     (RLB/hpet TASK-003). Drivers GATE on this
                                     bit, so its position is load-bearing
            [13]    count_size_cap   1 -- 64-bit counter
            [12:8]  num_tim_cap      NUM_TIMERS-1
            [7:0]   rev_id
        GCAP_ID[63:32] (HPET_PERIOD, 0x004): femtoseconds per tick, which must
        equal the clock the counter actually ticks on.
        TN_CONF: per_int_cap[4] and size_cap[5] are READ-ONLY 1; fsb_int_del_cap
        [15] is READ-ONLY 0 (no message delivery, so no FSB route registers).
        """
        self.log.info("=== RLB/hpet TASK-006: published-spec register layout ===")
        self.tb.test_phase = "SPEC_REGISTER_LAYOUT"

        # HALT THE COUNTER for the whole test. Everything here is a register
        # read plus one read-only probe, so nothing needs the counter running --
        # and the probe below writes 0xFFFFFFFF to TN_CONF, which SETS
        # INT_ENB[2] and TYPE[3]. On a running counter that arms a PERIODIC
        # timer against whatever comparator the previous test left behind, and
        # it fires after this test ends, leaving the scoreboard with an
        # unmatched assert. Writing TN_CONF = 0 afterwards does NOT stop it:
        # RLB/hpet TASK-006 removed the per-timer enable, so the only stop is
        # hpet_enable. Halting here removes the hazard at its source.
        await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

        try:
            passed = True

            _, id_value = await self.tb.read_register(HPETRegisterMap.HPET_ID)
            vendor = (id_value >> 16) & 0xFFFF
            leg_rt = (id_value >> 15) & 0x1
            cnt_sz = (id_value >> 13) & 0x1
            ntim   = (id_value >> 8) & 0x1F
            rev    = id_value & 0xFF
            self.log.info(f"HPET_ID = 0x{id_value:08X}: vendor=0x{vendor:04X} "
                          f"leg_rt_cap={leg_rt} count_size_cap={cnt_sz} "
                          f"num_tim_cap={ntim} rev_id=0x{rev:02X}")

            if vendor != (self.tb.VENDOR_ID & 0xFFFF):
                self.log.error(f"vendor_id[31:16] = 0x{vendor:04X}, expected "
                               f"0x{self.tb.VENDOR_ID & 0xFFFF:04X} -- the spec field "
                               "is 16 bits; a truncated byte means the old layout")
                passed = False
            if rev != (self.tb.REVISION_ID & 0xFF):
                self.log.error(f"rev_id[7:0] = 0x{rev:02X}, expected "
                               f"0x{self.tb.REVISION_ID & 0xFF:02X}")
                passed = False
            if ntim != self.tb.NUM_TIMERS - 1:
                self.log.error(f"num_tim_cap = {ntim}, expected {self.tb.NUM_TIMERS - 1}")
                passed = False
            if cnt_sz != 1:
                self.log.error(f"count_size_cap[13] = {cnt_sz}, expected 1 "
                               "(64-bit counter)")
                passed = False
            if leg_rt != 1:
                self.log.error(f"leg_rt_cap[15] = {leg_rt}, expected 1 -- "
                               "RLB/hpet TASK-003 implemented the "
                               "LegacyReplacement Route, and a driver that "
                               "reads 0 here will never use legacy mode")
                passed = False

            _, period = await self.tb.read_register(HPETRegisterMap.HPET_PERIOD)
            self.log.info(f"HPET_PERIOD = {period} fs "
                          f"(expected {self.tb.COUNTER_CLK_PERIOD_FS}, "
                          f"core clock {self.tb.CORE_CLOCK_PERIOD} ns)")
            if period != self.tb.COUNTER_CLK_PERIOD_FS:
                self.log.error(f"HPET_PERIOD = {period}, expected "
                               f"{self.tb.COUNTER_CLK_PERIOD_FS} fs")
                passed = False
            if period == 0 or period > 0x05F5E100:
                self.log.error(f"HPET_PERIOD = {period} violates the spec bounds "
                               "(non-zero, <= 0x05F5E100 = 100 ns)")
                passed = False
            if period != self.tb.CORE_CLOCK_PERIOD * 1_000_000:
                self.log.error(f"HPET_PERIOD {period} fs does not match the clock "
                               f"the counter ticks on ({self.tb.CORE_CLOCK_PERIOD} ns "
                               f"= {self.tb.CORE_CLOCK_PERIOD * 1_000_000} fs)")
                passed = False

            cfg_addr = HPETRegisterMap.get_timer_config_addr(0)
            _, tn_conf = await self.tb.read_register(cfg_addr)
            per_cap = (tn_conf >> HPETRegisterMap.TIMER_PER_INT_CAP) & 0x1
            sz_cap  = (tn_conf >> HPETRegisterMap.TIMER_SIZE_CAP) & 0x1
            fsb_cap = (tn_conf >> HPETRegisterMap.TIMER_FSB_CAP) & 0x1
            self.log.info(f"TIMER0 TN_CONF = 0x{tn_conf:08X}: per_int_cap={per_cap} "
                          f"size_cap={sz_cap} fsb_int_del_cap={fsb_cap}")
            if per_cap != 1:
                self.log.error(f"per_int_cap[4] = {per_cap}, expected 1 "
                               "(periodic mode is implemented)")
                passed = False
            if sz_cap != 1:
                self.log.error(f"size_cap[5] = {sz_cap}, expected 1 (64-bit capable)")
                passed = False
            if fsb_cap != 0:
                self.log.error(f"fsb_int_del_cap[15] = {fsb_cap}, expected 0 "
                               "(no message delivery)")
                passed = False

            # The capability bits are READ-ONLY: writing them must not stick.
            await self.tb.write_register(cfg_addr, 0xFFFFFFFF)
            _, after = await self.tb.read_register(cfg_addr)
            if ((after >> HPETRegisterMap.TIMER_PER_INT_CAP) & 0x1) != 1 or \
               ((after >> HPETRegisterMap.TIMER_SIZE_CAP) & 0x1) != 1 or \
               ((after >> HPETRegisterMap.TIMER_FSB_CAP) & 0x1) != 0:
                self.log.error(f"after writing 0xFFFFFFFF, TN_CONF = 0x{after:08X}: "
                               "a read-only capability bit changed")
                passed = False
            await self.tb.write_register(cfg_addr, 0x00000000)

            _, route_cap = await self.tb.read_register(
                HPETRegisterMap.get_timer_int_route_cap_addr(0))
            if route_cap != 0:
                self.log.error(f"TIMER_INT_ROUTE_CAP = 0x{route_cap:08X}, expected 0 "
                               "-- general I/O APIC route selection is still not "
                               "implemented. This is INDEPENDENT of leg_rt_cap=1: "
                               "legacy replacement OVERRIDES timer_int_route for "
                               "timers 0/1 rather than selecting through it")
                passed = False

            # Leave the block quiescent: counter halted, every timer's config
            # cleared, status clear. The 0xFFFFFFFF probe above touched TIMER0's
            # TN_CONF, and a stale armed timer would corrupt whatever runs next.
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            for timer_id in range(self.tb.NUM_TIMERS):
                await self.tb.write_register(
                    HPETRegisterMap.get_timer_config_addr(timer_id), 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFF)

            if passed:
                self.log.info("PASS RLB/hpet TASK-006: register layout matches the spec")
            return passed

        except Exception as e:
            self.log.error(f"spec register layout test failed with exception: {e}")
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
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
            ("TASK-006 spec register layout", self.test_spec_register_layout()),
        ]

        results = []
        for test_name, test_coro in tests:
            self.log.info(f"Running {test_name}...")
            try:
                result = await test_coro
                results.append(result)
                self.tb.scoreboard.record_test(test_name, result)
                status = "PASS" if result else "FAIL"
                self.log.info(f"{test_name}: {status}")
            except Exception as e:
                self.log.error(f"{test_name} failed with exception: {e}")
                results.append(False)
                self.tb.scoreboard.record_test(test_name, False)

        passed = sum(results)
        total = len(results)
        success = all(results)

        self.log.info(f"Basic tests summary: {passed}/{total} passed")
        return success
