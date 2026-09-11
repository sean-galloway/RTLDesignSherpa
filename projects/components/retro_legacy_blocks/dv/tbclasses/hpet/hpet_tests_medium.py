# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETMediumTests
# Purpose: HPET Medium Tests
#
# Documentation: projects/components/apb4_hpet/PRD.md
# Subsystem: apb4_hpet
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


Provenance: these were written TEST-FIRST against the unfixed RTL for
issue #46 -- the commit that landed the fix (32be0cefc) records that
twelve new tests were RED on the old RTL. A defect-regression test nobody
saw fail is decoration, so the evidence is recorded here rather than
left in a commit message nobody re-reads (RLB-006).
"""

import asyncio
from typing import Dict, List, Tuple
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import Timer, ClockCycles, RisingEdge

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

    # ========================================================================
    # Helpers shared by the issue #46 defect tests below
    # ========================================================================

    async def _configure_one_shot(self, timer_id: int, comparator: int,
                                    periodic: bool = False, int_enable: bool = True) -> None:
        """Arm timer_id as one-shot (or periodic) with the given comparator.
        Does NOT touch HPET_CONFIG.hpet_enable or the main counter."""
        config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
        comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
        comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

        await self.tb.write_register(comp_lo_addr, comparator & 0xFFFFFFFF)
        await self.tb.write_register(comp_hi_addr, 0x00000000)

        timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                    ((1 << HPETRegisterMap.TIMER_INT_ENABLE) if int_enable else 0) | \
                    ((1 << HPETRegisterMap.TIMER_TYPE) if periodic else 0)
        await self.tb.write_register(config_addr, timer_config)

    async def _wait_for_fire(self, timer_id: int, timeout_ns: int) -> bool:
        """Poll tb.timer_interrupt_state[timer_id] until it goes True or timeout."""
        start = get_sim_time('ns')
        while (get_sim_time('ns') - start) < timeout_ns:
            if self.tb.timer_interrupt_state[timer_id]:
                return True
            await Timer(2, units="ns")
        return False

    async def _sample_fire_cycles(self, timer_id: int, num_cycles: int) -> List[int]:
        """Sample the internal one-cycle pulse dut.u_hpet_core.w_timer_fire[timer_id]
        on every CORE clock rising edge for num_cycles cycles, with NO register
        access in the loop. An APB HPET_STATUS W1C round trip is ~31 core clocks
        (write_register's multi-cycle handshake), which starves any fixed-length
        cadence window of more than one observation; w_timer_fire is unaffected
        by HPET_STATUS (it only gates timer_int_status/timer_irq), so sampling it
        directly measures the RTL's actual fire cadence instead of the test's own
        register-access latency.

        Picks the core clock per CDC_ENABLE (hpet_clk when CDC is on, pclk when
        it is off -- see HPETTB.CORE_CLOCK_PERIOD), matching hpet_core's actual
        clock in either configuration.

        Returns the 0-based cycle indices (relative to the first sampled edge,
        i.e. the edge immediately following the call) at which the pulse was
        observed high.
        """
        core_clk = self.tb.dut.hpet_clk if self.tb.CDC_ENABLE else self.tb.dut.pclk
        fire_bus = self.tb.dut.u_hpet_core.w_timer_fire
        fire_cycles: List[int] = []
        for cycle in range(num_cycles):
            await RisingEdge(core_clk)
            raw = fire_bus.value
            if raw is not None and ((int(raw) >> timer_id) & 1):
                fire_cycles.append(cycle)
        return fire_cycles

    async def _fresh_disabled_state(self) -> None:
        """Common pre-trial state: HPET disabled, counter at 0, all status
        clear. Per the block's own rule (CLAUDE.md 'Timer Cleanup is
        MANDATORY'), also used as end-of-test cleanup."""
        await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
        await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
        await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
        # HPET_STATUS.timer_int_status is a fixed [7:0] field in the
        # generated regblock regardless of NUM_TIMERS (issue #46 C2 can
        # spuriously set bits >= NUM_TIMERS), so clear the full byte here,
        # not just (1<<NUM_TIMERS)-1, or a phantom bit from that defect
        # leaks state into whatever test runs next.
        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFF)
        for timer_id in range(self.tb.NUM_TIMERS):
            await self.tb.write_register(HPETRegisterMap.get_timer_config_addr(timer_id), 0x00000000)

    # ========================================================================
    # issue #46 C1: HPET_STATUS W1C must be scoped per-bit
    # ========================================================================

    async def test_status_w1c_per_bit(self) -> bool:
        """issue #46 C1: a write to HPET_STATUS must clear ONLY the bits
        written as 1, and writing 0 must be a complete no-op.

        RTL today (hpet_config_regs.sv):
            timer_int_clear = {NUM_TIMERS{swmod}} & timer_int_status
        `swmod` pulses on ANY write to HPET_STATUS with a nonzero byte
        enable, regardless of wdata -- so it broadcasts a clear to every bit
        that is CURRENTLY pending in hpet_core, not just the bits selected
        by wdata. The PeakRDL register itself does the right per-bit
        `value & ~(wdata & biten)`, so the desync shows up as a lost
        `timer_irq` pulse on the untouched timer, not (necessarily) as a
        wrong HPET_STATUS readback -- this test checks both.

        Scenario: arm two one-shot timers so both fire and stay pending
        (status bits 0 and 1 both set, both timer_irq outputs high). Write
        HPET_STATUS=0x1 (clear timer 0 only) -- timer 1's status bit AND
        its timer_irq output must remain asserted. Then write
        HPET_STATUS=0x0 -- a legal W1C no-op -- and confirm nothing further
        changes.
        """
        if self.tb.NUM_TIMERS < 2:
            self.log.info("Skipping W1C per-bit test (need at least 2 timers)")
            return True

        self.log.info("=== issue #46 C1: HPET_STATUS W1C must be per-bit ===")
        self.tb.test_phase = "ISSUE46_C1_W1C_PER_BIT"

        try:
            await self._fresh_disabled_state()

            # Arm timer 0 and timer 1 to fire quickly and independently.
            await self._configure_one_shot(0, comparator=5)
            await self._configure_one_shot(1, comparator=8)

            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            timeout_ns = self.tb.CORE_CLOCK_PERIOD * 200
            if not await self._wait_for_fire(0, timeout_ns):
                self.log.error("Timer 0 did not fire (setup failure)")
                return False
            if not await self._wait_for_fire(1, timeout_ns):
                self.log.error("Timer 1 did not fire (setup failure)")
                return False

            await Timer(self.tb.CORE_CLOCK_PERIOD * 4, units="ns")

            _, status_before = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            irq_before = int(self.tb.dut.timer_irq.value)
            if status_before & 0x3 != 0x3 or irq_before & 0x3 != 0x3:
                self.log.error(f"Setup failure: status=0x{status_before:X} irq=0x{irq_before:X}, "
                                "expected both timer 0 and timer 1 pending")
                return False

            # Write 1 to bit 0 ONLY. Correct behavior: bit 0 clears, bit 1
            # (register AND core AND timer_irq[1]) must be untouched.
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0x1)
            await Timer(self.tb.CORE_CLOCK_PERIOD * 4, units="ns")

            _, status_after_w1 = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            irq_after_w1 = int(self.tb.dut.timer_irq.value)

            passed = True
            if status_after_w1 & 0x1:
                self.log.error(f"HPET_STATUS bit 0 did not clear: 0x{status_after_w1:X}")
                passed = False
            if not (status_after_w1 & 0x2):
                self.log.error(f"HPET_STATUS bit 1 was cleared by a write that only "
                                f"targeted bit 0 (0x{status_after_w1:X}) -- "
                                "issue #46 C1 broadcast-clear defect")
                passed = False
            if irq_after_w1 & 0x1:
                self.log.error(f"timer_irq[0] did not deassert: 0x{irq_after_w1:X}")
                passed = False
            if not (irq_after_w1 & 0x2):
                self.log.error(f"timer_irq[1] deasserted from a write that only "
                                f"targeted bit 0 (irq=0x{irq_after_w1:X}) -- "
                                "issue #46 C1 broadcast-clear defect")
                passed = False

            # Write 0x0: per W1C semantics this is a legal no-op. Nothing
            # about bit 1 / timer_irq[1] may change.
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0x0)
            await Timer(self.tb.CORE_CLOCK_PERIOD * 4, units="ns")

            _, status_after_w0 = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            irq_after_w0 = int(self.tb.dut.timer_irq.value)

            if status_after_w0 != status_after_w1:
                self.log.error(f"Write of 0x0 to HPET_STATUS changed the register: "
                                f"0x{status_after_w1:X} -> 0x{status_after_w0:X} "
                                "(W1C with wdata=0 must be a no-op)")
                passed = False
            if irq_after_w0 != irq_after_w1:
                self.log.error(f"Write of 0x0 to HPET_STATUS changed timer_irq: "
                                f"0x{irq_after_w1:X} -> 0x{irq_after_w0:X} "
                                "(W1C with wdata=0 must be a no-op)")
                passed = False

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 C1: HPET_STATUS W1C is per-bit")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 C1 test failed with exception: {e}")
            await self._fresh_disabled_state()
            return False

    # ========================================================================
    # issue #46 C2: hwset must be per-bit, never all-ones
    # ========================================================================

    async def test_status_hwset_per_bit(self) -> bool:
        """issue #46 C2: a second timer firing while an earlier timer's
        status bit is still pending must set ONLY that timer's bit, never
        the whole register.

        RTL today (hpet_regs.sv HPET_STATUS field combo, ~line 288):
            else if((value=='0) && (next!='0)) next_c = next;      // multi-bit sticky
            else if(hwset) next_c = '1;                             // HW Set
        The correct per-bit `next` (driven every cycle from hpet_core's live
        level, hpet_config_regs.sv) only gets loaded when the register is
        currently all-zero. If timer 0's bit is still set when timer 1
        fires, `value != '0`, so the `hwset` branch runs instead and loads
        8'hFF -- including bits above NUM_TIMERS-1, which have no
        corresponding core timer at all.

        Scenario: let timer 0 fire and leave it pending, then let timer 1
        fire. HPET_STATUS must read EXACTLY (1<<0)|(1<<1) -- no phantom
        bits anywhere in [7:0].
        """
        if self.tb.NUM_TIMERS < 2:
            self.log.info("Skipping hwset per-bit test (need at least 2 timers)")
            return True

        self.log.info("=== issue #46 C2: HPET_STATUS hwset must be per-bit ===")
        self.tb.test_phase = "ISSUE46_C2_HWSET_PER_BIT"

        try:
            await self._fresh_disabled_state()

            # Timer 0 fires first and is left pending (not cleared).
            await self._configure_one_shot(0, comparator=5)
            # Timer 1 fires later, while timer 0's status bit is still set.
            await self._configure_one_shot(1, comparator=40)

            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            timeout_ns = self.tb.CORE_CLOCK_PERIOD * 300
            if not await self._wait_for_fire(0, timeout_ns):
                self.log.error("Timer 0 did not fire (setup failure)")
                return False

            _, status_mid = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if not (status_mid & 0x1):
                self.log.error(f"Setup failure: timer 0 bit not pending (0x{status_mid:X})")
                return False

            if not await self._wait_for_fire(1, timeout_ns):
                self.log.error("Timer 1 did not fire")
                return False

            await Timer(self.tb.CORE_CLOCK_PERIOD * 4, units="ns")

            _, status_final = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            expected = 0x1 | 0x2
            passed = True
            if status_final != expected:
                self.log.error(f"HPET_STATUS = 0x{status_final:02X}, expected exactly "
                                f"0x{expected:02X} -- issue #46 C2 hwset-sets-all-bits defect "
                                f"(phantom bits: 0x{(status_final & ~expected) & 0xFF:02X})")
                passed = False

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 C2: HPET_STATUS hwset is per-bit")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 C2 test failed with exception: {e}")
            await self._fresh_disabled_state()
            return False

    # ========================================================================
    # issue #46 C3: 64-bit counter writes must apply atomically
    # ========================================================================

    async def test_counter_64bit_write_atomic(self) -> bool:
        """issue #46 C3: writing HPET_COUNTER_LO then HPET_COUNTER_HI with
        distinct nonzero values must land both halves in the main counter.

        RTL as flagged by the review (hpet_config_regs.sv ~206-235):
        `last_sw_counter_lo/hi` capture the written halves via non-blocking
        assignment on the SAME edge as the write; hpet_core (hpet_core.sv
        ~105) loads `counter_wdata = {last_sw_counter_hi, last_sw_counter_lo}`
        on that SAME edge, so a single-cycle write strobe would always see
        the halves as they were BEFORE this cycle's capture takes effect.

        EMPIRICAL NOTE (traced via internal signals during test development,
        removed from the final test below): through the ACTUAL integrated
        path, this defect does not reproduce. `peakrdl_to_cmdrsp.sv`
        (`projects/components/converters/rtl/`) asserts
        `regblk_req = (cmd_state==CMD_WAIT_ACK) || (cmd_state==CMD_IDLE &&
        cmd_valid)` -- every APB write is presented to the regblock for TWO
        consecutive clock cycles with identical (registered) data, not one.
        The first cycle reproduces the stale-capture race exactly as
        described; the second cycle re-issues the SAME write with
        `last_sw_counter_hi` now settled from the first cycle's
        non-blocking update, so the core's second load overwrites the bad
        one with the correct `{hi,lo}` before software ever reads it. This
        redundant hold is a property of the shared adapter (also used by
        every other register in this block and by other components), not
        something an HPET-level fix would touch, and it cannot be
        suppressed via any legal single-write APB sequence -- there is no
        stimulus reachable through the framework BFM that defeats it.

        This test is kept as a correctness assertion (it still documents
        the required behavior and will catch a regression if the adapter's
        redundant-assert property is ever changed), but per the DV
        methodology it is NOT counted as a red/green proof of issue #46 C3:
        it passes today, before any RTL fix, for a reason unrelated to
        correctness. See the run report for the mutation-check finding.
        """
        self.log.info("=== issue #46 C3: 64-bit counter write must be atomic ===")
        self.tb.test_phase = "ISSUE46_C3_COUNTER_ATOMIC"

        try:
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            test_lo = 0x11112222
            test_hi = 0x33334444

            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, test_lo)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, test_hi)
            await Timer(self.tb.CORE_CLOCK_PERIOD * 4, units="ns")

            _, read_lo = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
            _, read_hi = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_HI)

            passed = True
            if read_lo != test_lo:
                self.log.error(f"COUNTER_LO readback 0x{read_lo:08X} != written 0x{test_lo:08X}")
                passed = False
            if read_hi != test_hi:
                self.log.error(f"COUNTER_HI readback 0x{read_hi:08X} != written 0x{test_hi:08X} "
                                "-- issue #46 C3 stale-half defect (HI write dropped)")
                passed = False

            # Mandatory cleanup: reset the main counter to 0.
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            if passed:
                self.log.info("PASS issue #46 C3: 64-bit counter write is atomic")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 C3 test failed with exception: {e}")
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
            return False

    # ========================================================================
    # issue #46 round_2 H1: HPET_STATUS must read 0 immediately after reset
    # ========================================================================

    async def test_status_reset_value(self) -> bool:
        """issue #46 round_2 H1: HPET_STATUS.timer_int_status is the only
        field in generated hpet_regs.sv with no reset branch
        (field_storage.HPET_STATUS.timer_int_status is loaded only on
        `load_next`, never on `rst`). Per the MAS reset table the register
        must read 0 immediately out of reset.

        Deterministic construction: force HPET_STATUS to a KNOWN nonzero
        value first (by letting a real timer fire -- not by relying on
        whatever state a previous test happened to leave behind), THEN
        drive an independent reset pulse, THEN check the register reads 0.
        Because the field has no reset branch, its stored value is simply
        left untouched by reset -- it does not go to 0 or to X, it stays
        whatever it was. Verilator zero-initializes flops with no reset
        branch only at time 0 (elaboration), not on every subsequent reset
        pulse, so forcing a real nonzero value first (rather than trusting
        power-up) is what makes this deterministic and RED under Verilator.
        """
        self.log.info("=== issue #46 round_2 H1: HPET_STATUS reset value ===")
        self.tb.test_phase = "ISSUE46_H1_STATUS_RESET"

        try:
            await self._fresh_disabled_state()
            await self._configure_one_shot(0, comparator=5)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            timeout_ns = self.tb.CORE_CLOCK_PERIOD * 200
            if not await self._wait_for_fire(0, timeout_ns):
                self.log.error("Timer 0 did not fire (setup failure)")
                return False

            _, status_before_reset = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if status_before_reset == 0:
                self.log.error(f"Setup failure: HPET_STATUS is 0x{status_before_reset:08X} "
                                "before the reset pulse (expected nonzero)")
                return False

            # Drive an independent reset pulse.
            self.tb.dut.presetn.value = 0
            self.tb.dut.hpet_resetn.value = 0
            await ClockCycles(self.tb.dut.pclk, 5)
            self.tb.dut.presetn.value = 1
            await ClockCycles(self.tb.dut.pclk, 2)
            self.tb.dut.hpet_resetn.value = 1
            await ClockCycles(self.tb.dut.pclk, 5)

            _, status_after_reset = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)

            passed = True
            if status_after_reset != 0:
                self.log.error(f"HPET_STATUS after reset = 0x{status_after_reset:08X} "
                                f"(was 0x{status_before_reset:08X} before reset), expected "
                                "0x00000000 -- issue #46 round_2 H1 (timer_int_status has no "
                                "reset branch)")
                passed = False

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 round_2 H1: HPET_STATUS reads 0 after reset")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 round_2 H1 test failed with exception: {e}")
            return False

    # ========================================================================
    # issue #46 round_3 HIGH: re-enable must not re-fire a completed timer
    # ========================================================================

    async def test_reenable_does_not_refire(self) -> bool:
        """issue #46 round_3 HIGH: a completed one-shot timer must NOT fire
        again just because hpet_enable (or the timer's own enable bit) is
        toggled 0->1 while the comparator is still expired.

        RTL today (hpet_core.sv): `w_timer_fire = w_timer_match &
        ~r_timer_match_prev`, and `w_timer_match` is forced to 0 whenever
        `timer_enable[i] && hpet_enable` is false. There is no
        already-fired latch, so disabling (either signal) drops match to 0,
        and re-enabling with the counter still past the comparator creates
        a fresh 0->1 edge on match -- a brand new fire pulse. This is
        exactly the MAS's own documented clock-gating sequence (disable ->
        gate -> ungate -> re-enable).
        """
        timer_id = 0
        self.log.info("=== issue #46 round_3 HIGH: re-enable must not re-fire ===")
        self.tb.test_phase = "ISSUE46_ROUND3_REENABLE_REFIRE"

        try:
            await self._fresh_disabled_state()

            await self._configure_one_shot(timer_id, comparator=5)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            timeout_ns = self.tb.CORE_CLOCK_PERIOD * 200
            if not await self._wait_for_fire(timer_id, timeout_ns):
                self.log.error(f"Timer {timer_id} did not fire (setup failure)")
                return False

            # Clear it -- status and irq must both go low.
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            await Timer(self.tb.CORE_CLOCK_PERIOD * 4, units="ns")

            _, status_cleared = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if status_cleared & (1 << timer_id):
                self.log.error(f"Timer {timer_id} status did not clear (setup failure)")
                return False
            if self.tb.timer_interrupt_state[timer_id]:
                self.log.error(f"timer_irq[{timer_id}] did not deassert (setup failure)")
                return False

            # MAS clock-gating sequence: disable -> settle -> re-enable, the
            # comparator is still expired and the timer's own enable stays
            # set throughout (only hpet_enable is toggled).
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            await Timer(self.tb.CORE_CLOCK_PERIOD * 4, units="ns")
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Correct behavior: no new fire. Give it a generous window.
            refired = await self._wait_for_fire(timer_id, self.tb.CORE_CLOCK_PERIOD * 100)

            passed = True
            if refired:
                self.log.error(f"Timer {timer_id} fired again after a plain hpet_enable "
                                "re-enable with an already-expired comparator -- "
                                "issue #46 round_3 re-enable re-fire defect")
                passed = False

            _, status_final = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if status_final & (1 << timer_id):
                self.log.error(f"HPET_STATUS bit {timer_id} spuriously set after re-enable "
                                f"(0x{status_final:X})")
                passed = False

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 round_3: re-enable does not re-fire a completed timer")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 round_3 re-enable test failed with exception: {e}")
            await self._fresh_disabled_state()
            return False

    # ========================================================================
    # issue #46 round_3 Low: comparator write must be write-strobe driven
    # ========================================================================

    async def test_comparator_write_strobe_not_value_change(self) -> bool:
        """issue #46 round_3 Low: rewriting a comparator with the SAME
        value it already holds must still reload hpet_core's internal
        comparator -- the write must be strobe-driven (like the counter
        path's `swmod`), not value-change-detected.

        RTL today (hpet_config_regs.sv):
            timer_comp_write[i] = (comp_lo.value != prev_comp_lo) ||
                                   (comp_hi.value != prev_comp_hi)
        For a PERIODIC timer, hpet_core auto-advances its internal
        `r_timer_comparator` on every fire while the PeakRDL-visible
        register keeps reading the ORIGINAL software-written value P
        forever (nothing ever writes the register itself during periodic
        auto-advance). So after N fires the internal comparator is at
        (N+1)*P while software still reads back P. If software rewrites P
        again (e.g. to restart a periodic phase after resetting the main
        counter), the value hasn't changed from what PeakRDL is storing, so
        `timer_comp_write` never pulses and the stale, far-advanced
        internal comparator is never reloaded.

        Deterministic construction: run a periodic timer at a period P large
        enough that a CDC round-trip cannot smuggle in an extra fire between
        "we observe a fire" and "our next APB write takes effect" (this bit
        RTL developers before: with a small P and CDC_ENABLE=1, a spurious
        THIRD fire could land between detecting fire #2 and the disable
        write reaching hpet_core, making the "stale" multiple config-
        dependent and any fixed elapsed-time threshold unreliable). After
        exactly 2 fires, disable HPET, reset the counter, and rewrite the
        SAME comparator value P.

        The primary, config-independent assertion reads hpet_core's
        internal `r_timer_comparator` directly (there is no software-
        visible register for "the comparator hpet_core is actually
        comparing against" -- the whole point of this defect is that it is
        invisible from the CPU interface) and requires it to read back
        exactly P. This sidesteps CDC-latency-dependent timing windows
        entirely: correct behavior reloads to P; the defect leaves it at
        whatever multiple of P it had already advanced to.

        A black-box corroboration follows: re-enable and confirm the timer
        actually fires, using a generous window sized from the OBSERVED
        internal comparator value (not a guess), so it does not itself
        introduce a race.
        """
        timer_id = 0
        period = 300
        self.log.info("=== issue #46 round_3: comparator write must be strobe-driven ===")
        self.tb.test_phase = "ISSUE46_ROUND3_COMP_STROBE"

        try:
            await self._fresh_disabled_state()

            await self._configure_one_shot(timer_id, comparator=period, periodic=True)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            fire_timeout_ns = self.tb.CORE_CLOCK_PERIOD * period * 6
            for fire_num in range(1, 3):
                if not await self._wait_for_fire(timer_id, fire_timeout_ns):
                    self.log.error(f"Timer {timer_id} periodic fire #{fire_num} did not occur "
                                    "(setup failure)")
                    return False
                if fire_num == 2:
                    # Disable HPET the instant fire #2 is observed, before
                    # spending time on the status W1C -- minimizes the
                    # CDC-latency window in which a 3rd fire could sneak in
                    # before hpet_enable's deassertion reaches the core.
                    await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
                else:
                    await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                    clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                    while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                        await Timer(2, units="ns")

            # Generous settle so any in-flight CDC crossing (disable, or the
            # comparator advance from fire #2) has fully landed before we
            # inspect/mutate state.
            await Timer(self.tb.CORE_CLOCK_PERIOD * 30, units="ns")
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFF)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Rewrite the SAME comparator value. Correct RTL: reloads to
            # `period`. Buggy RTL: no strobe, stays at whatever multiple of
            # `period` it had already advanced to.
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
            await self.tb.write_register(comp_lo_addr, period)
            await self.tb.write_register(comp_hi_addr, 0x00000000)
            # Settle for the rewrite to reach hpet_core (CDC round trip).
            await Timer(self.tb.CORE_CLOCK_PERIOD * 30, units="ns")

            internal_comparator = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
            self.log.info(f"internal r_timer_comparator[{timer_id}] after same-value rewrite "
                            f"= {internal_comparator} (period={period})")

            passed = True
            if internal_comparator != period:
                self.log.error(f"hpet_core's internal comparator for timer {timer_id} reads "
                                f"{internal_comparator}, expected exactly {period} after "
                                "rewriting the SAME comparator value -- issue #46 round_3 "
                                "value-change-detection defect (internal comparator left stale, "
                                f"{internal_comparator // period}x period)")
                passed = False

            # Black-box corroboration: does it actually fire, using a
            # window sized from the value we just observed (not a guess),
            # so this cannot itself race against CDC latency.
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)
            fire_window_ns = self.tb.CORE_CLOCK_PERIOD * internal_comparator * 2 + 1000
            fired = await self._wait_for_fire(timer_id, fire_window_ns)
            if not fired:
                self.log.error(f"Timer {timer_id} never fired within {fire_window_ns}ns of "
                                f"re-enable (internal comparator was {internal_comparator})")
                passed = False

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 round_3: comparator rewrite is strobe-driven")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 round_3 comparator strobe test failed with exception: {e}")
            await self._fresh_disabled_state()
            return False

    # ========================================================================
    # issue #46 review: periodic catch-up must keep firing (hpet_core.sv,
    # gen_timer_comparators / armed-latch block)
    # ========================================================================

    async def test_periodic_counter_ahead_keeps_firing(self) -> bool:
        """issue #46 review: a PERIODIC timer programmed while the main
        counter is already well past the comparator must keep firing at a
        period cadence, not fire once and go silent.

        RTL today (hpet_core.sv):
            gen_timer_comparators: r_timer_comparator[i] advances by
            r_timer_period[i] ONLY on the same cycle as w_timer_fire[i] --
            it does not keep advancing on the cycles after a fire while it
            is still <= counter. The armed latch:
                if (w_timer_comp_write[t] || !w_timer_match[t]) armed <= 1;
                else if (w_timer_fire[t])                       armed <= 0;
            has no other path back to 1. So: the comparator is written
            while HPET is disabled (explicit re-arm via w_timer_comp_write),
            the counter is already ahead, hpet_enable goes high, and the
            timer fires immediately on the first cycle. That SAME cycle it
            also advances the comparator by one period -- but if the counter
            has a big enough head start, one period is not enough to get
            the comparator back ahead of the counter. From then on:
            w_timer_match stays 1 (comparator still <= counter), no comp
            write is happening, so `!w_timer_match[t]` is false and
            `w_timer_comp_write[t]` is false -- armed never returns to 1,
            the comparator never advances again (its only advance path is
            gated on w_timer_fire, which requires armed), and the timer is
            silent forever.

        Construction: counter is set to 1200 (via COUNTER_LO/HI writes
        while HPET is disabled), then a PERIODIC timer is programmed with
        comparator=500, period=500, and only then is HPET enabled. The
        comparator is already 700 counts behind the counter at enable time.

        Correct behavior (per the module's own header comment on the
        armed-latch, "after a fire, the comparator advances ... until it
        exceeds the counter, then the timer re-arms and fires at the next
        boundary; missed periods are skipped, not burst"): at least 3
        fires within a bounded window, with the STEADY-STATE gap between
        fires (i.e. once the comparator has caught up and is no longer
        catching up from the original 700-count deficit) at least one
        period apart -- a fix that "bursts" instead of pacing at the
        programmed period is just as wrong as one that goes silent.

        A second, degenerate construction covers the case where the period
        is smaller than the fire-and-rearm latency (counter=0,
        comparator=1, period=1): the contract there is looser -- the timer
        must simply fire again at least once within a bounded window,
        nothing about spacing.
        """
        timer_id = 0
        counter_start = 1200
        comparator_start = 500
        period = 500
        self.log.info("=== issue #46 review: periodic catch-up must keep firing ===")
        self.tb.test_phase = "ISSUE46_REVIEW_PERIODIC_CATCHUP"

        try:
            await self._fresh_disabled_state()

            # Counter already well past the comparator BEFORE the timer is
            # even armed -- write it while HPET is disabled so it holds.
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, counter_start)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            await self._configure_one_shot(timer_id, comparator=comparator_start, periodic=True)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Bounded per-fire wait: enough for a correct implementation's
            # catch-up (a handful of cycles) plus up to ~1 period waiting
            # for the counter to reach the caught-up comparator.
            per_fire_timeout_ns = self.tb.CORE_CLOCK_PERIOD * (period * 3)

            fire_timestamps_ns = []
            for fire_num in range(1, 4):
                if not await self._wait_for_fire(timer_id, per_fire_timeout_ns):
                    self.log.error(f"Timer {timer_id} periodic fire #{fire_num} did not occur "
                                    f"within {per_fire_timeout_ns}ns (counter started at "
                                    f"{counter_start}, comparator {comparator_start}, "
                                    f"period {period})")
                    break
                fire_timestamps_ns.append(get_sim_time('ns'))

                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                    await Timer(2, units="ns")

            passed = True
            if len(fire_timestamps_ns) < 3:
                self.log.error(f"issue #46 review: periodic timer {timer_id} produced only "
                                f"{len(fire_timestamps_ns)} fire(s) with the counter started "
                                f"ahead of the comparator -- expected at least 3 (the armed "
                                "latch never re-sets once the auto-advanced comparator is "
                                "still <= counter)")
                passed = False
            else:
                # Steady-state spacing: skip the fire0->fire1 gap (it
                # includes the one-time catch-up from the original deficit)
                # and require the later gaps to be at least one period,
                # with slack for W1C-clear/CDC latency.
                min_gap_ns = 0.7 * period * self.tb.CORE_CLOCK_PERIOD
                for prev_ts, next_ts in zip(fire_timestamps_ns[1:], fire_timestamps_ns[2:]):
                    gap_ns = next_ts - prev_ts
                    if gap_ns < min_gap_ns:
                        self.log.error(f"issue #46 review: periodic timer {timer_id} fired "
                                        f"only {gap_ns}ns apart in steady state, expected at "
                                        f"least ~{min_gap_ns}ns (one period={period}) -- burst "
                                        "instead of paced firing")
                        passed = False

            await self._fresh_disabled_state()

            # Degenerate case: period shorter than the fire/re-arm latency.
            # Contract is loose here -- just must not go permanently silent.
            short_period = 1
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
            await self._configure_one_shot(timer_id, comparator=short_period, periodic=True)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            first_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 50
            if not await self._wait_for_fire(timer_id, first_timeout_ns):
                self.log.error(f"Timer {timer_id} short-period ({short_period}) first fire "
                                f"did not occur within {first_timeout_ns}ns (setup failure)")
                passed = False
            else:
                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                    await Timer(2, units="ns")

                second_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 200
                if not await self._wait_for_fire(timer_id, second_timeout_ns):
                    self.log.error(f"issue #46 review: short-period ({short_period}) timer "
                                    f"{timer_id} never fired again within {second_timeout_ns}ns "
                                    "of its first fire -- went permanently silent")
                    passed = False

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 review: periodic catch-up keeps firing")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 review periodic catch-up test failed with exception: {e}")
            await self._fresh_disabled_state()
            return False

    # ========================================================================
    # issue #46 review: live 64-bit comparator reprogram must not tear
    # (hpet_core.sv armed-latch: w_timer_comp_write forces an unconditional
    # re-arm on EITHER half's write strobe, so a LO-then-HI reprogram of a
    # live, already-fired 64-bit comparator exposes the torn intermediate
    # {old HI, new LO} value to the raw comparison for one cycle)
    # ========================================================================

    async def test_live_64bit_comparator_reprogram_no_spurious_fire(self) -> bool:
        """issue #46 review: reprogramming a LIVE (HPET still enabled) 64-bit
        comparator half-by-half must not spuriously re-fire on the torn
        intermediate value.

        RTL today (hpet_core.sv):
            assign w_timer_comp_write = timer_comp_write_lo | timer_comp_write_hi;
            ...
            if (w_timer_comp_write[t] || !w_timer_match[t]) armed <= 1'b1;
        A write to EITHER half sets w_timer_comp_write, which unconditionally
        re-arms the timer on that same cycle -- regardless of whether the
        other half has also been updated. Between "software writes LO" and
        "software writes HI", r_timer_comparator briefly holds {old HI, new
        LO}, a value software never intended to program. If that torn value
        is <= the live counter, the raw match is already 1, the timer is
        freshly re-armed by the LO write's strobe, and it fires immediately
        -- before HI is ever written.

        Construction: counter is driven to 0x0000_0001_0000_0000 while HPET
        is disabled. A 64-bit-mode timer is armed with a small comparator so
        it fires immediately on enable (establishing "already fired, armed
        clear"). Status is cleared. Then, with the timer and HPET both still
        ENABLED, the comparator is reprogrammed to 0x0000_0002_0000_0000 by
        writing LO first (LO=0), then HI (HI=2). The torn intermediate value
        is {HI=0 (the old, small HI half), LO=0} = 0, which is <= the live
        counter -- exactly the spurious-fire condition.

        Correct behavior: no fire from the torn value; status stays clear
        until HI is written and, even then, stays clear because the final
        target (0x2_00000000) is far beyond what the counter reaches in
        this test.

        A documented-flow leg follows in the same test: disable the timer,
        write BOTH halves of a reachable comparator, re-enable -- the timer
        must still arm and fire normally.
        """
        timer_id = 0
        self.log.info("=== issue #46 review: live 64-bit comparator reprogram must not tear ===")
        self.tb.test_phase = "ISSUE46_REVIEW_64BIT_TORN_REPROGRAM"

        try:
            await self._fresh_disabled_state()

            # Counter to a large 64-bit value while HPET is disabled.
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000001)

            # 64-bit-mode timer, small comparator -- fires immediately once
            # HPET is enabled (counter is already far past it).
            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

            initial_comparator = 5
            await self.tb.write_register(comp_lo_addr, initial_comparator)
            await self.tb.write_register(comp_hi_addr, 0x00000000)
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_SIZE)
            await self.tb.write_register(config_addr, timer_config)

            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            setup_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 50
            if not await self._wait_for_fire(timer_id, setup_timeout_ns):
                self.log.error(f"Timer {timer_id} did not fire on the initial small comparator "
                                "(setup failure)")
                return False

            # Clear it -- "already fired, armed clear" starting state.
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
            while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                await Timer(2, units="ns")

            _, status_before_reprogram = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if status_before_reprogram & (1 << timer_id):
                self.log.error(f"Timer {timer_id} status did not clear before reprogram "
                                "(setup failure)")
                return False

            # LIVE reprogram (HPET and the timer both stay enabled): write
            # LO first. Torn intermediate = {old HI=0, new LO=0} = 0, which
            # is <= the live counter (~0x1_00000000) -- the spurious-fire
            # condition under test.
            await self.tb.write_register(comp_lo_addr, 0x00000000)

            # Settle for the write to reach hpet_core (CDC round trip) and
            # for any spurious fire to land in status.
            settle_ns = self.tb.CORE_CLOCK_PERIOD * 30
            await Timer(settle_ns, units="ns")

            passed = True
            _, status_after_lo = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if (status_after_lo & (1 << timer_id)) or self.tb.timer_interrupt_state[timer_id]:
                self.log.error(f"issue #46 review: timer {timer_id} fired from the torn "
                                "intermediate comparator value (old HI, new LO=0) after only "
                                "the LO half of a live 64-bit reprogram was written -- "
                                f"HPET_STATUS=0x{status_after_lo:X}")
                passed = False

            # Complete the reprogram: write HI. Final target (0x2_00000000)
            # is far beyond what the counter reaches in this test.
            await self.tb.write_register(comp_hi_addr, 0x00000002)
            await Timer(settle_ns, units="ns")

            _, status_after_hi = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            if (status_after_hi & (1 << timer_id)) or self.tb.timer_interrupt_state[timer_id]:
                self.log.error(f"issue #46 review: timer {timer_id} status set after the live "
                                "64-bit reprogram completed, but the counter cannot have "
                                f"reached 0x2_00000000 in this test -- HPET_STATUS=0x"
                                f"{status_after_hi:X}")
                passed = False

            # Documented-flow leg: disable, write BOTH halves of a reachable
            # comparator, re-enable -- must still arm and fire normally.
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            await self.tb.write_register(config_addr, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0xFF)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            reachable_comparator = 40
            await self.tb.write_register(comp_lo_addr, reachable_comparator)
            await self.tb.write_register(comp_hi_addr, 0x00000000)
            await self.tb.write_register(config_addr, timer_config)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            documented_flow_timeout_ns = self.tb.CORE_CLOCK_PERIOD * (reachable_comparator + 300)
            if not await self._wait_for_fire(timer_id, documented_flow_timeout_ns):
                self.log.error(f"issue #46 review: documented flow (disable -> write both "
                                f"halves -> re-enable) did not fire timer {timer_id} within "
                                f"{documented_flow_timeout_ns}ns")
                passed = False

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 review: live 64-bit comparator reprogram is "
                               "torn-safe, documented flow still works")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 review 64-bit torn reprogram test failed with "
                            f"exception: {e}")
            await self._fresh_disabled_state()
            return False


    # ========================================================================
    # issue #46 review round_2: catch-up termination holes + a lowering-
    # polarity test gap found in re-review of the round_1 fix (hpet_core.sv
    # gen_timer_comparators / w_comp_adv_ahead / the armed latch). These are
    # RED against the round_1 RTL: they encode the round_2 target contract,
    # not what round_1 already does.
    # ========================================================================

    async def test_periodic_period1_with_deficit_keeps_firing(self) -> bool:
        """issue #46 review round_2, hole #1: catch-up termination test
        `advance > counter` (strict) can never re-arm a period-1 periodic
        timer once the counter starts more than a couple of counts ahead of
        the comparator, because for period=1 the catch-up advance and the
        counter's own increment move at EXACTLY the same rate every cycle:
        the gap between them is an invariant, not something that shrinks.
        The round_2 fix widens the test to `advance >= counter` so a
        period-1 timer re-arms and delivers on the catch-up cycle itself
        rather than waiting for a gap closure that can never happen.

        RTL today (hpet_core.sv):
            w_comp_adv_ahead[i] = (w_comp_advance[i] > r_main_counter);
        For ANY periodic timer at period=1 whose comparator trails the
        counter when it starts running, `comparator(K) + 1` and
        `counter(K)` differ by the same constant every cycle K (both
        advance by exactly 1 per cycle from then on), so `w_comp_adv_ahead`
        evaluates to the SAME truth value forever. If that initial gap is
        large enough that the (single, `>`) test is false, it is false on
        every subsequent cycle too: the timer fires once (the natural
        match at enable) and then goes permanently silent -- `r_timer_armed`
        never returns to 1 again.

        Leg 1 (large initial deficit): HPET disabled, COUNTER_LO written to
        100 (a 99-count deficit against a comparator of 1), TIMER0 armed
        periodic with comparator=1 (period=1), then timer and HPET enabled.
        The first fire is immediate (counter already past the comparator).
        Contract: at least 4 MORE fires within ~40 core cycles of that
        first fire (an every-other-tick cadence -- the fastest the
        one-cycle fire/re-arm loop allows).

        Leg 2 (cadence broken by a live counter write): the same timer is
        set up with counter and comparator starting in lock step (gap 0 --
        the one deficit size the current `>` test already happens to
        handle, per its own math, which is exactly why the existing
        coverage did not catch this hole). Two fires confirm the cadence.
        HPET is then disabled, COUNTER_LO is written to open a gap of 2
        between the live counter and the timer's current internal
        comparator (white-box peek -- there is no software-visible
        register for the auto-advanced value), and HPET is re-enabled.
        Contract: the timer must keep firing, with cadence resuming
        within a few cycles of the re-enable.

        MEASUREMENT NOTE: both legs count fires by sampling
        dut.u_hpet_core.w_timer_fire[timer_id] directly on every core
        clock (see _sample_fire_cycles), NOT by polling
        tb.timer_interrupt_state after an HPET_STATUS W1C write. A W1C
        round trip through write_register is a full APB handshake (~31
        core clocks), so a per-fire clear inside a 40-core-clock counting
        window can observe at most one further fire even though the RTL
        is delivering one every other tick -- a micro-TB confirmed 12
        fires in 24 cycles with no register access in the loop. Status
        W1C does not gate w_timer_fire (it only affects
        timer_int_status/timer_irq), so this measures the RTL's actual
        cadence rather than the test's own register-access latency.
        """
        timer_id = 0
        period = 1
        self.log.info("=== issue #46 review round_2: period-1 catch-up with a real deficit "
                       "must keep firing ===")
        self.tb.test_phase = "ISSUE46_REVIEW2_CATCHUP_PERIOD1_DEFICIT"

        try:
            passed = True

            # ---- Leg 1: large initial deficit (counter starts 99 ahead). ----
            await self._fresh_disabled_state()
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 100)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
            await self._configure_one_shot(timer_id, comparator=period, periodic=True)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            first_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 50
            if not await self._wait_for_fire(timer_id, first_timeout_ns):
                self.log.error(f"Timer {timer_id} did not deliver the first (natural) fire "
                                "with a 99-count deficit -- setup failure")
                return False

            # Sample w_timer_fire directly for a fixed 40-core-cycle window --
            # NO register writes in the loop (see docstring MEASUREMENT NOTE).
            # The already-observed first fire's pulse is over by the time
            # tb.timer_interrupt_state[timer_id] goes True (r_interrupt_status
            # registers one cycle after w_timer_fire, plus CDC latency when
            # enabled), so sampling starting now only counts FURTHER fires.
            window_cycles = 40
            fire_cycles = await self._sample_fire_cycles(timer_id, window_cycles)
            extra_fires = len(fire_cycles)

            if extra_fires < 4:
                self.log.error(f"issue #46 review round_2: period-1 periodic timer with a "
                                f"99-count initial deficit produced only {extra_fires} further "
                                f"fire(s) in {window_cycles} core cycles after the first -- "
                                f"expected at least 4 (every-other-tick cadence). fire_cycles="
                                f"{fire_cycles}")
                passed = False
            else:
                diffs = [fire_cycles[i + 1] - fire_cycles[i] for i in range(len(fire_cycles) - 1)]
                # Skip the first gap (settling from the already-consumed first
                # fire to this window's first sample) -- check the steady-state
                # cadence only.
                bad_diffs = [d for d in diffs[1:] if d < 1 or d > 3]
                if bad_diffs:
                    self.log.error(f"issue #46 review round_2: period-1 periodic timer "
                                    f"fire cadence is not every-other-tick -- fire_cycles="
                                    f"{fire_cycles}, diffs={diffs}, out-of-range gaps="
                                    f"{bad_diffs} (expected 1..3 core cycles between "
                                    "consecutive fires)")
                    passed = False

            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
            while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                await Timer(2, units="ns")

            # ---- Leg 2: cadence established (gap 0), then a live COUNTER_LO
            #      write opens a gap of 2. ----
            await self._fresh_disabled_state()
            await self._configure_one_shot(timer_id, comparator=period, periodic=True)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            cadence_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 30
            cadence_fires = 0
            for _ in range(2):
                if not await self._wait_for_fire(timer_id, cadence_timeout_ns):
                    self.log.error(f"Timer {timer_id} lock-step (gap=0) cadence did not "
                                    "establish -- setup failure")
                    break
                cadence_fires += 1
                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                    await Timer(2, units="ns")

            if cadence_fires != 2:
                passed = False
            else:
                await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
                await Timer(self.tb.CORE_CLOCK_PERIOD * 10, units="ns")
                current_comparator = int(
                    self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
                gap_counter = (current_comparator + 2) & 0xFFFFFFFF
                await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, gap_counter)
                await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
                await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

                # Same direct sampling as leg 1 (see docstring MEASUREMENT
                # NOTE) -- no register writes in the counting window.
                window2_cycles = 40
                fire_cycles2 = await self._sample_fire_cycles(timer_id, window2_cycles)
                extra_fires2 = len(fire_cycles2)

                if extra_fires2 < 3:
                    self.log.error(f"issue #46 review round_2: period-1 periodic timer opened "
                                    f"to a gap of 2 via a live COUNTER_LO write produced only "
                                    f"{extra_fires2} fire(s) in {window2_cycles} core cycles -- "
                                    f"expected to keep firing (at least 3). fire_cycles="
                                    f"{fire_cycles2}")
                    passed = False
                elif fire_cycles2[0] > 6:
                    self.log.error(f"issue #46 review round_2: period-1 periodic timer opened "
                                    f"to a gap of 2 did not resume cadence promptly -- first "
                                    f"post-re-enable fire at core cycle {fire_cycles2[0]} "
                                    f"(expected within a few cycles). fire_cycles={fire_cycles2}")
                    passed = False
                else:
                    diffs2 = [fire_cycles2[i + 1] - fire_cycles2[i]
                              for i in range(len(fire_cycles2) - 1)]
                    bad_diffs2 = [d for d in diffs2[1:] if d < 1 or d > 3]
                    if bad_diffs2:
                        self.log.error(f"issue #46 review round_2: period-1 periodic timer "
                                        f"opened to a gap of 2 does not sustain an "
                                        f"every-other-tick cadence -- fire_cycles={fire_cycles2}, "
                                        f"diffs={diffs2}, out-of-range gaps={bad_diffs2}")
                        passed = False

                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while (self.tb.timer_interrupt_state[timer_id]
                       and get_sim_time('ns') < clear_deadline):
                    await Timer(2, units="ns")

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 review round_2: period-1 catch-up with a "
                               "deficit keeps firing")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 review round_2 period-1 deficit test failed with "
                            f"exception: {e}")
            await self._fresh_disabled_state()
            return False

    async def test_periodic_advance_overflow_no_lockup(self) -> bool:
        """issue #46 review round_2, hole #2: catch-up's advance-by-period
        addition is a full 64-bit adder with NO width awareness, so in
        32-bit compare mode (timer_size=0) an advance that overflows 32
        bits carries straight into comparator[63:32] -- corrupting a field
        the 32-bit-mode comparison never even reads -- and there is
        currently no per-timer "this comparator now belongs to the next
        32-bit epoch, hold the raw match at 0 until the counter wraps (or
        software rewrites the comparator or the counter)" state at all.
        Without that hold, the catch-up just keeps evaluating whatever the
        unmasked adder produced, forever.

        RTL today (hpet_core.sv):
            assign w_comp_advance[i] = r_timer_comparator[i] + r_timer_period[i];
        unconditional on timer_size -- no `[31:0]` mask, no epoch/hold
        state. The match and "ahead" tests both truncate to bits [31:0] in
        32-bit mode, but the VALUE STORED into r_timer_comparator on the
        next advance is the full (possibly carry-extended) 64-bit sum, so
        comparator[63:32] silently accumulates carry out of a field that
        is supposed to be dead weight in this mode.

        Construction: 32-bit-mode (timer_size=0) periodic TIMER0, counter
        started at 0x8000_0000, comparator/period both 0x8000_0010 (period
        == comparator, so the very first advance already overflows 32
        bits: 0x8000_0010 + 0x8000_0010 = 0x1_0000_0020). HPET is disabled
        while counter and comparator are set up, then enabled.

        (a) After the first fire (at counter=0x8000_0010) and a ~20-cycle
            settle, the target design's epoch hold means
            r_timer_comparator[0] has stopped changing and reads exactly
            0x0000_0020 in its low 32 bits with bits [63:32] still 0.
            Current RTL: the unmasked adder has already written a carry
            into bits [63:32] and keeps mutating the register every
            catch-up cycle -- neither half of (a) holds.
        (b) No further fire for ~200 cycles (the comparator belongs to the
            next epoch, held until the counter wraps). Current RTL: the
            churning 32-bit-truncated comparator happens to re-cross the
            live counter's low 32 bits periodically, producing spurious
            extra fires inside the window.
        (c) A COUNTER_LO write (0xFFFF_FFF0) re-bases the epoch per the
            counter-write rule (E3): exactly one prompt fire within ~30
            cycles of the write, using the OLD (pre-overflow) comparator
            0x20. That fire is itself a periodic fire, so it advances the
            comparator again (0x20 + period 0x8000_0010 = 0x8000_0030,
            still below the live counter, so catch-up keeps stepping) and
            the very next catch-up step overflows a SECOND time
            (comparator -> 0x40, epoch set again) -- legitimately, per the
            same rule (a) and (b) already exercised. That second epoch
            holds the match at 0 until the counter itself WRAPS at the
            compare width (rule E1, ~16 cycles after the rebase since the
            counter started at 0xFFFF_FFF0): assert exactly one fire
            before the wrap (the prompt re-base fire; no premature second
            fire while the second epoch holds), then predict the next
            fire from r_timer_comparator sampled right after the wrap
            (epoch now cleared) and the counter at that same instant, and
            assert the timer fires at that distance within a tolerance --
            the next lattice point, not a lockup or a spurious extra fire.
        (d) is the same post-wrap check as (c) -- folded into (c) rather
            than repeated, since (c)'s own re-base fire is what creates
            the second overflow that (d) used to wait out separately.

        MEASUREMENT NOTE: (c)/(d) are evaluated from a single continuous
        core-clock-cycle sweep sampling dut.u_hpet_core.w_timer_fire and
        r_main_counter directly, with NO HPET_STATUS W1C in the loop. An
        APB W1C round trip is ~30 core clocks -- the same order as the
        ~16-cycle distance from 0xFFFF_FFF0 to the compare-width wrap --
        so clearing status between the re-base fire and watching for the
        wrap can let the wrap (and the legitimate post-wrap fire) happen
        INSIDE the clear's own round trip, which is what first made this
        leg misreport a real, on-schedule post-wrap fire as premature.
        """
        timer_id = 0
        counter_start = 0x80000000
        comparator_start = 0x80000010
        self.log.info("=== issue #46 review round_2: 32-bit catch-up advance overflow must "
                       "not lock up ===")
        self.tb.test_phase = "ISSUE46_REVIEW2_32BIT_ADVANCE_OVERFLOW"

        try:
            await self._fresh_disabled_state()
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, counter_start)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
            await self.tb.write_register(comp_lo_addr, comparator_start)
            await self.tb.write_register(comp_hi_addr, 0x00000000)
            # TIMER_SIZE left 0 -> 32-bit compare mode.
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_TYPE)
            await self.tb.write_register(config_addr, timer_config)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            first_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 60
            if not await self._wait_for_fire(timer_id, first_timeout_ns):
                self.log.error(f"Timer {timer_id} did not deliver the first fire at "
                                "0x8000_0010 -- setup failure")
                return False

            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
            while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                await Timer(2, units="ns")

            passed = True

            # ---- (a) churn should stop within ~20 cycles, wrapped to
            #      exactly 0x20, hi32 untouched. ----
            settle_ns = self.tb.CORE_CLOCK_PERIOD * 20
            await Timer(settle_ns, units="ns")
            comp_a = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
            await Timer(self.tb.CORE_CLOCK_PERIOD * 5, units="ns")
            comp_a2 = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)

            self.log.info(f"internal r_timer_comparator[{timer_id}] after {settle_ns}ns "
                           f"settle = 0x{comp_a:016X}, +5 more core cycles = 0x{comp_a2:016X}")

            if comp_a != comp_a2:
                self.log.error(f"issue #46 review round_2: r_timer_comparator[{timer_id}] is "
                                f"still changing {settle_ns}ns after the first overflowing "
                                f"advance (0x{comp_a:016X} -> 0x{comp_a2:016X}) -- no epoch "
                                "hold, catch-up churns indefinitely")
                passed = False
            if (comp_a & 0xFFFFFFFF) != 0x00000020 or (comp_a >> 32) != 0:
                self.log.error(f"issue #46 review round_2: r_timer_comparator[{timer_id}] = "
                                f"0x{comp_a:016X} after the first overflowing advance, "
                                "expected exactly 0x0000000000000020 (low 32 bits wrapped, "
                                "high 32 bits untouched) -- the unmasked 64-bit adder carried "
                                "into comparator[63:32], a field 32-bit mode never reads")
                passed = False

            # ---- (b) no further fire for ~200 cycles. ----
            no_fire_window_ns = self.tb.CORE_CLOCK_PERIOD * 200
            if await self._wait_for_fire(timer_id, no_fire_window_ns):
                self.log.error(f"issue #46 review round_2: timer {timer_id} fired again "
                                f"within {no_fire_window_ns}ns of the first overflowing "
                                "advance -- the comparator should belong to the next epoch "
                                "(no fire until the counter wraps or software rewrites the "
                                "comparator/counter)")
                passed = False
                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while (self.tb.timer_interrupt_state[timer_id]
                       and get_sim_time('ns') < clear_deadline):
                    await Timer(2, units="ns")

            # ---- (c) counter-write re-base: exactly one prompt fire within
            #      ~30 cycles (using the pre-overflow comparator). That fire's
            #      own periodic advance overflows a second time, so the epoch
            #      holds again until the counter WRAPS at the compare width
            #      (rule E1); assert no fire before the wrap, then predict the
            #      next fire from the post-wrap (epoch-cleared) comparator and
            #      confirm it lands there -- the next lattice point, not a
            #      lockup or a spurious fire. (d) is folded in here. ----
            # Monitor entirely off internal signals sampled on the core clock
            # (no APB access in the loop, and the sampler is STARTED BEFORE
            # the re-base write is even issued): an APB write's own round
            # trip is long enough, relative to the core clock, that the
            # entire re-base fire -> second overflow -> wrap sequence can
            # complete before write_register() even returns (confirmed: a
            # first attempt that started sampling AFTER awaiting the write
            # caught the wrap already 4 cycles in, with the re-base fire
            # itself missing entirely -- it had already happened during the
            # write's own APB handshake). Sampling from before the write
            # means cycle 0 is unambiguous and nothing can be missed.
            core_clk = self.tb.dut.hpet_clk if self.tb.CDC_ENABLE else self.tb.dut.pclk
            fire_bus = self.tb.dut.u_hpet_core.w_timer_fire
            counter_reg = self.tb.dut.u_hpet_core.r_main_counter
            comp_reg = self.tb.dut.u_hpet_core.r_timer_comparator[timer_id]

            monitor_cycles = 220

            async def _monitor_c_d():
                fire_cycles: List[int] = []
                wrap_cycle = None
                comp_at_wrap = None
                counter_at_wrap = None
                last_counter_lo = int(counter_reg.value) & 0xFFFFFFFF
                for cycle in range(monitor_cycles):
                    await RisingEdge(core_clk)
                    raw = fire_bus.value
                    if raw is not None and ((int(raw) >> timer_id) & 1):
                        fire_cycles.append(cycle)
                    cur_lo = int(counter_reg.value) & 0xFFFFFFFF
                    if wrap_cycle is None and cur_lo < last_counter_lo:
                        wrap_cycle = cycle
                        comp_at_wrap = int(comp_reg.value) & 0xFFFFFFFF
                        counter_at_wrap = cur_lo
                    last_counter_lo = cur_lo
                return fire_cycles, wrap_cycle, comp_at_wrap, counter_at_wrap

            monitor_task = cocotb.start_soon(_monitor_c_d())

            rebase_counter = 0xFFFFFFF0
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, rebase_counter)

            fire_cycles, wrap_cycle, comp_at_wrap, counter_at_wrap = await monitor_task

            self.log.info(f"issue #46 review round_2: (c)/(d) monitor -- fire_cycles="
                           f"{fire_cycles}, wrap_cycle={wrap_cycle}, "
                           f"comp_at_wrap={'0x%08X' % comp_at_wrap if comp_at_wrap is not None else None}, "
                           f"counter_at_wrap={'0x%08X' % counter_at_wrap if counter_at_wrap is not None else None}")

            if not fire_cycles:
                self.log.error(f"issue #46 review round_2: no fire within {monitor_cycles} "
                                f"core cycles of the COUNTER_LO=0x{rebase_counter:08X} re-base "
                                "write (expected exactly one prompt fire per the counter-write "
                                "epoch re-base rule)")
                passed = False
            elif wrap_cycle is None:
                self.log.error(f"issue #46 review round_2: counter never wrapped at the "
                                f"compare width within {monitor_cycles} core cycles of the "
                                "re-base -- setup/timing issue, cannot evaluate the post-wrap "
                                "lattice point")
                passed = False
            else:
                pre_wrap = [c for c in fire_cycles if c < wrap_cycle]
                if len(pre_wrap) != 1:
                    self.log.error(f"issue #46 review round_2: expected exactly ONE fire "
                                    f"before the counter wrapped at the compare width (cycle "
                                    f"{wrap_cycle}) -- the re-base fire itself, per the "
                                    "counter-write epoch re-base rule -- but observed "
                                    f"{len(pre_wrap)}: {pre_wrap}. Full fire_cycles={fire_cycles}")
                    passed = False
                else:
                    post_wrap = [c for c in fire_cycles if c > wrap_cycle]
                    if not post_wrap:
                        self.log.error(f"issue #46 review round_2: no fire after the counter "
                                        f"wrapped (cycle {wrap_cycle}) within the "
                                        f"{monitor_cycles}-cycle monitor window -- the wrap "
                                        "should clear the epoch (rule E1) and let the timer "
                                        "fire at the next lattice point")
                        passed = False
                    else:
                        distance = (comp_at_wrap - counter_at_wrap) & 0xFFFFFFFF
                        predicted_cycle = wrap_cycle + distance
                        tolerance_cycles = 15
                        if abs(post_wrap[0] - predicted_cycle) > tolerance_cycles:
                            self.log.error(f"issue #46 review round_2: post-wrap fire landed "
                                            f"at core cycle {post_wrap[0]}, expected "
                                            f"{predicted_cycle} (wrap cycle {wrap_cycle} + "
                                            f"distance {distance} to comparator "
                                            f"0x{comp_at_wrap:08X}) within {tolerance_cycles} "
                                            "cycles -- the wrap should clear the epoch (rule "
                                            "E1) and let the timer fire at the next lattice "
                                            "point, not somewhere else")
                            passed = False

            if self.tb.timer_interrupt_state[timer_id]:
                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while (self.tb.timer_interrupt_state[timer_id]
                       and get_sim_time('ns') < clear_deadline):
                    await Timer(2, units="ns")

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 review round_2: 32-bit advance overflow does "
                               "not lock up")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 review round_2 32-bit advance overflow test failed "
                            f"with exception: {e}")
            await self._fresh_disabled_state()
            return False

    async def test_epoch_hold_survives_out_of_width_writes(self) -> bool:
        """issue #46 re-review: w_epoch_clr ORs w_timer_comp_write and
        w_counter_sw_write for BOTH halves regardless of timer_size, so in
        32-bit compare mode (timer_size=0) a write to the OUT-OF-WIDTH half
        -- HPET_COUNTER_HI or TIMER_COMPARATOR_HI, neither of which the
        32-bit match ever reads -- clears the epoch hold anyway. Once
        cleared, the raw match (still true from the held state: the low32
        counter is already far past the wrapped low32 comparator) fires
        immediately, and periodic catch-up resumes from a comparator value
        that is not a real boundary the counter approached at all -- the
        timer fires roughly 2^31 counts early for the construction below.

        RTL today (hpet_core.sv ~517-518):
            assign w_epoch_clr = w_counter_wrap | w_timer_comp_write |
                                 w_timer_size_chg | {NUM_TIMERS{w_counter_sw_write}};
        w_timer_comp_write = timer_comp_write_lo | timer_comp_write_hi, and
        w_counter_sw_write = counter_write_lo | counter_write_hi -- both
        unconditional on timer_size. The fix muxes each pair by timer_size
        so only the LO strobe clears in 32-bit mode; both halves clear in
        64-bit mode (where HI is always in-width).

        Construction: reuse test_periodic_advance_overflow_no_lockup's
        32-bit-mode setup (TIMER0, counter from 0x8000_0000, comparator =
        period = 0x8000_0010) to reach the SAME held state that test
        already proves settles: after the first fire and its overflowing
        advance, r_timer_comparator[0] low32 == 0x20, r_comp_next_epoch[0]
        == 1, held with no churn (peeked white-box, exactly as that test
        does). The live counter's low32 is only a few cycles past the fire
        point, nowhere near the low32 wrap 2^32 away -- so the ONLY thing
        that should be able to end the hold here is a LO-half write
        (E2/E3) or the eventual counter wrap, not an out-of-width HI write.

        Leg (1): with the timer held, write HPET_COUNTER_HI = 0x0000_0001
        (out-of-width in 32-bit mode -- the low32 counter value the match
        actually reads is untouched). Contract: no fire within ~100 core
        cycles, r_comp_next_epoch[0] still 1, r_timer_comparator[0]
        unchanged. Current RTL: the HI write clears the epoch anyway, the
        already-true raw match fires immediately, and this leg is RED.

        Leg (2): re-established held state, then TIMER0_COMPARATOR_HI is
        rewritten to 0 -- its CURRENT value, a strobe-only write with no
        value change (out-of-width in 32-bit mode, and per issue #46
        round_3 the E2 clear is strobe-based, not value-compare-based, so
        this is a fair rewrite-of-same-value probe). Same assertions as
        leg (1), same current-RTL failure.

        Leg (3), positive control: re-established held state, settled an
        extra ~300 cycles so the live counter is unambiguously past
        0x8000_0020, then TIMER0_COMPARATOR_LO is written to 0x8000_0020
        (IN-WIDTH -- this is the LO half the 32-bit match reads, so it
        must clear the epoch on BOTH today's RTL and the fixed RTL). The
        timer re-arms and fires exactly once, promptly (the counter is
        already past the newly-written comparator); the periodic advance
        then overflows again and it goes quiet. This leg is expected to
        pass today AND after the fix -- it is the control proving the
        LO-write clear path this bug must not break.

        64-bit-mode leg: timer_size=1 makes HI ALWAYS in-width (bits
        [63:32] are exactly what the 64-bit match reads), so a
        COUNTER_HI write there must clear the hold on BOTH today's RTL
        and the fixed RTL -- this leg is expected to PASS UNCHANGED by
        the eventual fix; it is the regression guard for the mux the fix
        adds, not new coverage of the bug itself. Construction avoids the
        counter's own 64-bit wrap confusing the result: counter starts at
        0x8000_0000_0000_0000 (an ordinary value, astronomically far from
        its own wrap at all-ones) with comparator = period =
        0x8000_0000_0000_0010, so the first fire (16 counts away) and its
        doubling advance overflow the 64-bit compare width immediately
        (comparator -> 0x20, epoch set) without the counter itself ever
        approaching its own wrap. (A near-all-ones construction was
        rejected here: starting the counter within a handful of counts of
        ITS OWN 64-bit wrap makes rule E1 -- the counter's own wrap --
        fire inside the same short window, confounding an HI-write-
        specific result.) A same-value COUNTER_HI rewrite (strobe only)
        is then applied; the assertion is that the epoch clears and the
        timer fires PROMPTLY (the live counter is already past the tiny
        wrapped comparator) -- no claim is made about the epoch bit past
        that point, because this timer's period (needed huge, ~2^63, to
        reach the held state within a simulatable cycle count) makes the
        very same fire's own periodic advance likely to overflow AGAIN
        and legitimately re-set the epoch immediately, the same chained-
        overflow shape test_periodic_advance_overflow_no_lockup's (c) leg
        already covers for 32-bit mode -- not a new claim for this leg.
        """
        timer_id = 0
        self.log.info("=== issue #46 re-review: epoch hold must not clear on an "
                       "out-of-width HI write ===")
        self.tb.test_phase = "ISSUE46_REREVIEW_EPOCH_HOLD_OUT_OF_WIDTH"

        counter_start = 0x80000000
        comparator_start = 0x80000010

        async def _reach_32bit_held_state() -> bool:
            """Drive TIMER0 into the same 32-bit overflow-held state
            test_periodic_advance_overflow_no_lockup proves settles.
            Returns True once r_comp_next_epoch[0]==1 and the comparator
            has stopped changing (False on setup failure -- not the bug
            under test)."""
            await self._fresh_disabled_state()
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, counter_start)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
            await self.tb.write_register(comp_lo_addr, comparator_start)
            await self.tb.write_register(comp_hi_addr, 0x00000000)
            # TIMER_SIZE left 0 -> 32-bit compare mode.
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) |                         (1 << HPETRegisterMap.TIMER_INT_ENABLE) |                         (1 << HPETRegisterMap.TIMER_TYPE)
            await self.tb.write_register(config_addr, timer_config)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            first_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 60
            if not await self._wait_for_fire(timer_id, first_timeout_ns):
                self.log.error(f"Timer {timer_id} did not deliver the first fire at "
                                "0x8000_0010 -- setup failure")
                return False

            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
            while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < clear_deadline:
                await Timer(2, units="ns")

            settle_ns = self.tb.CORE_CLOCK_PERIOD * 20
            await Timer(settle_ns, units="ns")

            epoch_bit = int(self.tb.dut.u_hpet_core.r_comp_next_epoch.value)
            comp_now = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
            if not ((epoch_bit >> timer_id) & 1) or (comp_now & 0xFFFFFFFF) != 0x00000020:
                self.log.error(f"issue #46 re-review: setup did not reach the held state -- "
                                f"epoch_bit=0x{epoch_bit:X}, comparator=0x{comp_now:016X} "
                                "(setup failure, not the bug under test)")
                return False
            return True

        try:
            passed = True
            no_fire_ns = self.tb.CORE_CLOCK_PERIOD * 100

            # ---- Leg (1): out-of-width COUNTER_HI write must NOT clear
            #      the hold in 32-bit mode. ----
            if not await _reach_32bit_held_state():
                return False

            comp_before = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000001)

            if await self._wait_for_fire(timer_id, no_fire_ns):
                self.log.error(f"issue #46 re-review: timer {timer_id} fired within "
                                f"{no_fire_ns}ns of an out-of-width HPET_COUNTER_HI write "
                                "in 32-bit mode -- the epoch hold must survive a write to a "
                                "half the 32-bit match never reads")
                passed = False
                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while (self.tb.timer_interrupt_state[timer_id]
                       and get_sim_time('ns') < clear_deadline):
                    await Timer(2, units="ns")

            epoch_bit = int(self.tb.dut.u_hpet_core.r_comp_next_epoch.value)
            comp_after = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
            if not ((epoch_bit >> timer_id) & 1):
                self.log.error(f"issue #46 re-review: r_comp_next_epoch[{timer_id}] cleared "
                                "after an out-of-width HPET_COUNTER_HI write in 32-bit mode "
                                "-- w_epoch_clr is not width-conditioned")
                passed = False
            if comp_after != comp_before:
                self.log.error(f"issue #46 re-review: r_timer_comparator[{timer_id}] changed "
                                f"(0x{comp_before:016X} -> 0x{comp_after:016X}) after an "
                                "out-of-width HPET_COUNTER_HI write -- the held comparator "
                                "must not churn")
                passed = False

            # ---- Leg (2): out-of-width same-value COMPARATOR_HI rewrite
            #      must NOT clear the hold either (strobe-based, not
            #      value-compare-based -- issue #46 round_3). ----
            if not await _reach_32bit_held_state():
                passed = False
            else:
                comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
                comp_before2 = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
                await self.tb.write_register(comp_hi_addr, 0x00000000)  # its current value

                if await self._wait_for_fire(timer_id, no_fire_ns):
                    self.log.error(f"issue #46 re-review: timer {timer_id} fired within "
                                    f"{no_fire_ns}ns of a same-value out-of-width "
                                    "TIMER0_COMPARATOR_HI write in 32-bit mode -- the epoch "
                                    "hold must survive a write to a half the 32-bit match "
                                    "never reads")
                    passed = False
                    await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                    clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                    while (self.tb.timer_interrupt_state[timer_id]
                           and get_sim_time('ns') < clear_deadline):
                        await Timer(2, units="ns")

                epoch_bit2 = int(self.tb.dut.u_hpet_core.r_comp_next_epoch.value)
                comp_after2 = int(self.tb.dut.u_hpet_core.r_timer_comparator[timer_id].value)
                if not ((epoch_bit2 >> timer_id) & 1):
                    self.log.error(f"issue #46 re-review: r_comp_next_epoch[{timer_id}] "
                                    "cleared after a same-value out-of-width "
                                    "TIMER0_COMPARATOR_HI write in 32-bit mode")
                    passed = False
                if comp_after2 != comp_before2:
                    self.log.error(f"issue #46 re-review: r_timer_comparator[{timer_id}] "
                                    f"changed (0x{comp_before2:016X} -> 0x{comp_after2:016X}) "
                                    "after a same-value out-of-width TIMER0_COMPARATOR_HI "
                                    "write -- the held comparator must not churn")
                    passed = False

            # ---- Leg (3), positive control: in-width LO write DOES clear
            #      the hold, in both today's RTL and the fixed RTL. ----
            if not await _reach_32bit_held_state():
                passed = False
            else:
                # Settle well past the write-target comparator so the live
                # counter is unambiguously past it before the write lands.
                await Timer(self.tb.CORE_CLOCK_PERIOD * 300, units="ns")
                comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
                new_comparator = 0x80000020
                await self.tb.write_register(comp_lo_addr, new_comparator)

                prompt_ns = self.tb.CORE_CLOCK_PERIOD * 30
                if not await self._wait_for_fire(timer_id, prompt_ns):
                    self.log.error(f"issue #46 re-review: timer {timer_id} did not fire "
                                    f"within {prompt_ns}ns of the IN-WIDTH "
                                    f"TIMER0_COMPARATOR_LO=0x{new_comparator:08X} write -- the "
                                    "positive control (LO writes must still clear the epoch) "
                                    "is broken")
                    passed = False
                else:
                    await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                    clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                    while (self.tb.timer_interrupt_state[timer_id]
                           and get_sim_time('ns') < clear_deadline):
                        await Timer(2, units="ns")

                    quiet_ns = self.tb.CORE_CLOCK_PERIOD * 100
                    if await self._wait_for_fire(timer_id, quiet_ns):
                        self.log.error(f"issue #46 re-review: timer {timer_id} fired a SECOND "
                                        f"time within {quiet_ns}ns of the control fire -- "
                                        "expected the periodic advance to overflow again and "
                                        "go quiet")
                        passed = False
                        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

            await self._fresh_disabled_state()

            # ---- 64-bit-mode leg: HI IS in-width there, so a COUNTER_HI
            #      write must clear the hold -- expected to pass UNCHANGED
            #      by the eventual fix (regression guard for the mux). ----
            counter64_start = 0x8000000000000000
            comparator64_start = 0x8000000000000010
            counter_hi = (counter64_start >> 32) & 0xFFFFFFFF
            counter_lo = counter64_start & 0xFFFFFFFF
            comp_hi_val = (comparator64_start >> 32) & 0xFFFFFFFF
            comp_lo_val = comparator64_start & 0xFFFFFFFF

            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, counter_hi)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, counter_lo)

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
            await self.tb.write_register(comp_lo_addr, comp_lo_val)
            await self.tb.write_register(comp_hi_addr, comp_hi_val)
            timer_config64 = (1 << HPETRegisterMap.TIMER_ENABLE) |                           (1 << HPETRegisterMap.TIMER_INT_ENABLE) |                           (1 << HPETRegisterMap.TIMER_TYPE) |                           (1 << HPETRegisterMap.TIMER_SIZE)  # periodic, 64-bit
            await self.tb.write_register(config_addr, timer_config64)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            first64_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 60
            if not await self._wait_for_fire(timer_id, first64_timeout_ns):
                self.log.error(f"Timer {timer_id} did not deliver the first 64-bit fire at "
                                "0x8000_0000_0000_0010 -- setup failure")
                passed = False
            else:
                await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                while (self.tb.timer_interrupt_state[timer_id]
                       and get_sim_time('ns') < clear_deadline):
                    await Timer(2, units="ns")

                settle64_ns = self.tb.CORE_CLOCK_PERIOD * 20
                await Timer(settle64_ns, units="ns")
                epoch64 = int(self.tb.dut.u_hpet_core.r_comp_next_epoch.value)
                if not ((epoch64 >> timer_id) & 1):
                    self.log.error(f"issue #46 re-review: 64-bit-mode setup did not reach "
                                    f"the held state -- r_comp_next_epoch=0x{epoch64:X} "
                                    "(setup failure, not the leg under test)")
                    passed = False
                else:
                    # Same-value COUNTER_HI rewrite -- strobe only, HI is
                    # in-width for 64-bit mode.
                    await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, counter_hi)

                    prompt64_ns = self.tb.CORE_CLOCK_PERIOD * 30
                    if not await self._wait_for_fire(timer_id, prompt64_ns):
                        self.log.error(f"issue #46 re-review: 64-bit-mode timer {timer_id} "
                                        "did not fire promptly after the in-width "
                                        f"HPET_COUNTER_HI rewrite (within {prompt64_ns}ns) -- "
                                        "HI is in-width in 64-bit mode and must clear the "
                                        "epoch hold on both today's RTL and the fixed RTL")
                        passed = False
                    else:
                        # The prompt fire IS the regression-guard assertion
                        # (HI cleared the hold in 64-bit mode, unlike the
                        # bug under test). No claim is made about the
                        # epoch bit's state past this point: this timer's
                        # period (0x8000_0000_0000_0010, needed to reach
                        # the held state in a simulatable number of
                        # cycles in the first place) is itself close to
                        # 2^63, so the periodic fire-advance this same
                        # fire triggers can legitimately overflow AGAIN
                        # and re-set the epoch immediately -- the same
                        # chained-overflow shape test_periodic_advance_
                        # overflow_no_lockup's (c) leg already covers for
                        # 32-bit mode, not a new claim for this leg.
                        epoch64_after = int(self.tb.dut.u_hpet_core.r_comp_next_epoch.value)
                        self.log.info(f"issue #46 re-review: 64-bit-mode HI-write regression "
                                       f"guard fired promptly as expected; "
                                       f"r_comp_next_epoch=0x{epoch64_after:X} after (informational "
                                       "only -- a chained re-overflow here is legitimate)")
                        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
                        clear_deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * 20
                        while (self.tb.timer_interrupt_state[timer_id]
                               and get_sim_time('ns') < clear_deadline):
                            await Timer(2, units="ns")

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 re-review: epoch hold survives out-of-width "
                               "writes (32-bit legs) and still clears correctly on in-width "
                               "writes (LO control + 64-bit HI)")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 re-review epoch-hold out-of-width test failed with "
                            f"exception: {e}")
            await self._fresh_disabled_state()
            return False

    async def test_live_64bit_comparator_lowering_requires_disable(self) -> bool:
        """issue #46 review round_2, test-polarity gap: prior comparator-
        reprogram coverage (test_live_64bit_comparator_reprogram_no_spurious_fire)
        only ever RAISES a live comparator. This test exercises LOWERING a
        running 64-bit comparator, both the documented-safe
        (disable/write/enable) and the explicitly out-of-contract (write
        live, LO-first) directions, so the "disable a running timer before
        reprogramming its comparator" contract in the module header has a
        test that can actually fail if it stops being true.

        Leg A (documented flow -- disable before reprogramming): a
        64-bit-mode one-shot TIMER0 has already fired once (counter
        ~0x0000_0003_0000_0005, old comparator 0x0000_0003_0000_0000,
        armed clear, status cleared). TIMER0 is disabled (TIMER_ENABLE
        cleared), LO is written to 0xFFFF_FFFF then HI to 2 (final
        0x0000_0002_FFFF_FFFF -- BELOW the live counter), and the timer is
        re-enabled.

        CONTRACT (decided): a comparator write while the timer is stopped
        ALWAYS re-arms it (module header rule A3), whatever value is
        written. A value at or below the counter is therefore due
        immediately once the timer is (re-)enabled -- consistent with the
        >= match used everywhere else in this block, and with every
        deficit case exercised by the other tests in this file. There is
        no "waits for wrap" reading: "program it and it goes off
        immediately because it is already due" is the documented
        behavior, not a defect. Part 1 asserts the timer fires exactly
        once, promptly, after the re-enable, and does not fire again (it
        is a one-shot).

        A second write in leg A reprograms (disable, write both halves,
        re-enable) to a small, directly reachable comparator ABOVE a
        counter that was reset to 0 first -- this must fire once, at it,
        confirming the disable/write/enable flow itself is not broken for
        the ordinary raising direction either (the contract explicitly
        requires "lowering as well as raising" to work through this flow).

        Leg B (explicit non-contract case, logged only, independent setup):
        a fresh 64-bit-mode one-shot TIMER0 fires once at counter
        ~0x0000_0003_0000_0005 / comparator 0x0000_0003_0000_0000, and is
        then reprogrammed LIVE (never disabled) LO-first: LO is written to
        0xFFFF_FFFF, producing a torn intermediate {old HI=3, new LO} =
        0x0000_0003_FFFF_FFFF, which is ABOVE the live counter -- so the
        raw match goes false and the NATURAL re-arm rule (rule 1: !match)
        sets the timer armed again, entirely independent of the "live
        write does not re-arm" rule that protects against a torn value
        BELOW the counter. HI is then written to 2, completing the
        reprogram to 0x0000_0002_FFFF_FFFF -- BELOW the counter -- so the
        now-armed timer's raw match goes true and it fires at the
        completed write. No assertion is made on this leg; only the
        observed behavior is logged, because the docs explicitly disclaim
        this ordering as outside the documented contract (disable first).
        """
        timer_id = 0
        self.log.info("=== issue #46 review round_2: live 64-bit comparator LOWERING "
                       "requires disable first ===")
        self.tb.test_phase = "ISSUE46_REVIEW2_64BIT_LOWER_REQUIRES_DISABLE"

        config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
        comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
        comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
        timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                    (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                    (1 << HPETRegisterMap.TIMER_SIZE)  # 64-bit mode, one-shot

        async def _clear_and_wait(deadline_cycles: int = 20) -> None:
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            deadline = get_sim_time('ns') + self.tb.CORE_CLOCK_PERIOD * deadline_cycles
            while self.tb.timer_interrupt_state[timer_id] and get_sim_time('ns') < deadline:
                await Timer(2, units="ns")

        try:
            passed = True

            # ---- Leg A setup: already-fired 64-bit one-shot, armed clear. ----
            await self._fresh_disabled_state()
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000003)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000005)
            await self.tb.write_register(comp_hi_addr, 0x00000003)
            await self.tb.write_register(comp_lo_addr, 0x00000000)
            await self.tb.write_register(config_addr, timer_config)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            setup_timeout_ns = self.tb.CORE_CLOCK_PERIOD * 50
            if not await self._wait_for_fire(timer_id, setup_timeout_ns):
                self.log.error(f"Timer {timer_id} did not fire on the initial 64-bit "
                                "comparator -- setup failure")
                return False
            await _clear_and_wait()

            # ---- Leg A part 1: disable, LOWER below the live counter, re-enable. ----
            await self.tb.write_register(config_addr, 0x00000000)
            below_hi, below_lo = 0x00000002, 0xFFFFFFFF
            await self.tb.write_register(comp_lo_addr, below_lo)
            await self.tb.write_register(comp_hi_addr, below_hi)
            await self.tb.write_register(config_addr, timer_config)

            below_window_ns = self.tb.CORE_CLOCK_PERIOD * 50
            fired_below = await self._wait_for_fire(timer_id, below_window_ns)
            self.log.info(f"issue #46 review round_2: disable->lower(0x{below_hi:X}_"
                           f"{below_lo:08X}, below the live counter ~0x3_00000005)->re-enable: "
                           f"{'FIRED' if fired_below else 'did not fire'} within "
                           f"{below_window_ns}ns")
            if not fired_below:
                self.log.error(f"issue #46 review round_2: disable->write(below counter)->"
                                f"re-enable did NOT fire within {below_window_ns}ns. Contract "
                                "(module header rule A3): a comparator write on a STOPPED "
                                "timer always re-arms, and a value at or below the counter is "
                                "due immediately once the timer is enabled (>= match) -- it "
                                "must fire promptly, not wait for a counter wrap")
                passed = False
            else:
                await _clear_and_wait()
                no_more_window_ns = self.tb.CORE_CLOCK_PERIOD * 30
                fired_again = await self._wait_for_fire(timer_id, no_more_window_ns)
                if fired_again:
                    self.log.error(f"issue #46 review round_2: disable->write(below counter)->"
                                    f"re-enable fired a SECOND time within {no_more_window_ns}ns "
                                    "of the first -- this is a one-shot timer (TIMER_TYPE=0), "
                                    "it must fire exactly once")
                    passed = False
                    await _clear_and_wait()

            # ---- Leg A part 2: disable, reset counter, RAISE to a small
            #      reachable value above it, re-enable -- must fire once. ----
            await self.tb.write_register(config_addr, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
            above_comparator = 40
            await self.tb.write_register(comp_lo_addr, above_comparator)
            await self.tb.write_register(comp_hi_addr, 0x00000000)
            await self.tb.write_register(config_addr, timer_config)

            above_window_ns = self.tb.CORE_CLOCK_PERIOD * (above_comparator + 50)
            fired_above = await self._wait_for_fire(timer_id, above_window_ns)
            if not fired_above:
                self.log.error(f"issue #46 review round_2: disable->write({above_comparator}, "
                                "above the counter)->re-enable did not fire within "
                                f"{above_window_ns}ns -- the documented disable/write/enable "
                                "flow must work for lowering as well as raising, and this is "
                                "the ordinary raising direction")
                passed = False
            else:
                await _clear_and_wait()

            await self._fresh_disabled_state()

            # ---- Leg B: independent setup, LIVE LO-first lowering -- log only. ----
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000003)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000005)
            await self.tb.write_register(comp_hi_addr, 0x00000003)
            await self.tb.write_register(comp_lo_addr, 0x00000000)
            await self.tb.write_register(config_addr, timer_config)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            if not await self._wait_for_fire(timer_id, setup_timeout_ns):
                self.log.error(f"Timer {timer_id} did not fire on leg B's initial 64-bit "
                                "comparator -- setup failure")
                return False
            await _clear_and_wait()

            # Timer and HPET both stay enabled from here -- LIVE reprogram.
            await self.tb.write_register(comp_lo_addr, 0xFFFFFFFF)
            settle_ns = self.tb.CORE_CLOCK_PERIOD * 10
            await Timer(settle_ns, units="ns")
            _, status_after_torn = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
            self.log.info(f"issue #46 review round_2 leg B: after LIVE LO-first write "
                           f"(torn={{old HI=3, new LO=0xFFFFFFFF}} = 0x3_FFFFFFFF, above the "
                           f"counter) HPET_STATUS=0x{status_after_torn:X}, "
                           f"timer_irq[{timer_id}]={self.tb.timer_interrupt_state[timer_id]}")

            await self.tb.write_register(comp_hi_addr, 0x00000002)
            leg_b_window_ns = self.tb.CORE_CLOCK_PERIOD * 30
            fired_leg_b = await self._wait_for_fire(timer_id, leg_b_window_ns)
            self.log.info(f"issue #46 review round_2 leg B: after completing the LIVE "
                           f"reprogram to 0x2_FFFFFFFF (below the counter), "
                           f"{'FIRED' if fired_leg_b else 'did not fire'} within "
                           f"{leg_b_window_ns}ns of the HI write -- logged only, no assertion "
                           "(outside the documented disable-first contract)")
            if fired_leg_b:
                await _clear_and_wait()

            await self._fresh_disabled_state()
            if passed:
                self.log.info("PASS issue #46 review round_2: live 64-bit comparator "
                               "lowering leg A behaves per the literal target contract")
            return passed

        except Exception as e:
            self.log.error(f"issue #46 review round_2 64-bit lowering test failed with "
                            f"exception: {e}")
            await self._fresh_disabled_state()
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
            ("issue #46 C1: STATUS W1C per-bit", self.test_status_w1c_per_bit()),
            ("issue #46 C2: STATUS hwset per-bit", self.test_status_hwset_per_bit()),
            ("issue #46 C3: 64-bit counter atomic write", self.test_counter_64bit_write_atomic()),
            ("issue #46 round_2 H1: STATUS reset value", self.test_status_reset_value()),
            ("issue #46 round_3: re-enable does not re-fire", self.test_reenable_does_not_refire()),
            ("issue #46 round_3: comparator write strobe", self.test_comparator_write_strobe_not_value_change()),
            ("issue #46 review: periodic catch-up keeps firing", self.test_periodic_counter_ahead_keeps_firing()),
            ("issue #46 review: live 64-bit comparator reprogram no spurious fire",
             self.test_live_64bit_comparator_reprogram_no_spurious_fire()),
            ("issue #46 review round_2: period-1 catch-up with a deficit keeps firing",
             self.test_periodic_period1_with_deficit_keeps_firing()),
            ("issue #46 review round_2: 32-bit advance overflow no lockup",
             self.test_periodic_advance_overflow_no_lockup()),
            ("issue #46 review round_2: live 64-bit comparator lowering requires disable",
             self.test_live_64bit_comparator_lowering_requires_disable()),
            ("issue #46 re-review: epoch hold survives out-of-width writes",
             self.test_epoch_hold_survives_out_of_width_writes()),
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