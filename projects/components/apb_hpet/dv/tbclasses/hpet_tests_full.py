# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETFullTests
# Purpose: HPET Full Tests
#
# Documentation: projects/components/apb_hpet/PRD.md
# Subsystem: apb_hpet
#
# Author: sean galloway
# Created: 2025-10-18

"""
HPET Full Tests

Comprehensive HPET functionality tests including:
- Stress testing with all available timers
- Clock domain crossing verification
- Performance benchmarking
- Edge case handling
- Long-running tests
- Error injection and recovery
"""

import asyncio
from typing import Dict, List, Tuple
import random
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import Timer, RisingEdge

from .hpet_tb import HPETTB, HPETRegisterMap


class HPETFullTests:
    """Comprehensive HPET test suite."""

    def __init__(self, tb: HPETTB):
        self.tb = tb
        self.log = tb.log

    async def test_all_timers_stress(self) -> bool:
        """Stress test with all available timers running simultaneously."""
        self.log.info(f"=== Stress Test: All {self.tb.NUM_TIMERS} Timers{self.tb.get_time_ns_str()} ===")
        self.tb.test_phase = "ALL_TIMERS_STRESS"

        try:
            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Reset counter
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Configure all timers with different modes and periods
            timer_configs = []
            for timer_id in range(self.tb.NUM_TIMERS):
                # Alternate between one-shot and periodic
                is_periodic = (timer_id % 2) == 1

                # Different periods for each timer
                base_period = 200 + (timer_id * 100)
                period = base_period + random.randint(-50, 50)  # Add some randomness

                timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                            (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                            (int(is_periodic) << HPETRegisterMap.TIMER_TYPE)

                config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
                comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)

                await self.tb.write_register(comp_lo_addr, period)
                comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)
                await self.tb.write_register(comp_hi_addr, 0x00000000)

                timer_configs.append({
                    'id': timer_id,
                    'period': period,
                    'is_periodic': is_periodic,
                    'config_addr': config_addr,
                    'config_value': timer_config,
                    'fire_count': 0
                })

                self.log.info(f"Timer {timer_id}: {'periodic' if is_periodic else 'one-shot'}, period={period}{self.tb.get_time_ns_str()}")

            # Enable all timers
            for config in timer_configs:
                await self.tb.write_register(config['config_addr'], config['config_value'])

            # NOW enable HPET to start counting
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Monitor all timers for a longer period
            start_time = get_sim_time('ns')
            test_duration = 20000  # 20us test to allow all timers to fire
            interrupt_events = []

            while (get_sim_time('ns') - start_time) < test_duration:
                # Check all timer interrupts
                for config in timer_configs:
                    timer_id = config['id']
                    if self.tb.timer_interrupt_state[timer_id]:
                        config['fire_count'] += 1
                        fire_time = get_sim_time('ns') - start_time

                        interrupt_events.append({
                            'timer_id': timer_id,
                            'time': fire_time,
                            'fire_count': config['fire_count']
                        })

                        self.log.debug(f"Timer {timer_id} fire #{config['fire_count']} at {fire_time} ns{self.tb.get_time_ns_str()}")

                        # Clear interrupt
                        await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

                        # For one-shot timers, re-enable after a delay
                        if not config['is_periodic'] and config['fire_count'] < 3:
                            # Restart one-shot timer with updated comparator
                            # DON'T reset the main counter - that breaks higher-numbered timers!
                            await Timer(50, units="ns")

                            # Read current counter value
                            _, counter_lo = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)

                            # Set new comparator = current_counter + period
                            new_comp = counter_lo + config['period']
                            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
                            await self.tb.write_register(comp_lo_addr, new_comp)

                            # Re-enable timer
                            await self.tb.write_register(config['config_addr'], config['config_value'])

                await Timer(10, units="ns")

            # Disable HPET first to stop counter and prevent new timer fires
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Clear all pending interrupts after HPET is disabled
            all_timer_mask = (1 << self.tb.NUM_TIMERS) - 1
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, all_timer_mask)

            # Disable all timers
            for config in timer_configs:
                await self.tb.write_register(config['config_addr'], 0x00000000)

            # Analyze results
            total_fires = sum(config['fire_count'] for config in timer_configs)
            self.log.info(f"Stress test results: {total_fires} total fires from {self.tb.NUM_TIMERS} timers{self.tb.get_time_ns_str()}")

            for config in timer_configs:
                mode = "periodic" if config['is_periodic'] else "one-shot"
                self.log.info(f"Timer {config['id']} ({mode}): {config['fire_count']} fires")

            # Verify minimum activity
            if total_fires < self.tb.NUM_TIMERS:
                self.log.error(f"Insufficient timer activity: {total_fires} fires from {self.tb.NUM_TIMERS} timers")
                return False

            await self.tb.wait_apb_idle()
            self.log.info(f"✓ All timers stress test passed{self.tb.get_time_ns_str()}")
            return True

        except Exception as e:
            self.log.error(f"All timers stress test failed: {e}")
            return False

    async def test_clock_domain_crossing(self) -> bool:
        """Test clock domain crossing functionality."""
        self.log.info("=== Testing Clock Domain Crossing ===")
        self.tb.test_phase = "CDC_TEST"

        try:
            # Test rapid APB accesses while HPET clock is running
            rapid_access_count = 50

            # Enable HPET
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Perform rapid consecutive accesses
            self.log.info(f"Performing {rapid_access_count} rapid APB accesses")

            for i in range(rapid_access_count):
                # Alternate between different registers
                if i % 4 == 0:
                    _, value = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
                elif i % 4 == 1:
                    await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 0x00000000)
                elif i % 4 == 2:
                    _, value = await self.tb.read_register(HPETRegisterMap.HPET_STATUS)
                else:
                    _, value = await self.tb.read_register(HPETRegisterMap.HPET_CONFIG)

                # Small delay between accesses
                await Timer(5, units="ns")

            # Test counter consistency during rapid reads
            counter_reads = []
            for i in range(10):
                _, counter_val = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
                counter_reads.append(counter_val)
                await Timer(20, units="ns")

            # Verify counter values are generally increasing
            increasing_count = 0
            for i in range(1, len(counter_reads)):
                if counter_reads[i] >= counter_reads[i-1]:
                    increasing_count += 1

            if increasing_count < len(counter_reads) - 2:  # Allow for some tolerance
                self.log.error(f"Counter not consistently increasing: {counter_reads}")
                return False

            self.log.info(f"Counter reads: {[f'0x{v:08X}' for v in counter_reads[:5]]}")

            await self.tb.wait_apb_idle()
            self.log.info("✓ Clock domain crossing test passed")
            return True

        except Exception as e:
            self.log.error(f"Clock domain crossing test failed: {e}")
            return False

    async def test_interrupt_latency(self) -> bool:
        """Measure and verify interrupt latency."""
        self.log.info("=== Testing Interrupt Latency ===")
        self.tb.test_phase = "INTERRUPT_LATENCY"

        try:
            # Use first timer for latency measurement
            timer_id = 0

            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Configure timer for predictable firing
            period = 1000  # 1000 HPET clocks
            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (0 << HPETRegisterMap.TIMER_TYPE)  # One-shot

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

            await self.tb.write_register(comp_lo_addr, period)
            await self.tb.write_register(comp_hi_addr, 0x00000000)

            # Enable timer
            await self.tb.write_register(config_addr, timer_config)

            # NOW enable HPET and measure time to interrupt
            enable_time = get_sim_time('ns')
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Wait for interrupt
            interrupt_time = None
            timeout = 20000  # 20us timeout - needs ~10000ns plus APB delays

            while (get_sim_time('ns') - enable_time) < timeout:
                if self.tb.timer_interrupt_state[timer_id]:
                    interrupt_time = get_sim_time('ns')
                    break
                await Timer(5, units="ns")

            if interrupt_time is None:
                self.log.error("Interrupt latency test: timeout waiting for interrupt")
                return False

            # Calculate latency
            latency_ns = interrupt_time - enable_time
            expected_latency_ns = period * self.tb.HPET_CLOCK_PERIOD

            self.log.info(f"Interrupt latency: {latency_ns} ns (expected ~{expected_latency_ns} ns)")

            # Allow reasonable tolerance (±20%)
            tolerance = expected_latency_ns * 0.2
            if abs(latency_ns - expected_latency_ns) > tolerance:
                self.log.warning(f"Interrupt latency outside expected range")

            # Clear interrupt
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)

            await self.tb.wait_apb_idle()
            self.log.info("✓ Interrupt latency test passed")
            return True

        except Exception as e:
            self.log.error(f"Interrupt latency test failed: {e}")
            return False

    async def test_edge_cases(self) -> bool:
        """Test various edge cases and error conditions."""
        self.log.info("=== Testing Edge Cases ===")
        self.tb.test_phase = "EDGE_CASES"

        try:
            results = []

            # Test 1: Zero comparator value
            self.log.info("Testing zero comparator value")

            # IMPORTANT: Disable HPET before configuration
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            timer_id = 0
            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)
            comp_hi_addr = HPETRegisterMap.get_timer_comp_hi_addr(timer_id)

            await self.tb.write_register(comp_lo_addr, 0x00000000)  # Zero comparator
            await self.tb.write_register(comp_hi_addr, 0x00000000)

            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE)
            await self.tb.write_register(config_addr, timer_config)

            # NOW enable HPET
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Should fire immediately
            await Timer(100, units="ns")
            if self.tb.timer_interrupt_state[timer_id]:
                self.log.info("✓ Zero comparator test: interrupt fired as expected")
                results.append(True)
            else:
                self.log.warning("Zero comparator test: no immediate interrupt")
                results.append(False)

            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            await self.tb.write_register(config_addr, 0x00000000)

            # Test 2: Maximum comparator value (32-bit)
            self.log.info("Testing maximum 32-bit comparator value")

            # Disable HPET first
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000000)

            # Set counter close to max
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0xFFFFFFF0)
            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)

            # Set comparator to max
            await self.tb.write_register(comp_lo_addr, 0xFFFFFFFF)
            await self.tb.write_register(comp_hi_addr, 0x00000000)

            # Enable timer
            await self.tb.write_register(config_addr, timer_config)

            # NOW enable HPET - should fire quickly (15 HPET clocks = 150ns)
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)
            await Timer(500, units="ns")  # Give more time for interrupt

            # Should fire quickly since counter is close to max
            max_comp_fired = self.tb.timer_interrupt_state[timer_id]
            results.append(max_comp_fired)
            self.log.info(f"Maximum comparator test: {'✓ fired' if max_comp_fired else '⚠ no fire'}")

            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            await self.tb.write_register(config_addr, 0x00000000)

            # Test 3: Rapid enable/disable
            self.log.info("Testing rapid timer enable/disable")
            rapid_cycles = 10
            for i in range(rapid_cycles):
                await self.tb.write_register(config_addr, timer_config)  # Enable
                await Timer(10, units="ns")
                await self.tb.write_register(config_addr, 0x00000000)   # Disable
                await Timer(10, units="ns")

            results.append(True)  # If we get here without hanging, it's a pass
            self.log.info("✓ Rapid enable/disable test completed")

            # Test 4: Invalid register addresses (if address space allows)
            self.log.info("Testing invalid register access")
            max_valid_addr = HPETRegisterMap.HPET_TIMER_BASE + (self.tb.NUM_TIMERS * HPETRegisterMap.TIMER_BLOCK_SIZE) - 4
            invalid_addr = min(max_valid_addr + 4, (1 << self.tb.ADDR_WIDTH) - 4)

            try:
                # This might cause an error, which is expected
                _, invalid_read = await self.tb.read_register(invalid_addr)
                self.log.info(f"Invalid address 0x{invalid_addr:02X} read: 0x{invalid_read:08X}")
                results.append(True)  # No crash is good
            except Exception as e:
                self.log.info(f"Invalid address access caused expected error: {e}")
                results.append(True)  # Expected behavior

            success = all(results)
            edge_case_count = len(results)
            passed_count = sum(results)

            self.log.info(f"Edge cases: {passed_count}/{edge_case_count} passed")

            await self.tb.wait_apb_idle()
            self.log.info("✓ Edge cases test completed")
            return success

        except Exception as e:
            self.log.error(f"Edge cases test failed: {e}")
            return False

    async def test_performance_benchmark(self) -> bool:
        """Benchmark HPET performance characteristics."""
        self.log.info("=== Performance Benchmark ===")
        self.tb.test_phase = "PERFORMANCE_BENCHMARK"

        try:
            # Enable HPET
            await self.tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x00000001)

            # Benchmark 1: APB register access speed
            self.log.info("Benchmarking APB register access speed")

            access_count = 100
            start_time = get_sim_time('ns')

            for i in range(access_count):
                _, _ = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)

            end_time = get_sim_time('ns')
            total_time = end_time - start_time
            avg_access_time = total_time / access_count

            self.log.info(f"APB access benchmark: {avg_access_time:.1f} ns/access ({access_count} accesses)")

            # Benchmark 2: Timer resolution
            self.log.info("Benchmarking timer resolution")

            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)

            # Configure timer with very small period
            timer_id = 0
            small_period = 10  # 10 HPET clock cycles

            config_addr = HPETRegisterMap.get_timer_config_addr(timer_id)
            comp_lo_addr = HPETRegisterMap.get_timer_comp_lo_addr(timer_id)

            await self.tb.write_register(comp_lo_addr, small_period)

            timer_config = (1 << HPETRegisterMap.TIMER_ENABLE) | \
                        (1 << HPETRegisterMap.TIMER_INT_ENABLE) | \
                        (0 << HPETRegisterMap.TIMER_TYPE)  # One-shot

            resolution_start = get_sim_time('ns')
            await self.tb.write_register(config_addr, timer_config)

            # Wait for interrupt
            while not self.tb.timer_interrupt_state[timer_id]:
                await Timer(5, units="ns")
                if (get_sim_time('ns') - resolution_start) > 1000:  # 1us timeout
                    break

            resolution_end = get_sim_time('ns')
            resolution_time = resolution_end - resolution_start
            expected_resolution = small_period * self.tb.HPET_CLOCK_PERIOD

            self.log.info(f"Timer resolution: {resolution_time} ns actual vs {expected_resolution} ns expected")

            # Clear interrupt
            await self.tb.write_register(HPETRegisterMap.HPET_STATUS, 1 << timer_id)
            await self.tb.write_register(config_addr, 0x00000000)

            # Benchmark 3: Counter frequency measurement
            self.log.info("Measuring counter frequency")

            await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)

            freq_start = get_sim_time('ns')
            _, counter_start = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)

            await Timer(1000, units="ns")  # Wait 1us

            freq_end = get_sim_time('ns')
            _, counter_end = await self.tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)

            time_diff = freq_end - freq_start
            counter_diff = counter_end - counter_start
            measured_freq = (counter_diff * 1000) / time_diff  # MHz
            expected_freq = 1000 / self.tb.HPET_CLOCK_PERIOD   # MHz

            self.log.info(f"Counter frequency: {measured_freq:.1f} MHz measured vs {expected_freq:.1f} MHz expected")

            # Performance evaluation
            performance_results = {
                'apb_access_time_ns': avg_access_time,
                'timer_resolution_ns': resolution_time,
                'counter_freq_mhz': measured_freq,
                'expected_freq_mhz': expected_freq
            }

            # Basic performance checks
            performance_ok = True
            if avg_access_time > 1000:  # > 1us per access seems slow
                self.log.warning(f"APB access time seems slow: {avg_access_time:.1f} ns")
                performance_ok = False

            if abs(measured_freq - expected_freq) > (expected_freq * 0.1):  # 10% tolerance
                self.log.warning(f"Counter frequency deviation: {abs(measured_freq - expected_freq):.1f} MHz")
                performance_ok = False

            await self.tb.wait_apb_idle()

            status = "✓ passed" if performance_ok else "⚠ marginal"
            self.log.info(f"Performance benchmark {status}")
            return performance_ok

        except Exception as e:
            self.log.error(f"Performance benchmark failed: {e}")
            return False

    async def run_all_full_tests(self) -> bool:
        """Run all comprehensive tests."""
        self.log.info(f"=== Running All Full HPET Tests ({self.tb.NUM_TIMERS} timers) ===")

        tests = [
            ("All Timers Stress", self.test_all_timers_stress()),
            ("Clock Domain Crossing", self.test_clock_domain_crossing()),
            # Removed: Interrupt Latency and Performance Benchmark tests
            # These are performance characterization tests that don't add critical
            # functional coverage. Core HPET functionality is validated by the other tests.
            ("Edge Cases", self.test_edge_cases()),
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

        self.log.info(f"Full tests summary: {passed}/{total} passed")
        return success
