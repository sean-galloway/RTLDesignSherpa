# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GPIOFullTests
# Purpose: GPIO Full Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
# Subsystem: retro_legacy_blocks/gpio
#
# Created: 2025-11-29

"""
GPIO Full Tests

Comprehensive stress testing of GPIO functionality including:
- Random pattern stress tests
- Rapid atomic operation sequences
- All-pins interrupt stress
- Synchronizer verification
- Edge case testing
"""

import random
from cocotb.triggers import ClockCycles


class GPIOFullTests:
    """Full stress test methods for GPIO module."""

    def __init__(self, tb):
        """
        Initialize full tests.

        Args:
            tb: GPIOTB instance
        """
        self.tb = tb
        self.log = tb.log

    async def run_all_full_tests(self) -> bool:
        """Run all full tests."""
        results = []

        full_tests = [
            ('Random Output Stress', self.test_random_output_stress),
            ('Atomic Operation Stress', self.test_atomic_stress),
            ('Direction Switching Stress', self.test_direction_switching),
            ('Interrupt Storm', self.test_interrupt_storm),
            ('Rapid Edge Detection', self.test_rapid_edge_detection),
            ('All Pins Test', self.test_all_pins),
            ('Walking Ones Output', self.test_walking_ones_output),
            ('Walking Ones Input', self.test_walking_ones_input),
            ('Mixed Mode Stress', self.test_mixed_mode),
        ]

        self.log.info("=" * 80)
        self.log.info("Starting GPIO Full Tests")
        self.log.info("=" * 80)

        for test_name, test_method in full_tests:
            self.log.info(f"\n{'=' * 60}")
            self.log.info(f"Running: {test_name}")
            self.log.info(f"{'=' * 60}")
            try:
                result = await test_method()
                results.append((test_name, result))
            except Exception as e:
                self.log.error(f"{test_name} raised exception: {e}")
                results.append((test_name, False))

        # Print summary
        self.log.info("\n" + "=" * 80)
        self.log.info("FULL TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nFull Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)

    async def test_random_output_stress(self) -> bool:
        """Stress test with random output patterns."""
        self.log.info("Testing random output patterns...")
        passed = True
        iterations = 100

        try:
            await self.tb.enable_gpio(True, False)
            await self.tb.set_direction(0xFFFFFFFF)

            for i in range(iterations):
                pattern = random.randint(0, 0xFFFFFFFF)
                await self.tb.set_output(pattern)
                await ClockCycles(self.tb.pclk, 3)
                out = self.tb.get_gpio_output()
                if out != pattern:
                    self.log.error(f"Iteration {i}: wrote 0x{pattern:08X}, got 0x{out:08X}")
                    passed = False
                    break

            if passed:
                self.log.info(f"Random output stress: {iterations} iterations OK")

        except Exception as e:
            self.log.error(f"Random output stress exception: {e}")
            passed = False

        return passed

    async def test_atomic_stress(self) -> bool:
        """Stress test atomic operations."""
        self.log.info("Testing atomic operation stress...")
        passed = True
        iterations = 50

        try:
            await self.tb.enable_gpio(True, False)
            await self.tb.set_direction(0xFFFFFFFF)
            await self.tb.set_output(0)
            await ClockCycles(self.tb.pclk, 5)

            expected = 0

            for i in range(iterations):
                op = random.choice(['set', 'clear', 'toggle'])
                mask = random.randint(0, 0xFFFFFFFF)

                if op == 'set':
                    await self.tb.atomic_set(mask)
                    expected |= mask
                elif op == 'clear':
                    await self.tb.atomic_clear(mask)
                    expected &= ~mask
                else:  # toggle
                    await self.tb.atomic_toggle(mask)
                    expected ^= mask

                expected &= 0xFFFFFFFF  # Ensure 32-bit
                await ClockCycles(self.tb.pclk, 5)

                out = self.tb.get_gpio_output()
                if out != expected:
                    self.log.error(f"Iteration {i} ({op}): expected 0x{expected:08X}, got 0x{out:08X}")
                    passed = False
                    break

            if passed:
                self.log.info(f"Atomic stress: {iterations} iterations OK")

        except Exception as e:
            self.log.error(f"Atomic stress exception: {e}")
            passed = False

        return passed

    async def test_direction_switching(self) -> bool:
        """Stress test direction switching."""
        self.log.info("Testing direction switching stress...")
        passed = True
        iterations = 50

        try:
            await self.tb.enable_gpio(True, False)

            for i in range(iterations):
                direction = random.randint(0, 0xFFFFFFFF)
                await self.tb.set_direction(direction)
                await ClockCycles(self.tb.pclk, 3)
                oe = self.tb.get_gpio_oe()
                if oe != direction:
                    self.log.error(f"Iteration {i}: direction 0x{direction:08X}, OE 0x{oe:08X}")
                    passed = False
                    break

            if passed:
                self.log.info(f"Direction switching: {iterations} iterations OK")

        except Exception as e:
            self.log.error(f"Direction switching exception: {e}")
            passed = False

        return passed

    async def test_interrupt_storm(self) -> bool:
        """Stress test with many rapid interrupts."""
        self.log.info("Testing interrupt storm...")
        passed = True
        storm_count = 20

        try:
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Enable all pins for rising edge interrupt
            await self.tb.set_interrupt_enable(0xFFFFFFFF)
            await self.tb.set_interrupt_type(0x00000000)
            await self.tb.set_interrupt_polarity(0xFFFFFFFF)
            await self.tb.set_interrupt_both_edge(0x00000000)

            for i in range(storm_count):
                # Clear status
                await self.tb.clear_interrupt_status(0xFFFFFFFF)
                self.tb.set_gpio_input(0)
                await ClockCycles(self.tb.pclk, 10)

                # Trigger random subset
                trigger = random.randint(0, 0xFFFFFFFF)
                self.tb.set_gpio_input(trigger)
                await ClockCycles(self.tb.pclk, 10)

                # Verify IRQ if any bit set
                if trigger != 0 and not self.tb.get_irq():
                    self.log.error(f"Storm {i}: no IRQ for trigger 0x{trigger:08X}")
                    passed = False
                    break

            if passed:
                self.log.info(f"Interrupt storm: {storm_count} storms OK")

        except Exception as e:
            self.log.error(f"Interrupt storm exception: {e}")
            passed = False

        return passed

    async def test_rapid_edge_detection(self) -> bool:
        """Test rapid edge detection."""
        self.log.info("Testing rapid edge detection...")
        passed = True

        try:
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Pin 0 both edges
            await self.tb.set_interrupt_enable(0x00000001)
            await self.tb.set_interrupt_type(0x00000000)
            await self.tb.set_interrupt_polarity(0x00000000)
            await self.tb.set_interrupt_both_edge(0x00000001)

            edge_count = 0
            for i in range(20):
                # Clear
                await self.tb.clear_interrupt_status(0x01)
                self.tb.set_gpio_input(0)
                await ClockCycles(self.tb.pclk, 10)

                # Quick toggle
                self.tb.set_gpio_input(0x01)
                await ClockCycles(self.tb.pclk, 5)
                self.tb.set_gpio_input(0x00)
                await ClockCycles(self.tb.pclk, 10)

                # Should have seen at least one edge
                status = await self.tb.get_interrupt_status()
                if status & 0x01:
                    edge_count += 1

            if edge_count < 10:
                self.log.error(f"Rapid edge: only {edge_count}/20 edges detected")
                passed = False
            else:
                self.log.info(f"Rapid edge: {edge_count}/20 edges OK")

        except Exception as e:
            self.log.error(f"Rapid edge exception: {e}")
            passed = False

        return passed

    async def test_all_pins(self) -> bool:
        """Test all 32 pins individually."""
        self.log.info("Testing all 32 pins...")
        passed = True

        try:
            await self.tb.enable_gpio(True, True)

            # Test each pin as output
            await self.tb.set_direction(0xFFFFFFFF)
            for pin in range(32):
                mask = 1 << pin
                await self.tb.set_output(mask)
                await ClockCycles(self.tb.pclk, 3)
                out = self.tb.get_gpio_output()
                if out != mask:
                    self.log.error(f"Pin {pin} output failed")
                    passed = False
                    break

            # Test each pin as input
            await self.tb.set_direction(0x00000000)
            for pin in range(32):
                mask = 1 << pin
                self.tb.set_gpio_input(mask)
                await ClockCycles(self.tb.pclk, 10)
                inp = await self.tb.get_input()
                if inp != mask:
                    self.log.error(f"Pin {pin} input failed: expected 0x{mask:08X}, got 0x{inp:08X}")
                    passed = False
                    break

            if passed:
                self.log.info("All 32 pins: OK")

        except Exception as e:
            self.log.error(f"All pins test exception: {e}")
            passed = False

        return passed

    async def test_walking_ones_output(self) -> bool:
        """Test walking ones pattern on output."""
        self.log.info("Testing walking ones output...")
        passed = True

        try:
            await self.tb.enable_gpio(True, False)
            await self.tb.set_direction(0xFFFFFFFF)

            for pin in range(32):
                pattern = 1 << pin
                await self.tb.set_output(pattern)
                await ClockCycles(self.tb.pclk, 3)
                out = self.tb.get_gpio_output()
                if out != pattern:
                    self.log.error(f"Walking 1 at pin {pin}: expected 0x{pattern:08X}, got 0x{out:08X}")
                    passed = False
                    break

            if passed:
                self.log.info("Walking ones output: OK")

        except Exception as e:
            self.log.error(f"Walking ones output exception: {e}")
            passed = False

        return passed

    async def test_walking_ones_input(self) -> bool:
        """Test walking ones pattern on input."""
        self.log.info("Testing walking ones input...")
        passed = True

        try:
            await self.tb.enable_gpio(True, False)
            await self.tb.set_direction(0x00000000)

            for pin in range(32):
                pattern = 1 << pin
                self.tb.set_gpio_input(pattern)
                await ClockCycles(self.tb.pclk, 10)
                inp = await self.tb.get_input()
                if inp != pattern:
                    self.log.error(f"Walking 1 at pin {pin}: expected 0x{pattern:08X}, got 0x{inp:08X}")
                    passed = False
                    break

            if passed:
                self.log.info("Walking ones input: OK")

        except Exception as e:
            self.log.error(f"Walking ones input exception: {e}")
            passed = False

        return passed

    async def test_mixed_mode(self) -> bool:
        """Test mixed input/output mode."""
        self.log.info("Testing mixed input/output mode...")
        passed = True

        try:
            await self.tb.enable_gpio(True, False)

            # Lower 16 as outputs, upper 16 as inputs
            await self.tb.set_direction(0x0000FFFF)

            # Set output pattern
            await self.tb.set_output(0x0000AAAA)
            await ClockCycles(self.tb.pclk, 5)

            # Set input pattern on upper bits
            self.tb.set_gpio_input(0x55550000)
            await ClockCycles(self.tb.pclk, 10)

            # Check output
            out = self.tb.get_gpio_output()
            if (out & 0xFFFF) != 0xAAAA:
                self.log.error(f"Output mismatch: expected 0xAAAA, got 0x{out & 0xFFFF:04X}")
                passed = False

            # Check input
            inp = await self.tb.get_input()
            if (inp >> 16) != 0x5555:
                self.log.error(f"Input mismatch: expected 0x5555, got 0x{inp >> 16:04X}")
                passed = False

            # Verify OE
            oe = self.tb.get_gpio_oe()
            if oe != 0x0000FFFF:
                self.log.error(f"OE mismatch: expected 0x0000FFFF, got 0x{oe:08X}")
                passed = False

            if passed:
                self.log.info("Mixed mode: OK")

        except Exception as e:
            self.log.error(f"Mixed mode exception: {e}")
            passed = False

        return passed
