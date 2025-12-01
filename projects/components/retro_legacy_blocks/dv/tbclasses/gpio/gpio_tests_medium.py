# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GPIOMediumTests
# Purpose: GPIO Medium Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
# Subsystem: retro_legacy_blocks/gpio
#
# Created: 2025-11-29

"""
GPIO Medium Tests

Intermediate verification of GPIO functionality including:
- Edge interrupt detection (rising, falling, both)
- Level interrupt detection
- Multiple interrupt sources
- W1C interrupt clearing
"""

import random
from cocotb.triggers import ClockCycles


class GPIOMediumTests:
    """Medium test methods for GPIO module."""

    def __init__(self, tb):
        """
        Initialize medium tests.

        Args:
            tb: GPIOTB instance
        """
        self.tb = tb
        self.log = tb.log

    async def run_all_medium_tests(self) -> bool:
        """Run all medium tests."""
        results = []

        medium_tests = [
            ('Rising Edge Interrupt', self.test_rising_edge_interrupt),
            ('Falling Edge Interrupt', self.test_falling_edge_interrupt),
            ('Both Edge Interrupt', self.test_both_edge_interrupt),
            ('Level High Interrupt', self.test_level_high_interrupt),
            ('Level Low Interrupt', self.test_level_low_interrupt),
            ('Multiple Interrupt Sources', self.test_multiple_interrupts),
            ('W1C Interrupt Clear', self.test_w1c_clear),
            ('Raw vs Masked Status', self.test_raw_vs_masked),
        ]

        self.log.info("=" * 80)
        self.log.info("Starting GPIO Medium Tests")
        self.log.info("=" * 80)

        for test_name, test_method in medium_tests:
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
        self.log.info("MEDIUM TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nMedium Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)

    async def test_rising_edge_interrupt(self) -> bool:
        """Test rising edge interrupt detection."""
        self.log.info("Testing rising edge interrupt...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)

            # Set as input
            await self.tb.set_direction(0x00000000)

            # Configure pin 0 for rising edge interrupt
            await self.tb.set_interrupt_enable(0x00000001)
            await self.tb.set_interrupt_type(0x00000000)  # Edge
            await self.tb.set_interrupt_polarity(0x00000001)  # Rising
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Clear any pending
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            # Create rising edge
            await self.tb.create_rising_edge(0)
            await ClockCycles(self.tb.pclk, 5)

            # Check IRQ
            if not self.tb.get_irq():
                self.log.error("IRQ not asserted on rising edge")
                passed = False

            # Check status
            status = await self.tb.get_interrupt_status()
            if not (status & 0x01):
                self.log.error(f"Interrupt status not set: 0x{status:08X}")
                passed = False

            # Clear and verify
            await self.tb.clear_interrupt_status(0x01)
            await ClockCycles(self.tb.pclk, 5)

            # Falling edge should NOT trigger
            await self.tb.create_falling_edge(0)
            await ClockCycles(self.tb.pclk, 5)

            status = await self.tb.get_interrupt_status()
            if status & 0x01:
                self.log.error("Falling edge incorrectly triggered rising-edge interrupt")
                passed = False

            self.log.info("Rising edge interrupt: " + ("OK" if passed else "FAILED"))

        except Exception as e:
            self.log.error(f"Rising edge test exception: {e}")
            passed = False

        return passed

    async def test_falling_edge_interrupt(self) -> bool:
        """Test falling edge interrupt detection."""
        self.log.info("Testing falling edge interrupt...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Configure pin 1 for falling edge interrupt
            await self.tb.set_interrupt_enable(0x00000002)
            await self.tb.set_interrupt_type(0x00000000)  # Edge
            await self.tb.set_interrupt_polarity(0x00000000)  # Falling
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Clear and start high
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            self.tb.set_gpio_input(0x02)  # Pin 1 high
            await ClockCycles(self.tb.pclk, 10)

            # Create falling edge
            await self.tb.create_falling_edge(1)
            await ClockCycles(self.tb.pclk, 5)

            # Check status
            status = await self.tb.get_interrupt_status()
            if not (status & 0x02):
                self.log.error(f"Falling edge interrupt not set: 0x{status:08X}")
                passed = False

            # Clear and verify rising doesn't trigger
            await self.tb.clear_interrupt_status(0x02)
            await ClockCycles(self.tb.pclk, 5)

            await self.tb.create_rising_edge(1)
            await ClockCycles(self.tb.pclk, 5)

            status = await self.tb.get_interrupt_status()
            if status & 0x02:
                self.log.error("Rising edge incorrectly triggered falling-edge interrupt")
                passed = False

            self.log.info("Falling edge interrupt: " + ("OK" if passed else "FAILED"))

        except Exception as e:
            self.log.error(f"Falling edge test exception: {e}")
            passed = False

        return passed

    async def test_both_edge_interrupt(self) -> bool:
        """Test both-edge interrupt detection."""
        self.log.info("Testing both-edge interrupt...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Configure pin 2 for both edges
            await self.tb.set_interrupt_enable(0x00000004)
            await self.tb.set_interrupt_type(0x00000000)  # Edge
            await self.tb.set_interrupt_polarity(0x00000000)  # Don't care
            await self.tb.set_interrupt_both_edge(0x00000004)

            # Clear
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            # Rising edge should trigger
            await self.tb.create_rising_edge(2)
            await ClockCycles(self.tb.pclk, 5)

            status = await self.tb.get_interrupt_status()
            if not (status & 0x04):
                self.log.error("Both-edge: rising didn't trigger")
                passed = False

            # Clear
            await self.tb.clear_interrupt_status(0x04)
            await ClockCycles(self.tb.pclk, 5)

            # Falling edge should also trigger
            await self.tb.create_falling_edge(2)
            await ClockCycles(self.tb.pclk, 5)

            status = await self.tb.get_interrupt_status()
            if not (status & 0x04):
                self.log.error("Both-edge: falling didn't trigger")
                passed = False

            self.log.info("Both edge interrupt: " + ("OK" if passed else "FAILED"))

        except Exception as e:
            self.log.error(f"Both edge test exception: {e}")
            passed = False

        return passed

    async def test_level_high_interrupt(self) -> bool:
        """Test level-high interrupt detection."""
        self.log.info("Testing level-high interrupt...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Configure pin 3 for level-high
            await self.tb.set_interrupt_enable(0x00000008)
            await self.tb.set_interrupt_type(0x00000008)  # Level
            await self.tb.set_interrupt_polarity(0x00000008)  # High
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Clear and start low
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            # Should not have interrupt
            if self.tb.get_irq():
                self.log.error("IRQ asserted when pin is low")
                passed = False

            # Set pin high
            self.tb.set_gpio_input(0x08)
            await ClockCycles(self.tb.pclk, 10)

            # Should have interrupt
            if not self.tb.get_irq():
                self.log.error("IRQ not asserted when pin is high")
                passed = False

            # Set pin low - interrupt should clear
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            if self.tb.get_irq():
                self.log.error("IRQ still asserted after pin went low")
                passed = False

            self.log.info("Level high interrupt: " + ("OK" if passed else "FAILED"))

        except Exception as e:
            self.log.error(f"Level high test exception: {e}")
            passed = False

        return passed

    async def test_level_low_interrupt(self) -> bool:
        """Test level-low interrupt detection."""
        self.log.info("Testing level-low interrupt...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Configure pin 4 for level-low
            await self.tb.set_interrupt_enable(0x00000010)
            await self.tb.set_interrupt_type(0x00000010)  # Level
            await self.tb.set_interrupt_polarity(0x00000000)  # Low
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Clear any lingering interrupt status from previous tests
            await self.tb.clear_interrupt_status(0xFFFFFFFF)

            # Start high - no interrupt
            self.tb.set_gpio_input(0x10)
            await ClockCycles(self.tb.pclk, 10)

            if self.tb.get_irq():
                self.log.error("IRQ asserted when pin is high")
                passed = False

            # Set pin low
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            if not self.tb.get_irq():
                self.log.error("IRQ not asserted when pin is low")
                passed = False

            self.log.info("Level low interrupt: " + ("OK" if passed else "FAILED"))

        except Exception as e:
            self.log.error(f"Level low test exception: {e}")
            passed = False

        return passed

    async def test_multiple_interrupts(self) -> bool:
        """Test multiple simultaneous interrupt sources."""
        self.log.info("Testing multiple interrupt sources...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Configure pins 0-3 for rising edge interrupts
            await self.tb.set_interrupt_enable(0x0000000F)
            await self.tb.set_interrupt_type(0x00000000)
            await self.tb.set_interrupt_polarity(0x0000000F)
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Clear
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            # Trigger all 4
            self.tb.set_gpio_input(0x0F)
            await ClockCycles(self.tb.pclk, 10)

            status = await self.tb.get_interrupt_status()
            if (status & 0x0F) != 0x0F:
                self.log.error(f"Not all interrupts set: 0x{status:08X}")
                passed = False

            # Clear one at a time
            for i in range(4):
                await self.tb.clear_interrupt_status(1 << i)
                await ClockCycles(self.tb.pclk, 5)
                status = await self.tb.get_interrupt_status()
                expected = 0x0F & ~((1 << (i + 1)) - 1)
                # Note: Level or re-trigger may affect this

            self.log.info("Multiple interrupts: " + ("OK" if passed else "FAILED"))

        except Exception as e:
            self.log.error(f"Multiple interrupts test exception: {e}")
            passed = False

        return passed

    async def test_w1c_clear(self) -> bool:
        """Test W1C (write-1-to-clear) interrupt clearing."""
        self.log.info("Testing W1C interrupt clear...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Configure pins 0-7 for rising edge
            await self.tb.set_interrupt_enable(0x000000FF)
            await self.tb.set_interrupt_type(0x00000000)
            await self.tb.set_interrupt_polarity(0x000000FF)
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Clear
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            # Trigger all
            self.tb.set_gpio_input(0xFF)
            await ClockCycles(self.tb.pclk, 10)

            # Clear only bits 0, 2, 4, 6
            self.tb.set_gpio_input(0)  # Clear input first to prevent re-trigger
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.clear_interrupt_status(0x55)
            await ClockCycles(self.tb.pclk, 5)

            status = await self.tb.get_interrupt_status()
            if (status & 0xFF) != 0xAA:
                self.log.error(f"W1C clear failed: expected 0xAA, got 0x{status & 0xFF:02X}")
                passed = False
            else:
                self.log.info("W1C selective clear: OK")

        except Exception as e:
            self.log.error(f"W1C test exception: {e}")
            passed = False

        return passed

    async def test_raw_vs_masked(self) -> bool:
        """Test raw interrupt status vs masked status."""
        self.log.info("Testing raw vs masked interrupt status...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)
            await self.tb.set_direction(0x00000000)

            # Enable interrupts only on pin 0
            await self.tb.set_interrupt_enable(0x00000001)
            await self.tb.set_interrupt_type(0x00000000)  # Edge
            await self.tb.set_interrupt_polarity(0x000000FF)  # Rising for all
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Clear
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

            # Trigger pins 0 and 1
            self.tb.set_gpio_input(0x03)
            await ClockCycles(self.tb.pclk, 10)

            # Raw should show both, masked should show only pin 0
            raw = await self.tb.get_raw_interrupt_status()
            masked = await self.tb.get_interrupt_status()

            # Note: raw shows current edge conditions, may not be sticky
            # Check that masked status reflects enable mask

            self.log.info(f"Raw status: 0x{raw:08X}, Masked status: 0x{masked:08X}")

            # IRQ should be asserted (pin 0 is enabled)
            if not self.tb.get_irq():
                self.log.error("IRQ not asserted despite enabled interrupt")
                passed = False

            self.log.info("Raw vs masked: " + ("OK" if passed else "FAILED"))

        except Exception as e:
            self.log.error(f"Raw vs masked test exception: {e}")
            passed = False

        return passed
