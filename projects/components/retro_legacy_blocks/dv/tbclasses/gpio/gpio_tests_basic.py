# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GPIOBasicTests
# Purpose: GPIO Basic Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
# Subsystem: retro_legacy_blocks/gpio
#
# Created: 2025-11-29
# Updated: 2025-11-30 - Changed to 32-bit data width

"""
GPIO Basic Tests

Basic verification of GPIO functionality including:
- Register access
- Direction control
- Input/output operations
- Interrupt enable/disable
"""

from cocotb.triggers import ClockCycles


class GPIOBasicTests:
    """Basic test methods for GPIO module."""

    def __init__(self, tb):
        """
        Initialize basic tests.

        Args:
            tb: GPIOTB instance
        """
        self.tb = tb
        self.log = tb.log

    async def test_register_access(self) -> bool:
        """Test basic register read/write access (32-bit registers)."""
        self.log.info("Testing register access...")
        passed = True

        try:
            from .gpio_tb import GPIORegisterMap

            # Test GPIO_CONTROL
            await self.tb.write_register(GPIORegisterMap.GPIO_CONTROL, 0x03)
            _, ctrl = await self.tb.read_register(GPIORegisterMap.GPIO_CONTROL)
            if ctrl != 0x03:
                self.log.error(f"GPIO_CONTROL mismatch: wrote 0x03, read 0x{ctrl:08X}")
                passed = False
            else:
                self.log.info(f"GPIO_CONTROL: OK (0x{ctrl:08X})")

            # Test direction register (32-bit)
            await self.tb.write_register(GPIORegisterMap.GPIO_DIRECTION, 0x5555AAAA)
            _, direction = await self.tb.read_register(GPIORegisterMap.GPIO_DIRECTION)
            if direction != 0x5555AAAA:
                self.log.error(f"GPIO_DIRECTION mismatch: wrote 0x5555AAAA, read 0x{direction:08X}")
                passed = False
            else:
                self.log.info(f"GPIO_DIRECTION: OK (0x{direction:08X})")

            # Test output register (32-bit)
            await self.tb.write_register(GPIORegisterMap.GPIO_OUTPUT, 0x12345678)
            _, output = await self.tb.read_register(GPIORegisterMap.GPIO_OUTPUT)
            if output != 0x12345678:
                self.log.error(f"GPIO_OUTPUT mismatch: wrote 0x12345678, read 0x{output:08X}")
                passed = False
            else:
                self.log.info(f"GPIO_OUTPUT: OK (0x{output:08X})")

            # Reset to defaults
            await self.tb.write_register(GPIORegisterMap.GPIO_CONTROL, 0x01)
            await self.tb.write_register(GPIORegisterMap.GPIO_DIRECTION, 0x00000000)

        except Exception as e:
            self.log.error(f"Register access test exception: {e}")
            passed = False

        return passed

    async def test_direction_control(self) -> bool:
        """Test GPIO direction control."""
        self.log.info("Testing direction control...")
        passed = True

        try:
            # Enable GPIO
            await self.tb.enable_gpio(True, False)

            # Set some pins as outputs
            await self.tb.set_direction(0x0000FFFF)  # Lower 16 as outputs
            await ClockCycles(self.tb.pclk, 5)

            # Verify OE reflects direction
            oe = self.tb.get_gpio_oe()
            if oe != 0x0000FFFF:
                self.log.error(f"GPIO OE mismatch: expected 0x0000FFFF, got 0x{oe:08X}")
                passed = False
            else:
                self.log.info(f"Direction control: OK (OE=0x{oe:08X})")

            # Test alternating pattern
            await self.tb.set_direction(0xAAAAAAAA)
            await ClockCycles(self.tb.pclk, 5)
            oe = self.tb.get_gpio_oe()
            if oe != 0xAAAAAAAA:
                self.log.error(f"GPIO OE mismatch: expected 0xAAAAAAAA, got 0x{oe:08X}")
                passed = False

            # Disable GPIO - OE should go to 0
            await self.tb.enable_gpio(False, False)
            await ClockCycles(self.tb.pclk, 5)
            oe = self.tb.get_gpio_oe()
            if oe != 0:
                self.log.error(f"GPIO OE should be 0 when disabled, got 0x{oe:08X}")
                passed = False

            # Re-enable
            await self.tb.enable_gpio(True, False)

        except Exception as e:
            self.log.error(f"Direction control test exception: {e}")
            passed = False

        return passed

    async def test_output_operation(self) -> bool:
        """Test GPIO output operations."""
        self.log.info("Testing output operations...")
        passed = True

        try:
            # Enable GPIO and set all as outputs
            await self.tb.enable_gpio(True, False)
            await self.tb.set_direction(0xFFFFFFFF)

            # Test output data
            test_values = [0x00000000, 0xFFFFFFFF, 0xAAAAAAAA, 0x55555555, 0x12345678]
            for val in test_values:
                await self.tb.set_output(val)
                await ClockCycles(self.tb.pclk, 5)
                out = self.tb.get_gpio_output()
                if out != val:
                    self.log.error(f"Output mismatch: wrote 0x{val:08X}, read 0x{out:08X}")
                    passed = False
                else:
                    self.log.info(f"Output 0x{val:08X}: OK")

        except Exception as e:
            self.log.error(f"Output operation test exception: {e}")
            passed = False

        return passed

    async def test_input_operation(self) -> bool:
        """Test GPIO input operations."""
        self.log.info("Testing input operations...")
        passed = True

        try:
            # Enable GPIO and set all as inputs
            await self.tb.enable_gpio(True, False)
            await self.tb.set_direction(0x00000000)

            # Test input sampling (with synchronization delay)
            test_values = [0x00000000, 0xFFFFFFFF, 0xAAAAAAAA, 0x55555555, 0x12345678]
            for val in test_values:
                self.tb.set_gpio_input(val)
                # Wait for synchronization (2 stages + margin)
                await ClockCycles(self.tb.pclk, 10)
                inp = await self.tb.get_input()
                if inp != val:
                    self.log.error(f"Input mismatch: set 0x{val:08X}, read 0x{inp:08X}")
                    passed = False
                else:
                    self.log.info(f"Input 0x{val:08X}: OK")

        except Exception as e:
            self.log.error(f"Input operation test exception: {e}")
            passed = False

        return passed

    async def test_atomic_set_clear_toggle(self) -> bool:
        """Test atomic set/clear/toggle operations."""
        self.log.info("Testing atomic set/clear/toggle...")
        passed = True

        try:
            # Enable GPIO and set all as outputs
            await self.tb.enable_gpio(True, False)
            await self.tb.set_direction(0xFFFFFFFF)

            # Start with 0
            await self.tb.set_output(0x00000000)
            await ClockCycles(self.tb.pclk, 5)

            # Test atomic SET
            await self.tb.atomic_set(0x0000000F)  # Set bits 0-3
            await ClockCycles(self.tb.pclk, 5)
            out = self.tb.get_gpio_output()
            if out != 0x0000000F:
                self.log.error(f"Atomic SET failed: expected 0x0000000F, got 0x{out:08X}")
                passed = False
            else:
                self.log.info("Atomic SET: OK")

            # Test atomic SET again (should add more bits)
            await self.tb.atomic_set(0x000000F0)  # Set bits 4-7
            await ClockCycles(self.tb.pclk, 5)
            out = self.tb.get_gpio_output()
            if out != 0x000000FF:
                self.log.error(f"Atomic SET 2 failed: expected 0x000000FF, got 0x{out:08X}")
                passed = False

            # Test atomic CLEAR
            await self.tb.atomic_clear(0x0000000F)  # Clear bits 0-3
            await ClockCycles(self.tb.pclk, 5)
            out = self.tb.get_gpio_output()
            if out != 0x000000F0:
                self.log.error(f"Atomic CLEAR failed: expected 0x000000F0, got 0x{out:08X}")
                passed = False
            else:
                self.log.info("Atomic CLEAR: OK")

            # Test atomic TOGGLE
            await self.tb.atomic_toggle(0x0000FFFF)  # Toggle bits 0-15
            await ClockCycles(self.tb.pclk, 5)
            out = self.tb.get_gpio_output()
            if out != 0x0000FF0F:  # 0xF0 ^ 0xFFFF = 0xFF0F
                self.log.error(f"Atomic TOGGLE failed: expected 0x0000FF0F, got 0x{out:08X}")
                passed = False
            else:
                self.log.info("Atomic TOGGLE: OK")

        except Exception as e:
            self.log.error(f"Atomic operations test exception: {e}")
            passed = False

        return passed

    async def test_interrupt_enable(self) -> bool:
        """Test interrupt enable configuration."""
        self.log.info("Testing interrupt enable...")
        passed = True

        try:
            # Enable GPIO with global interrupt
            await self.tb.enable_gpio(True, True)

            # Configure interrupt for pin 0: rising edge
            await self.tb.set_interrupt_enable(0x00000001)
            await self.tb.set_interrupt_type(0x00000000)  # Edge
            await self.tb.set_interrupt_polarity(0x00000001)  # Rising
            await self.tb.set_interrupt_both_edge(0x00000000)

            # Verify IRQ is low initially
            if self.tb.get_irq():
                self.log.warning("IRQ unexpectedly high before edge")

            # Create rising edge on pin 0
            await self.tb.create_rising_edge(0)
            await ClockCycles(self.tb.pclk, 10)

            # Check IRQ
            if not self.tb.get_irq():
                self.log.error("IRQ not asserted after rising edge")
                passed = False
            else:
                self.log.info("IRQ asserted on rising edge: OK")

            # Clear interrupt status
            await self.tb.clear_interrupt_status(0xFFFFFFFF)
            await ClockCycles(self.tb.pclk, 5)

            # Clear input
            self.tb.set_gpio_input(0)
            await ClockCycles(self.tb.pclk, 10)

        except Exception as e:
            self.log.error(f"Interrupt enable test exception: {e}")
            passed = False

        return passed

    async def test_global_enable(self) -> bool:
        """Test global GPIO enable/disable."""
        self.log.info("=== Scenario GPIO-06: Interrupt Enable ===")
        self.log.info("=== Scenario GPIO-05: Atomic Set/Clear/Toggle ===")
        self.log.info("=== Scenario GPIO-04: Input Operation ===")
        self.log.info("=== Scenario GPIO-03: Output Operation ===")
        self.log.info("=== Scenario GPIO-02: Direction Control ===")
        self.log.info("=== Scenario GPIO-01: Register Access ===")
        self.log.info("Testing global enable...")
        passed = True

        try:
            # Set outputs
            await self.tb.set_direction(0xFFFFFFFF)
            await self.tb.set_output(0xAAAAAAAA)

            # Enable GPIO
            await self.tb.enable_gpio(True, False)
            await ClockCycles(self.tb.pclk, 5)

            # OE should match direction
            oe = self.tb.get_gpio_oe()
            if oe != 0xFFFFFFFF:
                self.log.error(f"OE should be 0xFFFFFFFF when enabled, got 0x{oe:08X}")
                passed = False

            # Disable GPIO
            await self.tb.enable_gpio(False, False)
            await ClockCycles(self.tb.pclk, 5)

            # OE should be 0
            oe = self.tb.get_gpio_oe()
            if oe != 0:
                self.log.error(f"OE should be 0 when disabled, got 0x{oe:08X}")
                passed = False
            else:
                self.log.info("Global enable/disable: OK")

            # Re-enable
            await self.tb.enable_gpio(True, False)

        except Exception as e:
            self.log.error(f"Global enable test exception: {e}")
            passed = False

        return passed
