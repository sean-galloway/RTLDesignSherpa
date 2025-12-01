# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GPIORegisterMap, GPIOTB
# Purpose: GPIO (General Purpose I/O) Testbench
#
# Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
# Subsystem: retro_legacy_blocks/gpio
#
# Created: 2025-11-29
# Updated: 2025-11-30 - Changed to 32-bit data width, s_apb_* naming

"""
GPIO (General Purpose I/O) Testbench

Comprehensive testbench for the APB GPIO module providing:
- Per-bit direction control testing
- Input synchronization verification
- Edge and level interrupt testing
- Atomic set/clear/toggle operations
- Interrupt status W1C verification
- CDC mode testing

Features:
- APB register access
- GPIO input simulation
- GPIO output verification
- Interrupt monitoring
"""

import os
import random
import asyncio
from typing import Dict, List, Optional, Tuple

import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer, FallingEdge, ClockCycles
from cocotb.clock import Clock

from CocoTBFramework.components.apb.apb_packet import APBPacket
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS


class GPIORegisterMap:
    """GPIO Register address definitions (32-bit registers, 4-byte aligned)."""

    # Control Register (0x00)
    GPIO_CONTROL = 0x000         # Global GPIO enable, interrupt enable

    # Direction Register (0x04) - 32-bit
    GPIO_DIRECTION = 0x004       # Direction [31:0] (1=output, 0=input)

    # Output Data Register (0x08) - 32-bit
    GPIO_OUTPUT = 0x008          # Output data [31:0]

    # Input Data Register (0x0C) - Read Only, 32-bit
    GPIO_INPUT = 0x00C           # Input data [31:0]

    # Interrupt Enable Register (0x10) - 32-bit
    GPIO_INT_ENABLE = 0x010      # Interrupt enable [31:0]

    # Interrupt Type Register (0x14) - 32-bit
    GPIO_INT_TYPE = 0x014        # 1=level, 0=edge [31:0]

    # Interrupt Polarity Register (0x18) - 32-bit
    GPIO_INT_POLARITY = 0x018    # 1=high/rising, 0=low/falling [31:0]

    # Interrupt Both Edge Register (0x1C) - 32-bit
    GPIO_INT_BOTH = 0x01C        # 1=both edges [31:0]

    # Interrupt Status Register (0x20) - W1C, 32-bit
    GPIO_INT_STATUS = 0x020      # Interrupt status [31:0]

    # Raw Interrupt Status Register (0x24) - Read Only, 32-bit
    GPIO_RAW_INT = 0x024         # Raw interrupt (pre-mask) [31:0]

    # Atomic Operation Registers - Write Only, 32-bit
    GPIO_OUTPUT_SET = 0x028      # Atomic set [31:0]
    GPIO_OUTPUT_CLR = 0x02C      # Atomic clear [31:0]
    GPIO_OUTPUT_TGL = 0x030      # Atomic toggle [31:0]

    # GPIO_CONTROL bit definitions
    CONTROL_GPIO_ENABLE = (1 << 0)
    CONTROL_INT_ENABLE = (1 << 1)


class GPIOTB(TBBase):
    """
    GPIO Testbench class.

    Provides comprehensive testing infrastructure for the APB GPIO module.
    """

    def __init__(self, dut, **kwargs):
        """
        Initialize GPIO testbench.

        Args:
            dut: DUT (Device Under Test) handle
            **kwargs: Additional arguments for TBBase
        """
        super().__init__(dut)

        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn

        # Components will be initialized in setup_clocks_and_reset
        self.apb_master = None

        # Test tracking
        self.interrupt_events = []

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD)."""
        # Start APB clock (100 MHz = 10ns period)
        await self.start_clock('pclk', freq=10, units='ns')

        # For CDC mode, start GPIO clock
        if hasattr(self.dut, 'gpio_clk'):
            await self.start_clock('gpio_clk', freq=10, units='ns')

        # Initialize GPIO inputs to 0
        self.dut.gpio_in.value = 0

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def setup_components(self):
        """Initialize APB components (call after setup_clocks_and_reset)."""
        self.log.info("Setting up GPIO testbench components")

        try:
            # Create APB Master
            self.apb_master = APBMaster(
                entity=self.dut,
                title='GPIO APB Master',
                prefix='s_apb_',  # Consistent s_apb_* naming
                clock=self.dut.pclk,
                bus_width=32,
                addr_width=12,
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log
            )

            # Properly initialize the APB master
            await self.apb_master.reset_bus()
            self.log.info(f"APB Master created and initialized: {type(self.apb_master)}")

        except Exception as e:
            self.log.error(f"Failed to create APB Master: {e}")
            raise

        self.log.info("GPIO testbench components setup complete")

    async def assert_reset(self):
        """Assert reset (MANDATORY METHOD)."""
        self.presetn.value = 0           # Active-low APB reset
        if hasattr(self.dut, 'gpio_rstn'):
            self.dut.gpio_rstn.value = 0 # Active-low GPIO reset for CDC mode

    async def deassert_reset(self):
        """Deassert reset (MANDATORY METHOD)."""
        self.presetn.value = 1           # Release active-low APB reset
        if hasattr(self.dut, 'gpio_rstn'):
            self.dut.gpio_rstn.value = 1 # Release active-low GPIO reset

    # ========================================================================
    # Register Access Methods
    # ========================================================================

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """Write to GPIO register using correct APB master API (32-bit)."""
        try:
            # Create APB packet
            write_packet = APBPacket(
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=0xF,  # 32-bit access
                pprot=0,
                data_width=32,
                addr_width=12,
                strb_width=4
            )

            write_packet.direction = 'WRITE'

            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            await self.apb_master.send(write_packet)

            # Wait for transaction to complete
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            await RisingEdge(self.dut.pclk)
            return write_packet

        except Exception as e:
            self.log.error(f"Write register failed: {e}")
            raise

    async def read_register(self, addr: int) -> Tuple[APBPacket, int]:
        """Read from GPIO register using correct APB master API (32-bit)."""
        try:
            # Create APB packet
            read_packet = APBPacket(
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0xF,  # 32-bit access
                pprot=0,
                data_width=32,
                addr_width=12,
                strb_width=4
            )

            read_packet.direction = 'READ'

            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            await self.apb_master.send(read_packet)

            # Wait for transaction to complete
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            # Capture read data
            read_data = int(self.dut.s_apb_PRDATA.value)
            read_packet.fields['prdata'] = read_data

            await RisingEdge(self.dut.pclk)
            return read_packet, read_data

        except Exception as e:
            self.log.error(f"Read register failed: {e}")
            raise

    # ========================================================================
    # GPIO Configuration Helpers
    # ========================================================================

    async def enable_gpio(self, enable: bool = True, int_enable: bool = False):
        """
        Enable/disable GPIO and global interrupt.

        Args:
            enable: Enable GPIO globally
            int_enable: Enable global interrupt
        """
        control = 0
        if enable:
            control |= GPIORegisterMap.CONTROL_GPIO_ENABLE
        if int_enable:
            control |= GPIORegisterMap.CONTROL_INT_ENABLE
        await self.write_register(GPIORegisterMap.GPIO_CONTROL, control)

    async def set_direction(self, direction: int):
        """
        Set GPIO direction (1=output, 0=input).

        Args:
            direction: 32-bit direction mask
        """
        await self.write_register(GPIORegisterMap.GPIO_DIRECTION, direction)

    async def get_direction(self) -> int:
        """
        Get GPIO direction.

        Returns:
            32-bit direction mask
        """
        _, data = await self.read_register(GPIORegisterMap.GPIO_DIRECTION)
        return data

    async def set_output(self, data: int):
        """
        Set GPIO output data.

        Args:
            data: 32-bit output data
        """
        await self.write_register(GPIORegisterMap.GPIO_OUTPUT, data)

    async def get_output(self) -> int:
        """
        Get GPIO output data register value.

        Returns:
            32-bit output data
        """
        _, data = await self.read_register(GPIORegisterMap.GPIO_OUTPUT)
        return data

    async def get_input(self) -> int:
        """
        Get GPIO input data (synchronized).

        Returns:
            32-bit input data
        """
        _, data = await self.read_register(GPIORegisterMap.GPIO_INPUT)
        return data

    async def atomic_set(self, mask: int):
        """
        Atomically set GPIO output bits.

        Args:
            mask: Bits to set (1=set)
        """
        await self.write_register(GPIORegisterMap.GPIO_OUTPUT_SET, mask)

    async def atomic_clear(self, mask: int):
        """
        Atomically clear GPIO output bits.

        Args:
            mask: Bits to clear (1=clear)
        """
        await self.write_register(GPIORegisterMap.GPIO_OUTPUT_CLR, mask)

    async def atomic_toggle(self, mask: int):
        """
        Atomically toggle GPIO output bits.

        Args:
            mask: Bits to toggle (1=toggle)
        """
        await self.write_register(GPIORegisterMap.GPIO_OUTPUT_TGL, mask)

    # ========================================================================
    # Interrupt Configuration
    # ========================================================================

    async def set_interrupt_enable(self, mask: int):
        """
        Set per-pin interrupt enable.

        Args:
            mask: 32-bit interrupt enable mask
        """
        await self.write_register(GPIORegisterMap.GPIO_INT_ENABLE, mask)

    async def set_interrupt_type(self, level_mask: int):
        """
        Set interrupt type (1=level, 0=edge).

        Args:
            level_mask: 32-bit type mask
        """
        await self.write_register(GPIORegisterMap.GPIO_INT_TYPE, level_mask)

    async def set_interrupt_polarity(self, polarity: int):
        """
        Set interrupt polarity (1=high/rising, 0=low/falling).

        Args:
            polarity: 32-bit polarity mask
        """
        await self.write_register(GPIORegisterMap.GPIO_INT_POLARITY, polarity)

    async def set_interrupt_both_edge(self, both_mask: int):
        """
        Set both-edge interrupt mode.

        Args:
            both_mask: 32-bit both-edge mask
        """
        await self.write_register(GPIORegisterMap.GPIO_INT_BOTH, both_mask)

    async def get_interrupt_status(self) -> int:
        """
        Get interrupt status.

        Returns:
            32-bit interrupt status
        """
        _, data = await self.read_register(GPIORegisterMap.GPIO_INT_STATUS)
        return data

    async def clear_interrupt_status(self, mask: int):
        """
        Clear interrupt status (W1C).

        Args:
            mask: Bits to clear
        """
        await self.write_register(GPIORegisterMap.GPIO_INT_STATUS, mask)

    async def get_raw_interrupt_status(self) -> int:
        """
        Get raw interrupt status (before mask).

        Returns:
            32-bit raw interrupt status
        """
        _, data = await self.read_register(GPIORegisterMap.GPIO_RAW_INT)
        return data

    # ========================================================================
    # GPIO Pin Simulation
    # ========================================================================

    def set_gpio_input(self, value: int):
        """
        Set GPIO input pins value.

        Args:
            value: 32-bit input value
        """
        self.dut.gpio_in.value = value

    def get_gpio_output(self) -> int:
        """
        Get GPIO output pins value.

        Returns:
            32-bit output value
        """
        return int(self.dut.gpio_out.value)

    def get_gpio_oe(self) -> int:
        """
        Get GPIO output enable.

        Returns:
            32-bit output enable mask
        """
        return int(self.dut.gpio_oe.value)

    def get_irq(self) -> bool:
        """
        Get interrupt request state.

        Returns:
            True if IRQ is asserted
        """
        return bool(self.dut.irq.value)

    async def pulse_gpio_input(self, bit: int, cycles: int = 5):
        """
        Pulse a GPIO input bit high then low.

        Args:
            bit: Bit number (0-31)
            cycles: Number of cycles to hold high
        """
        current = int(self.dut.gpio_in.value)
        self.dut.gpio_in.value = current | (1 << bit)
        await ClockCycles(self.pclk, cycles)
        self.dut.gpio_in.value = current & ~(1 << bit)
        await ClockCycles(self.pclk, 2)

    async def create_rising_edge(self, bit: int):
        """
        Create a rising edge on GPIO input.

        Args:
            bit: Bit number (0-31)
        """
        current = int(self.dut.gpio_in.value)
        # Ensure low first
        self.dut.gpio_in.value = current & ~(1 << bit)
        await ClockCycles(self.pclk, 5)
        # Then set high
        self.dut.gpio_in.value = current | (1 << bit)
        await ClockCycles(self.pclk, 5)

    async def create_falling_edge(self, bit: int):
        """
        Create a falling edge on GPIO input.

        Args:
            bit: Bit number (0-31)
        """
        current = int(self.dut.gpio_in.value)
        # Ensure high first
        self.dut.gpio_in.value = current | (1 << bit)
        await ClockCycles(self.pclk, 5)
        # Then set low
        self.dut.gpio_in.value = current & ~(1 << bit)
        await ClockCycles(self.pclk, 5)
