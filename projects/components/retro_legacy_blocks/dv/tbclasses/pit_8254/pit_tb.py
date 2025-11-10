# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PITRegisterMap, PITTB
# Purpose: 8254 PIT (Programmable Interval Timer) Testbench
#
# Documentation: projects/components/retro_legacy_blocks/docs/pit_8254_spec/
# Subsystem: retro_legacy_blocks/pit_8254
#
# Created: 2025-11-06

"""
8254 PIT (Programmable Interval Timer) Testbench

Comprehensive testbench for the APB 8254 PIT module providing:
- 3 independent 16-bit counter testing
- Mode 0 (interrupt on terminal count) verification
- Binary and BCD counting support
- LSB/MSB/both byte access modes
- Control word programming
- Status readback verification
- Interrupt generation testing

Features:
- APB register access
- Counter mode configuration
- Binary/BCD counting verification
- Byte access pattern testing
- OUT signal monitoring
- Status register validation
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


class PITRegisterMap:
    """PIT 8254 Register address definitions."""

    # Global registers
    PIT_CONFIG = 0x000      # 0x000: Global configuration (enable, clock select)
    PIT_CONTROL = 0x004     # 0x004: Control word (8254-compatible)
    PIT_STATUS = 0x008      # 0x008: Read-back status (3×8-bit)
    PIT_RESERVED = 0x00C    # 0x00C: Reserved

    # Counter data registers
    COUNTER0_DATA = 0x010   # 0x010: Counter 0 value (16-bit)
    COUNTER1_DATA = 0x014   # 0x014: Counter 1 value (16-bit)
    COUNTER2_DATA = 0x018   # 0x018: Counter 2 value (16-bit)

    # PIT_CONFIG bit definitions
    CONFIG_PIT_ENABLE = 0
    CONFIG_CLOCK_SELECT = 1

    # PIT_CONTROL bit positions
    CONTROL_BCD = 0
    CONTROL_MODE_LSB = 1
    CONTROL_MODE_MSB = 3
    CONTROL_RW_MODE_LSB = 4
    CONTROL_RW_MODE_MSB = 5
    CONTROL_COUNTER_SELECT_LSB = 6
    CONTROL_COUNTER_SELECT_MSB = 7

    # Counter modes
    MODE_INTERRUPT_ON_TERMINAL_COUNT = 0
    MODE_HW_RETRIGGERABLE_ONE_SHOT = 1
    MODE_RATE_GENERATOR = 2
    MODE_SQUARE_WAVE = 3
    MODE_SW_TRIGGERED_STROBE = 4
    MODE_HW_TRIGGERED_STROBE = 5

    # Read/Write modes
    RW_MODE_LATCH = 0
    RW_MODE_LSB_ONLY = 1
    RW_MODE_MSB_ONLY = 2
    RW_MODE_LSB_THEN_MSB = 3

    # Counter select
    COUNTER_SELECT_0 = 0
    COUNTER_SELECT_1 = 1
    COUNTER_SELECT_2 = 2
    COUNTER_SELECT_READBACK = 3

    # Status byte bit positions
    STATUS_BCD = 0
    STATUS_MODE_LSB = 1
    STATUS_MODE_MSB = 3
    STATUS_RW_MODE_LSB = 4
    STATUS_RW_MODE_MSB = 5
    STATUS_NULL_COUNT = 6
    STATUS_OUT = 7

    @staticmethod
    def make_control_word(bcd: int, mode: int, rw_mode: int, counter_select: int) -> int:
        """Create a control word from individual fields."""
        return (
            (bcd & 0x1) |
            ((mode & 0x7) << 1) |
            ((rw_mode & 0x3) << 4) |
            ((counter_select & 0x3) << 6)
        )

    @staticmethod
    def parse_status_byte(status: int) -> Dict[str, int]:
        """Parse a status byte into individual fields."""
        return {
            'bcd': (status >> 0) & 0x1,
            'mode': (status >> 1) & 0x7,
            'rw_mode': (status >> 4) & 0x3,
            'null_count': (status >> 6) & 0x1,
            'out': (status >> 7) & 0x1,
        }


class PITTB(TBBase):
    """
    PIT 8254 Testbench class.

    Provides comprehensive testing infrastructure for the APB 8254 PIT module.
    """

    def __init__(self, dut, **kwargs):
        """
        Initialize PIT testbench.

        Args:
            dut: DUT (Device Under Test) handle
            **kwargs: Additional arguments for TBBase
        """
        super().__init__(dut)

        self.dut = dut
        self.pclk = dut.pclk
        self.presetn = dut.presetn

        # Configuration
        self.num_counters = 3

        # Components will be initialized in setup_clocks_and_reset
        self.apb_master = None

        # Test tracking
        self.interrupt_events = [[] for _ in range(self.num_counters)]

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD)."""
        # Start APB clock (100 MHz = 10ns period)
        await self.start_clock('pclk', freq=10, units='ns')

        # Start PIT timer clock (100 MHz = 10ns period)
        await self.start_clock('pit_clk', freq=10, units='ns')

        # Set GATE inputs high (counters enabled)
        self.dut.gate_in.value = 0x7  # All 3 GATE inputs high

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def setup_components(self):
        """Initialize APB components (call after setup_clocks_and_reset)."""
        self.log.info("Setting up PIT testbench components")

        try:
            # Create APB Master - SAME AS HPET
            self.apb_master = APBMaster(
                entity=self.dut,
                title='PIT APB Master',
                prefix='s_apb',  # NO UNDERSCORE - matches HPET
                clock=self.dut.pclk,
                bus_width=32,
                addr_width=12,
                randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
                log=self.log
            )

            # Properly initialize the APB master
            await self.apb_master.reset_bus()
            self.log.info(f"✓ APB Master created and initialized: {type(self.apb_master)}")

        except Exception as e:
            self.log.error(f"Failed to create APB Master: {e}")
            raise

        self.log.info("PIT testbench components setup complete")

    async def assert_reset(self):
        """Assert reset (MANDATORY METHOD)."""
        self.presetn.value = 0           # Active-low APB reset
        self.dut.pit_resetn.value = 0    # Active-low PIT reset (matches HPET naming)

    async def deassert_reset(self):
        """Deassert reset (MANDATORY METHOD)."""
        self.presetn.value = 1           # Release active-low APB reset
        self.dut.pit_resetn.value = 1    # Release active-low PIT reset

    # ========================================================================
    # Register Access Methods
    # ========================================================================

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """Write to PIT register using correct APB master API (copied from HPET)."""
        try:
            # Create APB packet with proper field configuration
            write_packet = APBPacket(
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=0xF,  # All 4 bytes enabled for 32-bit
                pprot=0,
                data_width=32,  # Fixed 32-bit data
                addr_width=12,  # Fixed 12-bit addressing
                strb_width=4    # Fixed 4-byte strobe
            )

            # Ensure the packet has a direction attribute
            write_packet.direction = 'WRITE'

            # Initialize transmit_coroutine if needed
            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            # Send using APB master
            await self.apb_master.send(write_packet)

            # Wait for the APB transaction to complete
            # Need to wait for both PSEL and PENABLE, then PREADY
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            # Wait one more cycle for transaction to fully complete
            await RisingEdge(self.dut.pclk)

            return write_packet

        except Exception as e:
            self.log.error(f"Write register failed: {e}")
            raise

    async def read_register(self, addr: int) -> Tuple[APBPacket, int]:
        """Read from PIT register using correct APB master API (copied from HPET)."""
        try:
            # Create APB packet with proper field configuration
            read_packet = APBPacket(
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0xF,  # All 4 bytes enabled for 32-bit
                pprot=0,
                data_width=32,  # Fixed 32-bit data
                addr_width=12,  # Fixed 12-bit addressing
                strb_width=4    # Fixed 4-byte strobe
            )

            # Ensure the packet has a direction attribute
            read_packet.direction = 'READ'

            # Initialize transmit_coroutine if needed
            if not hasattr(self.apb_master, 'transmit_coroutine'):
                self.apb_master.transmit_coroutine = None

            # Send using APB master
            await self.apb_master.send(read_packet)

            # Wait for the APB transaction to complete
            # Need to wait for both PSEL and PENABLE, then PREADY
            timeout = 0
            while timeout < 100:
                await RisingEdge(self.dut.pclk)
                if (self.dut.s_apb_PSEL.value and
                    self.dut.s_apb_PENABLE.value and
                    self.dut.s_apb_PREADY.value):
                    break
                timeout += 1

            # Capture the read data from the bus
            read_data = int(self.dut.s_apb_PRDATA.value)
            read_packet.fields['prdata'] = read_data

            # Wait one more cycle for transaction to fully complete
            await RisingEdge(self.dut.pclk)

            return read_packet, read_data

        except Exception as e:
            self.log.error(f"Read register failed: {e}")
            raise

    async def enable_pit(self, enable: bool = True):
        """
        Enable or disable PIT.

        Args:
            enable: True to enable, False to disable
        """
        config = (1 << PITRegisterMap.CONFIG_PIT_ENABLE) if enable else 0
        await self.write_register(PITRegisterMap.PIT_CONFIG, config)

    async def write_control_word(self, bcd: int, mode: int, rw_mode: int, counter_select: int):
        """
        Write control word to configure a counter.

        Args:
            bcd: 0=binary, 1=BCD
            mode: Counter mode (0-5)
            rw_mode: 0=latch, 1=LSB, 2=MSB, 3=LSB+MSB
            counter_select: 0=ctr0, 1=ctr1, 2=ctr2, 3=readback
        """
        control_word = PITRegisterMap.make_control_word(bcd, mode, rw_mode, counter_select)
        await self.write_register(PITRegisterMap.PIT_CONTROL, control_word)

    async def write_counter(self, counter_id: int, value: int):
        """
        Write counter value.

        Args:
            counter_id: Counter number (0-2)
            value: 16-bit counter value
        """
        addr = PITRegisterMap.COUNTER0_DATA + (counter_id * 4)
        await self.write_register(addr, value & 0xFFFF)

    async def read_counter(self, counter_id: int) -> int:
        """
        Read counter value.

        Args:
            counter_id: Counter number (0-2)

        Returns:
            16-bit counter value
        """
        addr = PITRegisterMap.COUNTER0_DATA + (counter_id * 4)
        _, data = await self.read_register(addr)
        return data & 0xFFFF

    async def read_status(self) -> Tuple[int, int, int]:
        """
        Read status register.

        Returns:
            Tuple of (counter0_status, counter1_status, counter2_status)
        """
        _, status_reg = await self.read_register(PITRegisterMap.PIT_STATUS)
        counter0_status = (status_reg >> 0) & 0xFF
        counter1_status = (status_reg >> 8) & 0xFF
        counter2_status = (status_reg >> 16) & 0xFF
        return (counter0_status, counter1_status, counter2_status)

    # ========================================================================
    # Counter Configuration Helpers
    # ========================================================================

    async def configure_counter_mode0(self, counter_id: int, initial_count: int, bcd: bool = False):
        """
        Configure counter for mode 0 (interrupt on terminal count).

        Args:
            counter_id: Counter number (0-2)
            initial_count: Initial count value (16-bit)
            bcd: True for BCD counting, False for binary
        """
        # Write control word
        await self.write_control_word(
            bcd=1 if bcd else 0,
            mode=PITRegisterMap.MODE_INTERRUPT_ON_TERMINAL_COUNT,
            rw_mode=PITRegisterMap.RW_MODE_LSB_THEN_MSB,  # Use full 16-bit access
            counter_select=counter_id
        )

        # Wait for control word to be processed
        await ClockCycles(self.pclk, 10)

        # Write initial count value
        await self.write_counter(counter_id, initial_count)

        # Wait for count to load
        await ClockCycles(self.pclk, 10)

    async def wait_for_counter_out(self, counter_id: int, timeout_ns: int = 10000) -> bool:
        """
        Wait for counter OUT signal to go high.

        Args:
            counter_id: Counter number (0-2)
            timeout_ns: Timeout in nanoseconds

        Returns:
            True if OUT went high, False if timeout
        """
        start_time = get_sim_time('ns')

        while True:
            # Check OUT signal
            out_signals = self.dut.timer_irq.value
            if (out_signals >> counter_id) & 0x1:
                return True

            # Check timeout
            current_time = get_sim_time('ns')
            if (current_time - start_time) > timeout_ns:
                return False

            # Wait a bit
            await ClockCycles(self.pclk, 1)

    # ========================================================================
    # Verification Helpers
    # ========================================================================

    async def verify_counter_counting(self, counter_id: int, expected_direction: str = 'down') -> bool:
        """
        Verify counter is counting in expected direction.

        Args:
            counter_id: Counter number (0-2)
            expected_direction: 'up' or 'down'

        Returns:
            True if counting in expected direction
        """
        # Read initial value
        value1 = await self.read_counter(counter_id)
        await ClockCycles(self.pclk, 10)

        # Read second value
        value2 = await self.read_counter(counter_id)

        if expected_direction == 'down':
            return value2 < value1
        else:
            return value2 > value1
