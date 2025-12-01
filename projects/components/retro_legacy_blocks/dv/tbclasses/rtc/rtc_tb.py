# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RTCRegisterMap, RTCTB
# Purpose: Real-Time Clock (RTC) Testbench
#
# Documentation: projects/components/retro_legacy_blocks/docs/rtc_spec/
# Subsystem: retro_legacy_blocks/rtc
#
# Created: 2025-11-15

"""
Real-Time Clock (RTC) Testbench

Comprehensive testbench for the APB RTC module providing:
- Time-of-day tracking verification
- BCD and binary counting modes
- 24-hour and 12-hour (AM/PM) modes
- Alarm functionality testing
- Leap year handling verification
- Interrupt generation testing

Features:
- APB register access
- Time setting and reading
- Alarm configuration  
- Second tick monitoring
- Status flag verification
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


class RTCRegisterMap:
    """RTC Register address definitions."""

    # Configuration and control registers
    RTC_CONFIG = 0x000      # 0x000: Global configuration
    RTC_CONTROL = 0x004     # 0x004: Control (alarm, interrupt enables)
    RTC_STATUS = 0x008      # 0x008: Status flags

    # Time registers
    RTC_SECONDS = 0x00C     # 0x00C: Current seconds (0-59)
    RTC_MINUTES = 0x010     # 0x010: Current minutes (0-59)
    RTC_HOURS = 0x014       # 0x014: Current hours (0-23 or 1-12)
    RTC_DAY = 0x018         # 0x018: Current day (1-31)
    RTC_MONTH = 0x01C       # 0x01C: Current month (1-12)
    RTC_YEAR = 0x020        # 0x020: Current year (0-99, base 2000)

    # Alarm registers
    RTC_ALARM_SEC = 0x024   # 0x024: Alarm seconds
    RTC_ALARM_MIN = 0x028   # 0x028: Alarm minutes
    RTC_ALARM_HOUR = 0x02C  # 0x02C: Alarm hours
    RTC_ALARM_MASK = 0x030  # 0x030: Alarm field enables

    # RTC_CONFIG bit definitions
    CONFIG_RTC_ENABLE = (1 << 0)
    CONFIG_HOUR_MODE_12 = (1 << 1)
    CONFIG_BCD_MODE = (1 << 2)
    CONFIG_CLOCK_SELECT = (1 << 3)
    CONFIG_TIME_SET_MODE = (1 << 4)

    # RTC_CONTROL bit definitions
    CONTROL_ALARM_ENABLE = (1 << 0)
    CONTROL_ALARM_INT_ENABLE = (1 << 1)
    CONTROL_SECOND_INT_ENABLE = (1 << 2)

    # RTC_STATUS bit definitions
    STATUS_ALARM_FLAG = (1 << 0)
    STATUS_SECOND_TICK = (1 << 1)
    STATUS_TIME_VALID = (1 << 2)
    STATUS_PM_INDICATOR = (1 << 3)

    # RTC_ALARM_MASK bit definitions
    ALARM_MASK_SEC = (1 << 0)
    ALARM_MASK_MIN = (1 << 1)
    ALARM_MASK_HOUR = (1 << 2)


class RTCTB(TBBase):
    """
    RTC Testbench class.

    Provides comprehensive testing infrastructure for the APB RTC module.
    """

    def __init__(self, dut, **kwargs):
        """
        Initialize RTC testbench.

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
        self.alarm_events = []
        self.second_ticks = []

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD)."""
        # Start APB clock (100 MHz = 10ns period)
        await self.start_clock('pclk', freq=10, units='ns')

        # Start RTC clock (for testing, use faster clock)
        # In real hardware this would be 32.768 kHz
        await self.start_clock('rtc_clk', freq=10, units='ns')

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def setup_components(self):
        """Initialize APB components (call after setup_clocks_and_reset)."""
        self.log.info("Setting up RTC testbench components")

        try:
            # Create APB Master - SAME AS PIT/HPET
            self.apb_master = APBMaster(
                entity=self.dut,
                title='RTC APB Master',
                prefix='s_apb_',  # Consistent s_apb_* naming
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

        self.log.info("RTC testbench components setup complete")

    async def assert_reset(self):
        """Assert reset (MANDATORY METHOD)."""
        self.presetn.value = 0           # Active-low APB reset
        self.dut.rtc_resetn.value = 0    # Active-low RTC reset

    async def deassert_reset(self):
        """Deassert reset (MANDATORY METHOD)."""
        self.presetn.value = 1           # Release active-low APB reset
        self.dut.rtc_resetn.value = 1    # Release active-low RTC reset

    # ========================================================================
    # Register Access Methods
    # ========================================================================

    async def write_register(self, addr: int, data: int) -> APBPacket:
        """Write to RTC register using correct APB master API."""
        try:
            # Create APB packet
            write_packet = APBPacket(
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=0xF,
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
        """Read from RTC register using correct APB master API."""
        try:
            # Create APB packet
            read_packet = APBPacket(
                pwrite=0,
                paddr=addr,
                pwdata=0,
                pstrb=0xF,
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
    # RTC Configuration Helpers
    # ========================================================================

    async def enable_rtc(self, enable: bool = True, use_sys_clock: bool = True):
        """
        Enable or disable RTC.

        Args:
            enable: True to enable, False to disable
            use_sys_clock: True to use system clock (for testing), False for RTC clock
        """
        config = 0
        if enable:
            config |= RTCRegisterMap.CONFIG_RTC_ENABLE
        if use_sys_clock:
            config |= RTCRegisterMap.CONFIG_CLOCK_SELECT
        await self.write_register(RTCRegisterMap.RTC_CONFIG, config)

    async def set_time_mode(self, bcd_mode: bool = False, hour_12_mode: bool = False):
        """
        Configure time format modes.

        Args:
            bcd_mode: True for BCD, False for binary
            hour_12_mode: True for 12-hour, False for 24-hour
        """
        _, config = await self.read_register(RTCRegisterMap.RTC_CONFIG)
        if bcd_mode:
            config |= RTCRegisterMap.CONFIG_BCD_MODE
        else:
            config &= ~RTCRegisterMap.CONFIG_BCD_MODE
        if hour_12_mode:
            config |= RTCRegisterMap.CONFIG_HOUR_MODE_12
        else:
            config &= ~RTCRegisterMap.CONFIG_HOUR_MODE_12
        await self.write_register(RTCRegisterMap.RTC_CONFIG, config)

    async def set_time(self, seconds: int, minutes: int, hours: int, 
                       day: int, month: int, year: int):
        """
        Set RTC time.

        Args:
            seconds: Seconds (0-59)
            minutes: Minutes (0-59)
            hours: Hours (0-23 or 1-12)
            day: Day of month (1-31)
            month: Month (1-12)
            year: Year (0-99, base 2000)
        """
        # Enter time set mode
        _, config = await self.read_register(RTCRegisterMap.RTC_CONFIG)
        config |= RTCRegisterMap.CONFIG_TIME_SET_MODE
        await self.write_register(RTCRegisterMap.RTC_CONFIG, config)
        await ClockCycles(self.pclk, 5)

        # Write time values
        await self.write_register(RTCRegisterMap.RTC_SECONDS, seconds)
        await self.write_register(RTCRegisterMap.RTC_MINUTES, minutes)
        await self.write_register(RTCRegisterMap.RTC_HOURS, hours)
        await self.write_register(RTCRegisterMap.RTC_DAY, day)
        await self.write_register(RTCRegisterMap.RTC_MONTH, month)
        await self.write_register(RTCRegisterMap.RTC_YEAR, year)
        await ClockCycles(self.pclk, 5)

        # Exit time set mode
        config &= ~RTCRegisterMap.CONFIG_TIME_SET_MODE
        await self.write_register(RTCRegisterMap.RTC_CONFIG, config)
        await ClockCycles(self.pclk, 5)

    async def read_time(self) -> Dict[str, int]:
        """
        Read current RTC time.

        Returns:
            Dictionary with time values
        """
        _, seconds = await self.read_register(RTCRegisterMap.RTC_SECONDS)
        _, minutes = await self.read_register(RTCRegisterMap.RTC_MINUTES)
        _, hours = await self.read_register(RTCRegisterMap.RTC_HOURS)
        _, day = await self.read_register(RTCRegisterMap.RTC_DAY)
        _, month = await self.read_register(RTCRegisterMap.RTC_MONTH)
        _, year = await self.read_register(RTCRegisterMap.RTC_YEAR)

        return {
            'seconds': seconds & 0xFF,
            'minutes': minutes & 0xFF,
            'hours': hours & 0xFF,
            'day': day & 0xFF,
            'month': month & 0xFF,
            'year': year & 0xFF
        }

    async def set_alarm(self, seconds: int, minutes: int, hours: int,
                        sec_match: bool = True, min_match: bool = True, 
                        hour_match: bool = True):
        """
        Configure alarm.

        Args:
            seconds: Alarm seconds
            minutes: Alarm minutes
            hours: Alarm hours
            sec_match: Enable seconds matching
            min_match: Enable minutes matching
            hour_match: Enable hours matching
        """
        await self.write_register(RTCRegisterMap.RTC_ALARM_SEC, seconds)
        await self.write_register(RTCRegisterMap.RTC_ALARM_MIN, minutes)
        await self.write_register(RTCRegisterMap.RTC_ALARM_HOUR, hours)

        mask = 0
        if sec_match:
            mask |= RTCRegisterMap.ALARM_MASK_SEC
        if min_match:
            mask |= RTCRegisterMap.ALARM_MASK_MIN
        if hour_match:
            mask |= RTCRegisterMap.ALARM_MASK_HOUR

        await self.write_register(RTCRegisterMap.RTC_ALARM_MASK, mask)

    async def enable_alarm(self, enable: bool = True, enable_interrupt: bool = True):
        """
        Enable/disable alarm.

        Args:
            enable: Enable alarm comparison
            enable_interrupt: Enable alarm interrupt
        """
        control = 0
        if enable:
            control |= RTCRegisterMap.CONTROL_ALARM_ENABLE
        if enable_interrupt:
            control |= RTCRegisterMap.CONTROL_ALARM_INT_ENABLE

        await self.write_register(RTCRegisterMap.RTC_CONTROL, control)

    async def read_status(self) -> Dict[str, bool]:
        """
        Read status register.

        Returns:
            Dictionary with status flags
        """
        _, status = await self.read_register(RTCRegisterMap.RTC_STATUS)

        return {
            'alarm_flag': bool(status & RTCRegisterMap.STATUS_ALARM_FLAG),
            'second_tick': bool(status & RTCRegisterMap.STATUS_SECOND_TICK),
            'time_valid': bool(status & RTCRegisterMap.STATUS_TIME_VALID),
            'pm_indicator': bool(status & RTCRegisterMap.STATUS_PM_INDICATOR)
        }

    async def clear_status_flags(self, clear_alarm: bool = False, clear_tick: bool = False):
        """
        Clear status flags (write 1 to clear).

        Args:
            clear_alarm: Clear alarm flag
            clear_tick: Clear second tick flag
        """
        clear_val = 0
        if clear_alarm:
            clear_val |= RTCRegisterMap.STATUS_ALARM_FLAG
        if clear_tick:
            clear_val |= RTCRegisterMap.STATUS_SECOND_TICK

        if clear_val:
            await self.write_register(RTCRegisterMap.RTC_STATUS, clear_val)
