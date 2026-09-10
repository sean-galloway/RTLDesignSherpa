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
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS


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
    # GitHub #56 coordinator direction (2026-09-09, test 4): the RTL
    # follow-up adds a sticky W1C RTC_STATUS.commit_timeout bit at the next
    # free bit. rtc_regs.rdl currently uses bits 0-3 (alarm_flag,
    # second_tick, time_valid, pm_indicator) with reserved[31:4], so bit 4
    # is the next free one - this constant anticipates that fix. It does
    # NOT exist in the RTL yet (the bit reads 0, always, because it is part
    # of `reserved`), which is exactly test 4's RED signature.
    STATUS_COMMIT_TIMEOUT = (1 << 4)

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
        self.apb4_master = None

        # Test tracking
        self.alarm_events = []
        self.second_ticks = []

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD).

        Clock periods are read from TEST_APB_CLOCK_PERIOD / TEST_RTC_CLOCK_PERIOD
        (plumbed by the test runner in dv/tests/test_apb4_rtc.py), same pattern
        as gpio_tb.py's TEST_GPIO_CLOCK_PERIOD / pit_tb.py's TEST_PIT_CLOCK_PERIOD.
        Defaults to 10ns/10ns (both clocks edge-identical) which reproduces the
        ORIGINAL hardcoded behaviour exactly, so every existing test-mode test
        (cfg_clock_select=1, selected_clk=pclk - rtc_clk is not even read in
        that mode) is unaffected by this change.

        GitHub #56 (H7/round_3 item 1): the RTC's production configuration
        (cfg_clock_select=0, selected_clk=rtc_clk) is architecturally a 32.768
        kHz crystal against a much faster pclk - a real, non-unity ratio. The
        existing suite runs rtc_clk at the SAME period as pclk, which makes
        every CDC-shaped defect (time-set capture, W1C-undone-by-wide-pulse,
        torn multi-register reads) invisible: at 1:1 the "single pclk pulse"
        r_time_regs_wr is captured on effectively every attempt, and the
        "~30us-wide" second-tick set pulse is only one pclk cycle wide. The
        GH#56 defect-regression suite (rtc_tests_medium.py) sets
        TEST_RTC_CLOCK_PERIOD=100 (10:1) so cfg_clock_select=0 actually
        crosses a real clock-domain boundary; cfg_clock_select=1 tests are
        indifferent to rtc_clk's period entirely, so this ratio is safe to
        apply for the WHOLE run rather than needing a second sim build.
        """
        apb_clock_period_ns = int(os.environ.get('TEST_APB_CLOCK_PERIOD', '10'))
        rtc_clock_period_ns = int(os.environ.get('TEST_RTC_CLOCK_PERIOD', str(apb_clock_period_ns)))

        # Start APB clock (100 MHz = 10ns period by default)
        await self.start_clock('pclk', freq=apb_clock_period_ns, units='ns')

        # Start RTC clock (possibly at a different, non-unity ratio to pclk -
        # see the GH#56 note above). Uses start_rtc_clk() (below) rather than
        # TBBase.start_clock() so the Clock coroutine's task handle is kept -
        # GH#56 coordinator direction test 4 needs to stop and later restart
        # this specific clock mid-test (a commit attempted while rtc_clk is
        # not toggling must report a timeout, not hang silently).
        self.rtc_clock_period_ns = rtc_clock_period_ns
        await self.start_rtc_clk()

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks('pclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('pclk', 5)

    async def start_rtc_clk(self):
        """(Re)start the rtc_clk driver, keeping the task handle so it can be
        stopped later - see setup_clocks_and_reset()'s docstring and
        stop_rtc_clk() below."""
        self._rtc_clk_task = cocotb.start_soon(
            Clock(self.dut.rtc_clk, self.rtc_clock_period_ns, units='ns').start()
        )
        await Timer(100, units='ps')

    def stop_rtc_clk(self):
        """Stop the rtc_clk driver (kills the Clock coroutine). The signal
        freezes at whatever level it was last driven to rather than being
        forced - this is what "the RTC clock has stopped" looks like on real
        hardware (crystal removed / oscillator fault), and it is what GH#56
        coordinator direction test 4 uses to exercise the time-set commit
        handshake's timeout path."""
        if getattr(self, '_rtc_clk_task', None) is not None:
            self._rtc_clk_task.kill()
            self._rtc_clk_task = None

    async def assert_presetn(self):
        """Assert ONLY the APB-domain reset, leaving rtc_resetn untouched.
        GH#56 coordinator direction test 1: the time-set commit crosses via
        the commit handshake (rtc_core.sv's cdc_*_phase_handshake instance -
        deliberately not named here, since the RTL has already swapped which
        primitive it uses once during this review and a hardcoded module
        name in a comment is exactly the kind of doc that goes stale),
        whose source side lives in the presetn domain and destination side
        in the rtc_resetn domain - a reset that touches only one side is the
        scenario the CDC library's own reset-section warning is about
        (rtl/cdc/CLAUDE.md)."""
        self.presetn.value = 0

    async def deassert_presetn(self):
        """Release ONLY the APB-domain reset - see assert_presetn_only()."""
        self.presetn.value = 1

    async def assert_rtc_resetn(self):
        """Assert ONLY the RTC-domain reset, leaving presetn untouched -
        the mirror leg of assert_presetn_only(), see its docstring."""
        self.dut.rtc_resetn.value = 0

    async def deassert_rtc_resetn(self):
        """Release ONLY the RTC-domain reset - see assert_rtc_resetn_only()."""
        self.dut.rtc_resetn.value = 1

    async def setup_components(self):
        """Initialize APB components (call after setup_clocks_and_reset)."""
        self.log.info("Setting up RTC testbench components")

        try:
            # Create APB Master - SAME AS PIT/HPET
            self.apb4_master = APBMaster(
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
            await self.apb4_master.reset_bus()
            self.log.info(f"✓ APB Master created and initialized: {type(self.apb4_master)}")

        except Exception as e:
            self.log.error(f"Failed to create APB Master: {e}")
            raise

        self.log.info("RTC testbench components setup complete")

    async def assert_reset(self):
        """Assert reset (MANDATORY METHOD) - both domains together."""
        await self.assert_presetn()
        await self.assert_rtc_resetn()

    async def deassert_reset(self):
        """Deassert reset (MANDATORY METHOD) - both domains together."""
        await self.deassert_presetn()
        await self.deassert_rtc_resetn()

    # ========================================================================
    # Register Access Methods
    # ========================================================================

    async def write_register(self, addr: int, data: int, pstrb: int = 0xF) -> APBPacket:
        """Write to RTC register using correct APB master API.

        Returns:
            APBPacket. ``.pslverr`` (and equivalently ``.fields['pslverr']``)
            carries the APB slave error response sampled by the framework APB
            master BFM (APBMaster._finish_xmit) once the transaction
            completes - same convention as pit_tb.py/ioapic_tb.py, needed for
            GitHub #56 contract H (address decode / PSLVERR).
        """
        try:
            # Create APB packet
            write_packet = APBPacket(
                pwrite=1,
                paddr=addr,
                pwdata=data,
                pstrb=pstrb,
                pprot=0,
                data_width=32,
                addr_width=12,
                strb_width=4
            )

            write_packet.direction = 'WRITE'

            if not hasattr(self.apb4_master, 'transmit_coroutine'):
                self.apb4_master.transmit_coroutine = None

            await self.apb4_master.send(write_packet)

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

            write_packet.pslverr = write_packet.fields.get('pslverr', 0)
            return write_packet

        except Exception as e:
            self.log.error(f"Write register failed: {e}")
            raise

    async def read_register(self, addr: int) -> Tuple[APBPacket, int]:
        """Read from RTC register using correct APB master API.

        Returns:
            Tuple of (APBPacket, read_value). The packet's ``.pslverr`` (and
            equivalently ``.fields['pslverr']``) carries the APB slave error
            response - see write_register() for the same-timing rationale.
        """
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

            if not hasattr(self.apb4_master, 'transmit_coroutine'):
                self.apb4_master.transmit_coroutine = None

            await self.apb4_master.send(read_packet)

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

            read_packet.pslverr = read_packet.fields.get('pslverr', 0)
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

    # ========================================================================
    # GitHub #56 Whitebox Helpers (rtc_core internals)
    # ========================================================================
    #
    # These directly poke/sample rtc_core's internal registers
    # (dut.u_rtc_core.<signal>, per apb4_rtc.sv's instance name) rather than
    # going through the APB register interface. Two independent reasons this
    # suite needs them, matching the hpet/pm_acpi precedent
    # (force_pm_timer_near_overflow in pm_acpi_tb.py):
    #
    # 1. Speed: production mode's real divider target is 32767 rtc_clk edges
    #    per second (32768-tick divide). At the test's 10:1 ratio that is
    #    327,680 pclk cycles (~3.3ms of sim time) per tick - waiting for a
    #    NATURAL tick in every scenario would make the suite impractically
    #    slow. Forcing r_clk_div_counter close to the target lets a test
    #    reach a real tick in a handful of rtc_clk edges instead.
    #
    # 2. Isolation: contracts D/E/G/C are about the COUNTING/comparison logic
    #    once a given time is loaded, not about the (separately broken, GH#56
    #    contract A/B) time-SET mechanism. Loading r_seconds..r_year directly
    #    lets those tests reach a specific calendar/hour state deterministically
    #    without depending on whether a production-mode APB time-set happened
    #    to land - conflating the two would make a calendar-logic test's
    #    result depend on an unrelated CDC coin flip.

    async def force_time_registers(self, seconds: int, minutes: int, hours: int,
                                    day: int, month: int, year: int,
                                    time_valid: bool = True):
        """
        Whitebox-load rtc_core's counting registers directly, bypassing the
        (separately broken, GH#56 contract A/B) APB time-set path. Values are
        raw byte encodings - pass BCD-encoded bytes (e.g. 0x59) when the core
        is configured for BCD mode, binary otherwise, exactly like the
        existing set_time()/read_time() convention.
        """
        core = self.dut.u_rtc_core
        core.r_seconds.value = seconds & 0xFF
        core.r_minutes.value = minutes & 0xFF
        core.r_hours.value = hours & 0xFF
        core.r_day.value = day & 0xFF
        core.r_month.value = month & 0xFF
        core.r_year.value = year & 0xFF
        core.r_time_valid.value = 1 if time_valid else 0
        self.log.info(
            f"  [whitebox] forced rtc_core time regs -> "
            f"{seconds:02x}:{minutes:02x}:{hours:02x} {day:02x}/{month:02x}/{year:02x}"
        )

    def read_time_registers_whitebox(self) -> Dict[str, int]:
        """Sample rtc_core's counting registers directly (no APB round trip)."""
        core = self.dut.u_rtc_core
        return {
            'seconds': int(core.r_seconds.value),
            'minutes': int(core.r_minutes.value),
            'hours': int(core.r_hours.value),
            'day': int(core.r_day.value),
            'month': int(core.r_month.value),
            'year': int(core.r_year.value),
        }

    async def force_divider_near_target(self, clock_select: int, remaining_cycles: int = 2):
        """
        Whitebox-poke rtc_core.r_clk_div_counter so the NEXT (or next few)
        selected_clk edges roll the second-tick divider over, instead of
        waiting the real 100 (test mode) / 32768 (production mode) cycles.

        Args:
            clock_select: the cfg_clock_select value currently programmed
                (0=rtc_clk/production, target=32767; 1=pclk/test, target=99) -
                must match what CONFIG.clock_select actually holds, since that
                is what rtc_core's own clk_div_target mux selects.
            remaining_cycles: how many selected_clk edges before the forced
                value rolls over (>=1).
        """
        target = 32767 if clock_select == 0 else 99
        core = self.dut.u_rtc_core
        core.r_clk_div_counter.value = max(0, target - remaining_cycles)
        self.log.info(
            f"  [whitebox] forced r_clk_div_counter -> "
            f"{target - remaining_cycles} (target={target}, clock_select={clock_select})"
        )
