# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RTCHelper
# Purpose: Human-readable RTC register programming helper
#
# Author: sean galloway
# Created: 2025-11-15

"""
RTC Register Programming Helper

Provides human-readable methods for configuring RTC registers using the
RegisterMap class with auto-generated register definitions.

Example Usage:
    rtc = RTCHelper('rtc_regmap.py', apb_data_width=32, 
                    apb_addr_width=16, start_address=0x0, log=logger)
    
    # Enable RTC with binary counting and 24-hour mode
    rtc.enable_rtc(True, use_system_clock=True, binary_mode=True, hour_24_mode=True)
    
    # Set time to 14:30:45 on 2025-06-15
    rtc.set_time(hours=14, minutes=30, seconds=45, day=15, month=6, year=25)
    
    # Configure alarm for 14:35:00
    rtc.set_alarm(hours=14, minutes=35, seconds=0)
    rtc.enable_alarm(True, enable_interrupt=True)
    
    # Generate APB cycles
    apb_transactions = rtc.generate_apb_cycles()
"""

from typing import List, Dict, Tuple, Optional
from CocoTBFramework.tbclasses.apb.register_map import RegisterMap
from CocoTBFramework.components.apb.apb_packet import APBPacket


class RTCHelper:
    """
    RTC Register Programming Helper
    
    Provides intuitive methods for programming RTC registers without
    needing to know the low-level register/field names.
    """
    
    def __init__(self, regmap_file: str, apb_data_width: int, 
                 apb_addr_width: int, start_address: int, log):
        """
        Initialize RTC helper with register map.
        
        Args:
            regmap_file: Path to generated register map file (e.g., 'rtc_regmap.py')
            apb_data_width: APB bus data width (typically 32)
            apb_addr_width: APB bus address width
            start_address: Base address of RTC in memory map
            log: Logger instance
        """
        self.reg_map = RegisterMap(regmap_file, apb_data_width, 
                                   apb_addr_width, start_address, log)
        self.log = log
        
    def enable_rtc(self, enable: bool = True, 
                   use_system_clock: bool = False,
                   binary_mode: bool = True,
                   hour_24_mode: bool = True):
        """
        Enable or disable the RTC and configure modes.
        
        Args:
            enable: True to enable RTC, False to disable
            use_system_clock: True for system clock (testing), False for 32.768kHz
            binary_mode: True for binary counting, False for BCD
            hour_24_mode: True for 24-hour format, False for 12-hour (AM/PM)
        """
        self.reg_map.write('RTC_CONFIG', 'rtc_enable', 1 if enable else 0)
        self.reg_map.write('RTC_CONFIG', 'clock_select', 1 if use_system_clock else 0)
        self.reg_map.write('RTC_CONFIG', 'bcd_mode', 0 if binary_mode else 1)
        self.reg_map.write('RTC_CONFIG', 'hour_mode_12', 0 if hour_24_mode else 1)
        
        mode_str = f"{'binary' if binary_mode else 'BCD'}, {'24h' if hour_24_mode else '12h'}"
        clock_str = "system clock" if use_system_clock else "32.768kHz"
        self.log.info(f"RTC {'enabled' if enable else 'disabled'} ({mode_str}, {clock_str})")
        
    def set_time(self, hours: int, minutes: int, seconds: int,
                 day: int = 1, month: int = 1, year: int = 0,
                 is_pm: bool = False):
        """
        Set RTC time.
        
        Args:
            hours: Hours (0-23 for 24h mode, 1-12 for 12h mode)
            minutes: Minutes (0-59)
            seconds: Seconds (0-59)
            day: Day of month (1-31)
            month: Month (1-12)
            year: Year (0-99, representing 2000-2099)
            is_pm: PM indicator for 12-hour mode (ignored in 24-hour mode)
        """
        # Enter time set mode
        self.reg_map.write('RTC_CONFIG', 'time_set_mode', 1)
        
        # Write time values
        self.reg_map.write('RTC_SECONDS', 'seconds', seconds)
        self.reg_map.write('RTC_MINUTES', 'minutes', minutes)
        
        # For 12-hour BCD mode, bit 7 indicates PM
        if is_pm:
            hours_val = hours | 0x80
        else:
            hours_val = hours
        self.reg_map.write('RTC_HOURS', 'hours', hours_val)
        
        self.reg_map.write('RTC_DAY', 'day', day)
        self.reg_map.write('RTC_MONTH', 'month', month)
        self.reg_map.write('RTC_YEAR', 'year', year)
        
        # Exit time set mode
        self.reg_map.write('RTC_CONFIG', 'time_set_mode', 0)
        
        pm_str = " PM" if is_pm else " AM" if not is_pm else ""
        self.log.info(f"Time set to {hours:02d}:{minutes:02d}:{seconds:02d}{pm_str}, " +
                     f"20{year:02d}-{month:02d}-{day:02d}")
        
    def read_time_config(self) -> Dict[str, int]:
        """
        Prepare to read current time (in actual usage, this would trigger a read).
        
        Returns:
            Dictionary with register names to read
        """
        # In actual usage with real RegisterMap, this would return read values
        # For now, we return the registers that should be read
        return {
            'seconds': 'RTC_SECONDS.seconds',
            'minutes': 'RTC_MINUTES.minutes',
            'hours': 'RTC_HOURS.hours',
            'day': 'RTC_DAY.day',
            'month': 'RTC_MONTH.month',
            'year': 'RTC_YEAR.year'
        }
        
    def set_alarm(self, hours: int, minutes: int, seconds: int,
                  match_hours: bool = True,
                  match_minutes: bool = True,
                  match_seconds: bool = True):
        """
        Configure alarm time and match fields.
        
        Args:
            hours: Alarm hours (0-23 or 1-12)
            minutes: Alarm minutes (0-59)
            seconds: Alarm seconds (0-59)
            match_hours: True to match hours field
            match_minutes: True to match minutes field
            match_seconds: True to match seconds field
        """
        # Write alarm values
        self.reg_map.write('RTC_ALARM_SEC', 'alarm_seconds', seconds)
        self.reg_map.write('RTC_ALARM_MIN', 'alarm_minutes', minutes)
        self.reg_map.write('RTC_ALARM_HOUR', 'alarm_hours', hours)
        
        # Configure match enables
        self.reg_map.write('RTC_ALARM_MASK', 'sec_match_en', 1 if match_seconds else 0)
        self.reg_map.write('RTC_ALARM_MASK', 'min_match_en', 1 if match_minutes else 0)
        self.reg_map.write('RTC_ALARM_MASK', 'hour_match_en', 1 if match_hours else 0)
        
        match_fields = []
        if match_hours: match_fields.append('H')
        if match_minutes: match_fields.append('M')
        if match_seconds: match_fields.append('S')
        match_str = ':'.join(match_fields) if match_fields else 'none'
        
        self.log.info(f"Alarm set to {hours:02d}:{minutes:02d}:{seconds:02d} (match: {match_str})")
        
    def enable_alarm(self, enable: bool = True, enable_interrupt: bool = True):
        """
        Enable or disable alarm and its interrupt.
        
        Args:
            enable: True to enable alarm comparison
            enable_interrupt: True to enable alarm interrupt
        """
        self.reg_map.write('RTC_CONTROL', 'alarm_enable', 1 if enable else 0)
        self.reg_map.write('RTC_CONTROL', 'alarm_int_enable', 1 if enable_interrupt else 0)
        
        action = "enabled" if enable else "disabled"
        int_action = "enabled" if enable_interrupt else "disabled"
        self.log.info(f"Alarm {action}, interrupt {int_action}")
        
    def enable_second_interrupt(self, enable: bool = True):
        """
        Enable or disable second tick interrupt.
        
        Args:
            enable: True to enable, False to disable
        """
        self.reg_map.write('RTC_CONTROL', 'second_int_enable', 1 if enable else 0)
        self.log.info(f"Second interrupt {'enabled' if enable else 'disabled'}")
        
    def clear_status_flags(self, clear_alarm: bool = False, 
                          clear_second_tick: bool = False):
        """
        Clear status flags (write-1-to-clear).
        
        Args:
            clear_alarm: True to clear alarm flag
            clear_second_tick: True to clear second tick flag
        """
        if clear_alarm:
            self.reg_map.write('RTC_STATUS', 'alarm_flag', 1)
            self.log.info("Alarm flag cleared")
            
        if clear_second_tick:
            self.reg_map.write('RTC_STATUS', 'second_tick', 1)
            self.log.info("Second tick flag cleared")
            
    def read_status_config(self) -> Dict[str, str]:
        """
        Prepare to read status flags.
        
        Returns:
            Dictionary with status register fields to read
        """
        return {
            'alarm_flag': 'RTC_STATUS.alarm_flag',
            'second_tick': 'RTC_STATUS.second_tick',
            'time_valid': 'RTC_STATUS.time_valid',
            'pm_indicator': 'RTC_STATUS.pm_indicator'
        }
        
    def configure_simple_alarm(self, alarm_seconds_from_now: int):
        """
        Configure a simple alarm that triggers N seconds from current time.
        
        This is a simplified interface for testing.
        
        Args:
            alarm_seconds_from_now: Seconds until alarm (assumes current time is 00:00:00)
        """
        # Calculate alarm time (simplified - assumes starting from 00:00:00)
        alarm_mins = alarm_seconds_from_now // 60
        alarm_secs = alarm_seconds_from_now % 60
        alarm_hours = alarm_mins // 60
        alarm_mins = alarm_mins % 60
        
        self.set_alarm(
            hours=alarm_hours,
            minutes=alarm_mins,
            seconds=alarm_secs,
            match_hours=(alarm_hours > 0),
            match_minutes=(alarm_mins > 0 or alarm_hours > 0),
            match_seconds=True
        )
        
        self.log.info(f"Simple alarm configured for {alarm_seconds_from_now}s " +
                     f"({alarm_hours:02d}:{alarm_mins:02d}:{alarm_secs:02d})")
        
    def initialize_defaults(self):
        """
        Initialize RTC with sensible defaults:
        - Enabled
        - Binary counting mode
        - 24-hour mode  
        - System clock (for testing)
        - Time set to 00:00:00 2000-01-01
        - Alarm disabled
        """
        # Configure modes
        self.enable_rtc(
            enable=True,
            use_system_clock=True,  # Use system clock for faster testing
            binary_mode=True,
            hour_24_mode=True
        )
        
        # Set initial time to midnight, Jan 1, 2000
        self.set_time(
            hours=0,
            minutes=0,
            seconds=0,
            day=1,
            month=1,
            year=0
        )
        
        # Disable alarm
        self.enable_alarm(enable=False, enable_interrupt=False)
        
        # Disable second interrupt
        self.enable_second_interrupt(enable=False)
        
        self.log.info("RTC initialized to defaults (00:00:00 2000-01-01)")
        
    def configure_for_testing(self, start_time_seconds: int = 0):
        """
        Configure RTC for rapid testing.
        
        Args:
            start_time_seconds: Starting time in seconds from midnight
        """
        self.enable_rtc(
            enable=True,
            use_system_clock=True,  # Use fast system clock
            binary_mode=True,       # Binary for easy calculation
            hour_24_mode=True       # 24-hour for simplicity
        )
        
        # Calculate time from seconds
        hours = (start_time_seconds // 3600) % 24
        minutes = (start_time_seconds // 60) % 60
        seconds = start_time_seconds % 60
        
        self.set_time(
            hours=hours,
            minutes=minutes,
            seconds=seconds,
            day=1,
            month=1,
            year=25  # 2025
        )
        
        self.log.info(f"RTC configured for testing (start: {hours:02d}:{minutes:02d}:{seconds:02d})")
        
    def generate_apb_cycles(self) -> List[APBPacket]:
        """
        Generate APB bus cycles for all pending register writes.
        
        Returns:
            List of APBPacket objects ready for bus transaction
        """
        return self.reg_map.generate_apb_cycles()
        
    def bcd_to_binary(self, bcd_val: int) -> int:
        """
        Convert BCD value to binary.
        
        Args:
            bcd_val: BCD encoded value
            
        Returns:
            Binary value
        """
        return ((bcd_val >> 4) * 10) + (bcd_val & 0x0F)
        
    def binary_to_bcd(self, binary_val: int) -> int:
        """
        Convert binary value to BCD.
        
        Args:
            binary_val: Binary value
            
        Returns:
            BCD encoded value
        """
        tens = binary_val // 10
        ones = binary_val % 10
        return (tens << 4) | ones
