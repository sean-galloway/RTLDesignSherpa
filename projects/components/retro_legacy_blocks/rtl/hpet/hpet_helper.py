# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HPETHelper
# Purpose: Human-readable HPET register programming helper
#
# Author: sean galloway
# Created: 2025-11-14

"""
HPET Register Programming Helper

Provides human-readable methods for configuring HPET registers using the
RegisterMap class with auto-generated register definitions.

Example Usage:
    hpet = HPETHelper('hpet_regmap.py', apb_data_width=32, 
                      apb_addr_width=16, start_address=0x0, log=logger)
    
    # Enable HPET main counter
    hpet.enable_main_counter(True)
    
    # Configure timer 0 as periodic with 100ms period at 10MHz
    hpet.configure_timer(timer_id=0, 
                        enable=True,
                        periodic=True, 
                        size_64bit=True,
                        comparator_value=1000000)  # 100ms at 10MHz
    
    # Generate APB cycles
    apb_transactions = hpet.generate_apb_cycles()
"""

from typing import List, Optional
from CocoTBFramework.tbclasses.apb.register_map import RegisterMap
from CocoTBFramework.components.apb.apb_packet import APBPacket


class HPETHelper:
    """
    HPET Register Programming Helper
    
    Provides intuitive methods for programming HPET registers without
    needing to know the low-level register/field names.
    """
    
    def __init__(self, regmap_file: str, apb_data_width: int, 
                 apb_addr_width: int, start_address: int, log):
        """
        Initialize HPET helper with register map.
        
        Args:
            regmap_file: Path to generated register map file (e.g., 'hpet_regmap.py')
            apb_data_width: APB bus data width (typically 32)
            apb_addr_width: APB bus address width
            start_address: Base address of HPET in memory map
            log: Logger instance
        """
        self.reg_map = RegisterMap(regmap_file, apb_data_width, 
                                   apb_addr_width, start_address, log)
        self.log = log
        self.num_timers = 8  # Maximum supported timers
        
    def enable_main_counter(self, enable: bool = True):
        """
        Enable or disable the HPET main counter.
        
        Args:
            enable: True to enable, False to disable
        """
        self.reg_map.write('HPET_CONFIG', 'hpet_enable', 1 if enable else 0)
        self.log.info(f"HPET main counter {'enabled' if enable else 'disabled'}")
        
    def enable_legacy_mode(self, enable: bool = True):
        """
        Enable or disable legacy replacement mode.
        
        In legacy mode, HPET can replace the legacy PIT/RTC timers.
        
        Args:
            enable: True to enable legacy mode, False to disable
        """
        self.reg_map.write('HPET_CONFIG', 'legacy_replacement', 1 if enable else 0)
        self.log.info(f"HPET legacy mode {'enabled' if enable else 'disabled'}")
        
    def set_main_counter(self, value: int):
        """
        Set the main counter value (64-bit).
        
        Args:
            value: Counter value (0 to 2^64-1)
        """
        counter_lo = value & 0xFFFFFFFF
        counter_hi = (value >>32) & 0xFFFFFFFF
        
        self.reg_map.write('HPET_COUNTER_LO', 'counter_lo', counter_lo)
        self.reg_map.write('HPET_COUNTER_HI', 'counter_hi', counter_hi)
        self.log.info(f"HPET main counter set to 0x{value:016X}")
        
    def clear_timer_interrupt(self, timer_id: int):
        """
        Clear interrupt status for a specific timer (write-1-to-clear).
        
        Args:
            timer_id: Timer number (0-7)
        """
        if not 0 <= timer_id < self.num_timers:
            raise ValueError(f"Timer ID must be 0-{self.num_timers-1}")
            
        # Write 1 to clear the interrupt bit
        self.reg_map.write('HPET_STATUS', 'timer_int_status', 1 << timer_id)
        self.log.info(f"Cleared interrupt for timer {timer_id}")
        
    def configure_timer(self, timer_id: int, 
                       enable: bool = True,
                       interrupt_enable: bool = True,
                       periodic: bool = False,
                       size_64bit: bool = True,
                       comparator_value: Optional[int] = None):
        """
        Configure an HPET timer with common settings.
        
        Args:
            timer_id: Timer number (0-7)
            enable: Enable the timer
            interrupt_enable: Enable interrupt generation
            periodic: True for periodic mode, False for one-shot
            size_64bit: True for 64-bit comparator, False for 32-bit
            comparator_value: Optional comparator value to set (64-bit)
        """
        if not 0 <= timer_id < self.num_timers:
            raise ValueError(f"Timer ID must be 0-{self.num_timers-1}")
        
        # Build register names
        config_reg = f"TIMER{timer_id}_TIMER_CONFIG"
        
        # Configure timer settings
        self.reg_map.write(config_reg, 'timer_enable', 1 if enable else 0)
        self.reg_map.write(config_reg, 'timer_int_enable', 1 if interrupt_enable else 0)
        self.reg_map.write(config_reg, 'timer_type', 1 if periodic else 0)
        self.reg_map.write(config_reg, 'timer_size', 1 if size_64bit else 0)
        
        # Set comparator if provided
        if comparator_value is not None:
            self.set_timer_comparator(timer_id, comparator_value)
            
        mode_str = "periodic" if periodic else "one-shot"
        size_str = "64-bit" if size_64bit else "32-bit"
        self.log.info(f"Timer {timer_id} configured: {mode_str}, {size_str}, "
                     f"enable={enable}, int_enable={interrupt_enable}")
        
    def set_timer_comparator(self, timer_id: int, value: int):
        """
        Set the comparator value for a timer.
        
        Args:
            timer_id: Timer number (0-7)
            value: Comparator value (64-bit or 32-bit depending on timer config)
        """
        if not 0 <= timer_id < self.num_timers:
            raise ValueError(f"Timer ID must be 0-{self.num_timers-1}")
            
        comp_lo_reg = f"TIMER{timer_id}_TIMER_COMPARATOR_LO"
        comp_hi_reg = f"TIMER{timer_id}_TIMER_COMPARATOR_HI"
        
        comp_lo = value & 0xFFFFFFFF
        comp_hi = (value >> 32) & 0xFFFFFFFF
        
        self.reg_map.write(comp_lo_reg, 'timer_comp_lo', comp_lo)
        self.reg_map.write(comp_hi_reg, 'timer_comp_hi', comp_hi)
        
        self.log.info(f"Timer {timer_id} comparator set to 0x{value:016X}")
        
    def setup_periodic_timer(self, timer_id: int, period_ticks: int):
        """
        Convenience method to setup a periodic timer.
        
        Args:
            timer_id: Timer number (0-7)
            period_ticks: Number of main counter ticks per period
        """
        self.configure_timer(timer_id=timer_id,
                           enable=True,
                           interrupt_enable=True,
                           periodic=True,
                           size_64bit=True,
                           comparator_value=period_ticks)
        self.log.info(f"Periodic timer {timer_id} configured with period {period_ticks} ticks")
        
    def setup_oneshot_timer(self, timer_id: int, timeout_ticks: int):
        """
        Convenience method to setup a one-shot timer.
        
        Args:
            timer_id: Timer number (0-7)
            timeout_ticks: Number of main counter ticks until interrupt
        """
        self.configure_timer(timer_id=timer_id,
                           enable=True,
                           interrupt_enable=True,
                           periodic=False,
                           size_64bit=True,
                           comparator_value=timeout_ticks)
        self.log.info(f"One-shot timer {timer_id} configured with timeout {timeout_ticks} ticks")
        
    def generate_apb_cycles(self) -> List[APBPacket]:
        """
        Generate APB bus cycles for all pending register writes.
        
        Returns:
            List of APBPacket objects ready for bus transaction
        """
        return self.reg_map.generate_apb_cycles()
        
    def initialize_defaults(self):
        """
        Initialize HPET with sensible defaults:
        - Disable main counter
        - Disable all timers
        - Clear all interrupts
        - Set counter to 0
        """
        # Disable main counter
        self.enable_main_counter(False)
        
        # Reset main counter
        self.set_main_counter(0)
        
        # Disable all timers
        for timer_id in range(self.num_timers):
            config_reg = f"TIMER{timer_id}_TIMER_CONFIG"
            self.reg_map.write(config_reg, 'timer_enable', 0)
            self.reg_map.write(config_reg, 'timer_int_enable', 0)
            
        # Clear all interrupts
        self.reg_map.write('HPET_STATUS', 'timer_int_status', 0xFF)
        
        self.log.info("HPET initialized to defaults")
