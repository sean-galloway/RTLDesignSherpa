# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PITHelper
# Purpose: Human-readable PIT 8254 register programming helper
#
# Author: sean galloway
# Created: 2025-11-14

"""
PIT 8254 Register Programming Helper

Provides human-readable methods for configuring PIT 8254 registers using the
RegisterMap class with auto-generated register definitions.

Example Usage:
    pit = PITHelper('pit_regmap.py', apb_data_width=32, 
                    apb_addr_width=16, start_address=0x0, log=logger)
    
    # Enable PIT globally
    pit.enable_pit(True)
    
    # Configure counter 0 for square wave mode at 1kHz (assuming 1MHz clock)
    pit.configure_counter(counter_id=0, 
                         mode=3,  # Square wave
                         count_value=1000)  # 1MHz/1000 = 1kHz
    
    # Generate APB cycles
    apb_transactions = pit.generate_apb_cycles()
"""

from typing import List
from CocoTBFramework.tbclasses.apb.register_map import RegisterMap
from CocoTBFramework.components.apb.apb_packet import APBPacket


# PIT 8254 Counter Modes
MODE_INTERRUPT_ON_TERMINAL = 0  # Mode 0: Interrupt on terminal count
MODE_ONE_SHOT = 1               # Mode 1: Hardware retriggerable one-shot
MODE_RATE_GENERATOR = 2         # Mode 2: Rate generator (divide by N)
MODE_SQUARE_WAVE = 3            # Mode 3: Square wave generator
MODE_SW_STROBE = 4              # Mode 4: Software triggered strobe
MODE_HW_STROBE = 5              # Mode 5: Hardware triggered strobe


class PITHelper:
    """
    PIT 8254 Register Programming Helper
    
    Provides intuitive methods for programming PIT 8254 registers without
    needing to know the low-level register/field names or 8254 programming sequences.
    """
    
    def __init__(self, regmap_file: str, apb_data_width: int, 
                 apb_addr_width: int, start_address: int, log):
        """
        Initialize PIT helper with register map.
        
        Args:
            regmap_file: Path to generated register map file (e.g., 'pit_regmap.py')
            apb_data_width: APB bus data width (typically 32)
            apb_addr_width: APB bus address width
            start_address: Base address of PIT in memory map
            log: Logger instance
        """
        self.reg_map = RegisterMap(regmap_file, apb_data_width, 
                                   apb_addr_width, start_address, log)
        self.log = log
        self.num_counters = 3  # PIT 8254 has 3 counters
        
    def enable_pit(self, enable: bool = True):
        """
        Enable or disable the PIT globally.
        
        Args:
            enable: True to enable, False to disable all counters
        """
        self.reg_map.write('PIT_CONFIG', 'pit_enable', 1 if enable else 0)
        self.log.info(f"PIT {'enabled' if enable else 'disabled'}")
        
    def set_clock_source(self, use_apb_clock: bool = False):
        """
        Set clock source for all counters.
        
        Args:
            use_apb_clock: True to use APB clock, False to use external clock inputs
        """
        self.reg_map.write('PIT_CONFIG', 'clock_select', 1 if use_apb_clock else 0)
        clock_src = "APB clock" if use_apb_clock else "external clocks"
        self.log.info(f"PIT clock source set to {clock_src}")
        
    def configure_counter(self, counter_id: int, mode: int, count_value: int,
                         bcd_mode: bool = False, rw_mode: int = 3):
        """
        Configure a PIT counter with mode and count value.
        
        Args:
            counter_id: Counter number (0-2)
            mode: Counter operating mode (0-5):
                  0: Interrupt on terminal count
                  1: Hardware retriggerable one-shot
                  2: Rate generator (divide by N)
                  3: Square wave generator
                  4: Software triggered strobe
                  5: Hardware triggered strobe
            count_value: 16-bit count value (1-65535, 0 = 65536)
            bcd_mode: True for BCD counting, False for binary (default)
            rw_mode: Read/write mode (0=latch, 1=LSB only, 2=MSB only, 3=LSB then MSB)
        """
        if not 0 <= counter_id < self.num_counters:
            raise ValueError(f"Counter ID must be 0-{self.num_counters-1}")
        if not 0 <= mode <= 5:
            raise ValueError("Mode must be 0-5")
        if not 0 <= count_value <= 0xFFFF:
            raise ValueError("Count value must be 0-65535")
            
        # Write control word
        self.reg_map.write('PIT_CONTROL', 'counter_select', counter_id)
        self.reg_map.write('PIT_CONTROL', 'rw_mode', rw_mode)
        self.reg_map.write('PIT_CONTROL', 'mode', mode)
        self.reg_map.write('PIT_CONTROL', 'bcd', 1 if bcd_mode else 0)
        
        # Write count value
        counter_data_reg = f"COUNTER{counter_id}_DATA"
        self.reg_map.write(counter_data_reg, f'counter{counter_id}_data', count_value)
        
        mode_names = ["INT_TERM", "ONE_SHOT", "RATE_GEN", "SQUARE", "SW_STROBE", "HW_STROBE"]
        self.log.info(f"Counter {counter_id} configured: mode={mode_names[mode]}, "
                     f"count={count_value}, {'BCD' if bcd_mode else 'binary'}")
        
    def set_square_wave(self, counter_id: int, count_value: int):
        """
        Convenience method to configure a counter for square wave output.
        
        This is the most common use case - generating a square wave clock.
        
        Args:
            counter_id: Counter number (0-2)
            count_value: Count value (output frequency = input_freq / count_value)
        """
        self.configure_counter(counter_id, MODE_SQUARE_WAVE, count_value, 
                              bcd_mode=False, rw_mode=3)
        self.log.info(f"Counter {counter_id} configured for square wave, count={count_value}")
        
    def set_rate_generator(self, counter_id: int, count_value: int):
        """
        Convenience method to configure a counter as a rate generator.
        
        Rate generator produces a pulse every N counts.
        
        Args:
            counter_id: Counter number (0-2)
            count_value: Divide ratio (1-65536)
        """
        self.configure_counter(counter_id, MODE_RATE_GENERATOR, count_value,
                              bcd_mode=False, rw_mode=3)
        self.log.info(f"Counter {counter_id} configured as rate generator, count={count_value}")
        
    def set_one_shot(self, counter_id: int, count_value: int):
        """
        Convenience method to configure a counter for one-shot mode.
        
        One-shot mode triggers once and waits for hardware retrigger.
        
        Args:
            counter_id: Counter number (0-2)
            count_value: Count value before trigger
        """
        self.configure_counter(counter_id, MODE_ONE_SHOT, count_value,
                              bcd_mode=False, rw_mode=3)
        self.log.info(f"Counter {counter_id} configured for one-shot, count={count_value}")
        
    def latch_counter(self, counter_id: int):
        """
        Latch the current count value for reading.
        
        This is used to safely read a counter that's actively counting.
        
        Args:
            counter_id: Counter number (0-2)
        """
        if not 0 <= counter_id < self.num_counters:
            raise ValueError(f"Counter ID must be 0-{self.num_counters-1}")
            
        # Latch command: counter select + rw_mode = 0
        self.reg_map.write('PIT_CONTROL', 'counter_select', counter_id)
        self.reg_map.write('PIT_CONTROL', 'rw_mode', 0)
        
        self.log.info(f"Counter {counter_id} latched for reading")
        
    def setup_pc_speaker_timer(self, frequency_hz: int, clock_freq_hz: int = 1193182):
        """
        Convenience method to setup counter 2 for PC speaker/beeper.
        
        This is a classic use case - generating audio tones.
        
        Args:
            frequency_hz: Desired output frequency in Hz (e.g., 440 for A4 note)
            clock_freq_hz: Input clock frequency (default: 1.193182 MHz, standard PC PIT clock)
        """
        count_value = clock_freq_hz // frequency_hz
        if count_value > 0xFFFF:
            count_value = 0xFFFF
            actual_freq = clock_freq_hz // count_value
            self.log.warning(f"Frequency too low, clamping to {actual_freq} Hz")
        elif count_value < 1:
            count_value = 1
            
        self.set_square_wave(2, count_value)
        actual_freq = clock_freq_hz // count_value
        self.log.info(f"PC speaker configured: requested={frequency_hz}Hz, actual={actual_freq}Hz")
        
    def setup_system_timer(self, rate_hz: int = 1000):
        """
        Convenience method to setup counter 0 as system timer (classic use).
        
        This emulates the standard PC timer interrupt at specified rate.
        
        Args:
            rate_hz: Timer interrupt rate in Hz (default: 1000 Hz = 1ms period)
        """
        # Standard PC PIT clock is 1.193182 MHz
        clock_freq = 1193182
        count_value = clock_freq // rate_hz
        
        self.set_rate_generator(0, count_value)
        actual_rate = clock_freq // count_value
        self.log.info(f"System timer configured: requested={rate_hz}Hz, actual={actual_rate}Hz")
        
    def generate_apb_cycles(self) -> List[APBPacket]:
        """
        Generate APB bus cycles for all pending register writes.
        
        Returns:
            List of APBPacket objects ready for bus transaction
        """
        return self.reg_map.generate_apb_cycles()
        
    def initialize_defaults(self):
        """
        Initialize PIT with sensible defaults:
        - Disable PIT globally
        - Use external clock sources
        - Set all counters to mode 0 (terminal count) with max count
        """
        # Disable PIT
        self.enable_pit(False)
        
        # Use external clocks
        self.set_clock_source(use_apb_clock=False)
        
        # Initialize all counters to safe defaults
        for counter_id in range(self.num_counters):
            self.configure_counter(counter_id, 
                                 mode=MODE_INTERRUPT_ON_TERMINAL,
                                 count_value=0xFFFF,  # Maximum count
                                 bcd_mode=False,
                                 rw_mode=3)
            
        self.log.info("PIT initialized to defaults")
