"""
GAXI Buffer Sequence Classes

This module provides specialized sequence generators for GAXI buffer testing
with multi-field support (addr, ctrl, data0, data1).
"""

import itertools
import random
from typing import Dict, List, Any, Optional, Union
from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.components.flex_randomizer import FlexRandomizer


class GAXIBufferSequence(GAXISequence):
    """
    Extended sequence generator for GAXI buffer tests with multi-field support.
    
    This class expands on the base GAXISequence to add specific patterns and 
    sequences suitable for testing GAXI buffer components with multiple fields
    (addr, ctrl, data0, data1).
    """
    
    def __init__(self, name, field_config, packet_class=GAXIPacket):
        """
        Initialize the GAXI buffer sequence.
        
        Args:
            name: Sequence name
            field_config: Field configuration for multi-field packets
            packet_class: Class to use for packet creation
        """
        super().__init__(name, field_config, packet_class)
        
        # Extract field widths from the field_config
        if isinstance(field_config, FieldConfig):
            # Get field widths from FieldConfig object
            self.addr_width = field_config.get_field('addr').bits
            self.ctrl_width = field_config.get_field('ctrl').bits
            self.data0_width = field_config.get_field('data0').bits
            self.data1_width = field_config.get_field('data1').bits
        else:
            # Get field widths from dictionary
            self.addr_width = field_config['addr']['bits']
            self.ctrl_width = field_config['ctrl']['bits']
            self.data0_width = field_config['data0']['bits']
            self.data1_width = field_config['data1']['bits']
    
    def add_multi_field_transaction(self, addr=0, ctrl=0, data0=0, data1=0, delay=0):
        """
        Add a transaction with values for all fields.
        
        Args:
            addr: Address value
            ctrl: Control value
            data0: Data0 value
            data1: Data1 value
            delay: Delay after transaction
            
        Returns:
            Self for method chaining
        """
        field_values = {
            'addr': addr,
            'ctrl': ctrl,
            'data0': data0,
            'data1': data1
        }
        return self.add_transaction(field_values, delay)
    
    def add_incrementing_pattern(self, count, start_value=0, addr_step=1, ctrl_step=1, 
                                data0_step=1, data1_step=1, delay=0):
        """
        Add transactions with incrementing values for all fields.
        
        Args:
            count: Number of transactions to generate
            start_value: Base starting value for all fields
            addr_step: Increment step for address field
            ctrl_step: Increment step for control field
            data0_step: Increment step for data0 field
            data1_step: Increment step for data1 field
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        for i in range(count):
            addr = start_value + (i * addr_step)
            ctrl = start_value + (i * ctrl_step)
            data0 = start_value + (i * data0_step)
            data1 = start_value + (i * data1_step)
            
            self.add_multi_field_transaction(
                addr=addr,
                ctrl=ctrl,
                data0=data0,
                data1=data1,
                delay=delay
            )
        
        return self
    
    def add_walking_ones_pattern(self, delay=0):
        """
        Add transactions with walking ones pattern across all fields.
        The pattern moves from LSB to MSB through each field in sequence.
        
        Args:
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Calculate total bits across all fields
        total_bits = self.addr_width + self.ctrl_width + self.data0_width + self.data1_width
        
        for bit_position in range(total_bits):
            # Determine which field this bit belongs to
            if bit_position < self.addr_width:
                # This bit is in the addr field
                addr = 1 << bit_position
                ctrl = 0
                data0 = 0
                data1 = 0
            elif bit_position < (self.addr_width + self.ctrl_width):
                # This bit is in the ctrl field
                addr = 0
                ctrl = 1 << (bit_position - self.addr_width)
                data0 = 0
                data1 = 0
            elif bit_position < (self.addr_width + self.ctrl_width + self.data0_width):
                # This bit is in the data0 field
                addr = 0
                ctrl = 0
                data0 = 1 << (bit_position - self.addr_width - self.ctrl_width)
                data1 = 0
            else:
                # This bit is in the data1 field
                addr = 0
                ctrl = 0
                data0 = 0
                data1 = 1 << (bit_position - self.addr_width - self.ctrl_width - self.data0_width)
            
            self.add_multi_field_transaction(
                addr=addr,
                ctrl=ctrl,
                data0=data0,
                data1=data1,
                delay=delay
            )
        
        return self
    
    def add_field_test_pattern(self, delay=0):
        """
        Add test patterns that exercise all fields individually and together.
        
        Args:
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create masks for each field
        addr_mask = (1 << self.addr_width) - 1
        ctrl_mask = (1 << self.ctrl_width) - 1
        data0_mask = (1 << self.data0_width) - 1
        data1_mask = (1 << self.data1_width) - 1
        
        # Test each field individually
        # Addr only
        self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=0, data1=0, delay=delay)
        
        # Ctrl only
        self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=0, data1=0, delay=delay)
        
        # Data0 only
        self.add_multi_field_transaction(addr=0, ctrl=0, data0=data0_mask, data1=0, delay=delay)
        
        # Data1 only
        self.add_multi_field_transaction(addr=0, ctrl=0, data0=0, data1=data1_mask, delay=delay)
        
        # Test pairs of fields
        # Addr + Ctrl
        self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=0, data1=0, delay=delay)
        
        # Addr + Data0
        self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=data0_mask, data1=0, delay=delay)
        
        # Addr + Data1
        self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=0, data1=data1_mask, delay=delay)
        
        # Ctrl + Data0
        self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=data0_mask, data1=0, delay=delay)
        
        # Ctrl + Data1
        self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=0, data1=data1_mask, delay=delay)
        
        # Data0 + Data1
        self.add_multi_field_transaction(addr=0, ctrl=0, data0=data0_mask, data1=data1_mask, delay=delay)
        
        # Test groups of three fields
        # Addr + Ctrl + Data0
        self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=data0_mask, data1=0, delay=delay)
        
        # Addr + Ctrl + Data1
        self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=0, data1=data1_mask, delay=delay)
        
        # Addr + Data0 + Data1
        self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=data0_mask, data1=data1_mask, delay=delay)
        
        # Ctrl + Data0 + Data1
        self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=data0_mask, data1=data1_mask, delay=delay)
        
        # Test all fields
        # Addr + Ctrl + Data0 + Data1
        self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=data0_mask, data1=data1_mask, delay=delay)
        
        return self
    
    def add_alternating_patterns(self, count, delay=0):
        """
        Add transactions with alternating bit patterns across fields.
        
        Args:
            count: Number of transactions to generate
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create masks for each field
        addr_mask = (1 << self.addr_width) - 1
        ctrl_mask = (1 << self.ctrl_width) - 1
        data0_mask = (1 << self.data0_width) - 1
        data1_mask = (1 << self.data1_width) - 1

        # Patterns
        patterns = [
            # 0x55 = 01010101, 0xAA = 10101010
            {'addr': 0x55555555 & addr_mask, 'ctrl': 0x55 & ctrl_mask, 
                'data0': 0x55555555 & data0_mask, 'data1': 0x55555555 & data1_mask},

            {'addr': 0xAAAAAAAA & addr_mask, 'ctrl': 0xAA & ctrl_mask, 
                'data0': 0xAAAAAAAA & data0_mask, 'data1': 0xAAAAAAAA & data1_mask},

            # 0x33 = 00110011, 0xCC = 11001100
            {'addr': 0x33333333 & addr_mask, 'ctrl': 0x33 & ctrl_mask, 
                'data0': 0x33333333 & data0_mask, 'data1': 0x33333333 & data1_mask},

            {'addr': 0xCCCCCCCC & addr_mask, 'ctrl': 0xCC & ctrl_mask, 
                'data0': 0xCCCCCCCC & data0_mask, 'data1': 0xCCCCCCCC & data1_mask},

            # 0x0F = 00001111, 0xF0 = 11110000
            {'addr': 0x0F0F0F0F & addr_mask, 'ctrl': 0x0F & ctrl_mask, 
                'data0': 0x0F0F0F0F & data0_mask, 'data1': 0x0F0F0F0F & data1_mask},

            {'addr': 0xF0F0F0F0 & addr_mask, 'ctrl': 0xF0 & ctrl_mask, 
                'data0': 0xF0F0F0F0 & data0_mask, 'data1': 0xF0F0F0F0 & data1_mask},
        ]

        # Add transactions with these patterns
        for _, pattern in itertools.product(range(count), patterns):
            self.add_multi_field_transaction(
                addr=pattern['addr'],
                ctrl=pattern['ctrl'],
                data0=pattern['data0'],
                data1=pattern['data1'],
                delay=delay
            )

        return self
    
    def add_random_data_pattern(self, count, delay=0):
        """
        Add transactions with random data in all fields.
        
        Args:
            count: Number of transactions to generate
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create masks for each field
        addr_mask = (1 << self.addr_width) - 1
        ctrl_mask = (1 << self.ctrl_width) - 1
        data0_mask = (1 << self.data0_width) - 1
        data1_mask = (1 << self.data1_width) - 1
        
        # Add random transactions
        for _ in range(count):
            addr = random.randint(0, 0xFFFFFFFF) & addr_mask
            ctrl = random.randint(0, 0xFF) & ctrl_mask
            data0 = random.randint(0, 0xFFFFFFFF) & data0_mask
            data1 = random.randint(0, 0xFFFFFFFF) & data1_mask
            
            self.add_multi_field_transaction(
                addr=addr,
                ctrl=ctrl,
                data0=data0,
                data1=data1,
                delay=delay
            )
        
        return self
    
    def add_boundary_values(self, delay=0):
        """
        Add transactions with boundary values for all fields.
        
        Args:
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create masks for each field
        addr_mask = (1 << self.addr_width) - 1
        ctrl_mask = (1 << self.ctrl_width) - 1
        data0_mask = (1 << self.data0_width) - 1
        data1_mask = (1 << self.data1_width) - 1
        
        # Boundary test cases
        test_cases = [
            # All zeros
            {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': 0},
            
            # All ones
            {'addr': addr_mask, 'ctrl': ctrl_mask, 'data0': data0_mask, 'data1': data1_mask},
            
            # LSB only
            {'addr': 1, 'ctrl': 1, 'data0': 1, 'data1': 1},
            
            # MSB only
            {'addr': 1 << (self.addr_width - 1), 'ctrl': 1 << (self.ctrl_width - 1), 
                'data0': 1 << (self.data0_width - 1), 'data1': 1 << (self.data1_width - 1)},
            
            # All except LSB
            {'addr': addr_mask & ~1, 'ctrl': ctrl_mask & ~1, 
                'data0': data0_mask & ~1, 'data1': data1_mask & ~1},
            
            # All except MSB
            {'addr': addr_mask & ~(1 << (self.addr_width - 1)), 
                'ctrl': ctrl_mask & ~(1 << (self.ctrl_width - 1)), 
                'data0': data0_mask & ~(1 << (self.data0_width - 1)), 
                'data1': data1_mask & ~(1 << (self.data1_width - 1))},
        ]
        
        # Add transactions with boundary values
        for test_case in test_cases:
            self.add_multi_field_transaction(
                addr=test_case['addr'],
                ctrl=test_case['ctrl'],
                data0=test_case['data0'],
                data1=test_case['data1'],
                delay=delay
            )
        
        return self
    
    def add_overflow_test(self, delay=0):
        """
        Add transactions with values that exceed field widths to test masking.
        
        Args:
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create masks and overflow values for each field
        addr_mask = (1 << self.addr_width) - 1
        addr_overflow = addr_mask + random.randint(1, 100)
        
        ctrl_mask = (1 << self.ctrl_width) - 1
        ctrl_overflow = ctrl_mask + random.randint(1, 20)
        
        data0_mask = (1 << self.data0_width) - 1
        data0_overflow = data0_mask + random.randint(1, 100)
        
        data1_mask = (1 << self.data1_width) - 1
        data1_overflow = data1_mask + random.randint(1, 100)
        
        # Add transactions with overflow values
        # Test each field individually
        self.add_multi_field_transaction(addr=addr_overflow, ctrl=0, data0=0, data1=0, delay=delay)
        self.add_multi_field_transaction(addr=0, ctrl=ctrl_overflow, data0=0, data1=0, delay=delay)
        self.add_multi_field_transaction(addr=0, ctrl=0, data0=data0_overflow, data1=0, delay=delay)
        self.add_multi_field_transaction(addr=0, ctrl=0, data0=0, data1=data1_overflow, delay=delay)
        
        # Test all fields with overflow
        self.add_multi_field_transaction(
            addr=addr_overflow,
            ctrl=ctrl_overflow,
            data0=data0_overflow,
            data1=data1_overflow,
            delay=delay
        )
        
        return self
