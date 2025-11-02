# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXIBufferSequence
# Purpose: Updated GAXI Buffer Sequence Classes - Refactored to use FlexConfigGen only
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated GAXI Buffer Sequence Classes - Refactored to use FlexConfigGen only

Key changes:
- Eliminated manual FlexRandomizer instantiation in add_random_pattern
- FlexConfigGen integration for consistent randomization approach
- Simplified randomizer management through centralized configuration
- Enhanced randomization capabilities using FlexConfigGen profiles
- Fixed 'uniform' profile issue by properly defining all profiles
"""

import itertools
import random
from typing import Any
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen


class GAXIBufferSequence(GAXISequence):
    """
    Extended sequence generator for GAXI buffer tests using FlexConfigGen only.

    This class expands on the base GAXISequence to add specific patterns and
    sequences suitable for testing GAXI buffer components with multiple fields
    (addr, ctrl, data0, data1).

    Refactored to use FlexConfigGen for all randomization needs.
    """

    def __init__(self, name, field_config, packet_class=GAXIPacket):
        """
        Initialize the GAXI buffer sequence with FlexConfigGen integration.

        Args:
            name: Sequence name
            field_config: Field configuration for multi-field packets (dict or FieldConfig)
            packet_class: Class to use for packet creation
        """
        print(f"🔍 GAXIBufferSequence.__init__: Step 1 - About to call super().__init__")
        
        # CRITICAL: Call parent initialization FIRST
        super().__init__(name, field_config, packet_class)
        print(f"🔍 GAXIBufferSequence.__init__: Step 1 - ✅ super().__init__ completed")
        
        print(f"🔍 GAXIBufferSequence.__init__: Step 2 - About to extract field widths")
        
        # NOW extract field widths after parent is properly initialized
        try:
            self.addr_width = self._get_field_width('addr')
            print(f"🔍 GAXIBufferSequence.__init__: addr_width = {self.addr_width}")
            
            self.ctrl_width = self._get_field_width('ctrl')
            print(f"🔍 GAXIBufferSequence.__init__: ctrl_width = {self.ctrl_width}")
            
            self.data0_width = self._get_field_width('data0')
            print(f"🔍 GAXIBufferSequence.__init__: data0_width = {self.data0_width}")
            
            self.data1_width = self._get_field_width('data1')
            print(f"🔍 GAXIBufferSequence.__init__: data1_width = {self.data1_width}")
            
            print(f"🔍 GAXIBufferSequence.__init__: Step 2 - ✅ Field widths extracted")
            
        except Exception as e:
            print(f"🚨 ERROR: Field width extraction failed: {e}")
            # Fallback to safe defaults
            self.addr_width = 12
            self.ctrl_width = 6
            self.data0_width = 32
            self.data1_width = 32
            print(f"🔍 GAXIBufferSequence.__init__: Using fallback field widths")
        
        print(f"🔍 GAXIBufferSequence.__init__: Step 3 - About to create randomizer manager")
        
        try:
            self._create_randomizer_manager()
            print(f"🔍 GAXIBufferSequence.__init__: Step 3 - ✅ Randomizer manager created")
        except Exception as e:
            print(f"🚨 ERROR: Randomizer manager creation failed: {e}")
            # Create minimal randomizer setup
            self.randomizer_instances = {}
            print(f"🔍 GAXIBufferSequence.__init__: Using minimal randomizer setup")
        
        print(f"🔍 GAXIBufferSequence.__init__: Step 4 - Setting up enhanced statistics")
        
        # Enhanced statistics tracking
        self.stats.update({
            'multi_field_transactions': 0,
            'boundary_tests': 0,
            'overflow_tests': 0,
            'pattern_tests': 0,
            'burst_tests': 0
        })
        
        print(f"🔍 GAXIBufferSequence.__init__: ✅ ALL INITIALIZATION COMPLETED SUCCESSFULLY!")

    def _create_randomizer_manager(self):
        """Create FlexConfigGen manager for sequence randomization"""
        
        # Define sequence-specific randomization profiles
        sequence_profiles = {
            'seq_uniform': ([(0, 100)], [1]),                          # Uniform distribution
            'seq_weighted': ([(0, 25), (26, 75), (76, 100)], [3, 2, 1]), # Weighted distribution
            'seq_boundary_focus': ([(0, 5), (250, 255)], [1, 1]),     # Focus on boundaries
            'seq_mid_range': ([(40, 60)], [1]),                       # Mid-range values
            'seq_sparse': ([(0, 10), (50, 60), (90, 100)], [1, 1, 1]), # Sparse coverage
        }

        # Create FlexConfigGen for sequence randomization
        # Only use profiles that exist as defaults or are defined as custom profiles
        config_gen = FlexConfigGen(
            profiles=[
                'moderate', 'balanced', 'constrained', 'chaotic',
                'seq_uniform', 'seq_weighted', 'seq_boundary_focus', 
                'seq_mid_range', 'seq_sparse'
            ],
            fields=['addr_range', 'ctrl_range', 'data0_range', 'data1_range'],
            custom_profiles=sequence_profiles
        )

        # Customize profiles for sequence generation
        self._customize_sequence_profiles(config_gen)

        # Build and store randomizer instances
        self.randomizer_instances = config_gen.build(return_flexrandomizer=True)
        
        # Set default randomizer for sequence generation
        self.sequence_randomizer = self.randomizer_instances.get('balanced', None)
        self.use_randomization = True

        print(f"Created {len(self.randomizer_instances)} sequence randomizer profiles")

    def _customize_sequence_profiles(self, config_gen):
        """Customize FlexConfigGen profiles for sequence generation"""
        
        # Calculate field maximums
        addr_max = (1 << self.addr_width) - 1
        ctrl_max = (1 << self.ctrl_width) - 1
        data0_max = (1 << self.data0_width) - 1
        data1_max = (1 << self.data1_width) - 1
        
        # Balanced profile for general sequence use
        config_gen.balanced.addr_range.uniform_range(0, addr_max)
        config_gen.balanced.ctrl_range.uniform_range(0, ctrl_max)
        config_gen.balanced.data0_range.uniform_range(0, data0_max)
        config_gen.balanced.data1_range.uniform_range(0, data1_max)

        # Moderate profile with some constraints
        # Ensure ranges are valid for small field widths
        if addr_max >= 4:
            addr_quarter = addr_max // 4
            addr_half = addr_max // 2
            config_gen.moderate.addr_range.weighted_ranges([
                ((0, addr_quarter), 2), ((addr_half, addr_max), 1)
            ])
        else:
            # For very small fields, just use uniform distribution
            config_gen.moderate.addr_range.uniform_range(0, addr_max)
        
        if ctrl_max >= 2:
            ctrl_half = ctrl_max // 2
            config_gen.moderate.ctrl_range.weighted_ranges([
                ((0, ctrl_half), 3), ((ctrl_half, ctrl_max), 1)
            ])
        else:
            config_gen.moderate.ctrl_range.uniform_range(0, ctrl_max)
            
        config_gen.moderate.data0_range.uniform_range(0, data0_max)
        config_gen.moderate.data1_range.uniform_range(0, data1_max)

        # Constrained profile for focused testing
        config_gen.constrained.addr_range.uniform_range(0, min(0xFF, addr_max))
        config_gen.constrained.ctrl_range.uniform_range(0, min(0xF, ctrl_max))
        config_gen.constrained.data0_range.uniform_range(0, min(0xFFFF, data0_max))
        config_gen.constrained.data1_range.uniform_range(0, min(0xFFFF, data1_max))

        # Chaotic profile for stress testing - handle small field widths gracefully
        # For addr field
        if addr_max >= 8:
            config_gen.chaotic.addr_range.probability_split([
                ((0, addr_max // 8), 0.3), ((addr_max // 2, addr_max), 0.7)
            ])
        else:
            config_gen.chaotic.addr_range.uniform_range(0, addr_max)
        
        # For ctrl field
        if ctrl_max >= 2:
            config_gen.chaotic.ctrl_range.probability_split([
                ((0, max(1, ctrl_max // 4)), 0.5), ((max(1, ctrl_max - 1), ctrl_max), 0.5)
            ])
        else:
            config_gen.chaotic.ctrl_range.uniform_range(0, ctrl_max)
        
        # For data0 field - ensure valid ranges
        if data0_max >= 0xFF:
            # Large enough for complex patterns
            low_end = min(0xFF, data0_max // 4)
            mid_start = max(low_end + 1, data0_max // 2)
            high_start = max(mid_start + 1, data0_max - data0_max // 4)
            config_gen.chaotic.data0_range.probability_split([
                ((0, low_end), 0.4), 
                ((mid_start, min(mid_start + data0_max // 4, data0_max)), 0.3), 
                ((high_start, data0_max), 0.3)
            ])
        else:
            # Small field, use simple split
            mid_point = data0_max // 2
            config_gen.chaotic.data0_range.probability_split([
                ((0, mid_point), 0.5), ((mid_point + 1 if mid_point < data0_max else mid_point, data0_max), 0.5)
            ])
        
        # For data1 field - same logic as data0
        if data1_max >= 0xFF:
            low_end = min(0xFF, data1_max // 4)
            mid_start = max(low_end + 1, data1_max // 2)
            high_start = max(mid_start + 1, data1_max - data1_max // 4)
            config_gen.chaotic.data1_range.probability_split([
                ((0, low_end), 0.4), 
                ((mid_start, min(mid_start + data1_max // 4, data1_max)), 0.3), 
                ((high_start, data1_max), 0.3)
            ])
        else:
            # Small field, use simple split
            mid_point = data1_max // 2
            config_gen.chaotic.data1_range.probability_split([
                ((0, mid_point), 0.5), ((mid_point + 1 if mid_point < data1_max else mid_point, data1_max), 0.5)
            ])

        # Customize the seq_uniform profile to be truly uniform across full ranges
        config_gen.seq_uniform.addr_range.uniform_range(0, addr_max)
        config_gen.seq_uniform.ctrl_range.uniform_range(0, ctrl_max)
        config_gen.seq_uniform.data0_range.uniform_range(0, data0_max)
        config_gen.seq_uniform.data1_range.uniform_range(0, data1_max)

        # Customize seq_weighted for interesting distribution patterns
        # Handle small field widths gracefully
        if addr_max >= 4:
            addr_q1 = addr_max // 4
            addr_q2 = addr_max // 2
            config_gen.seq_weighted.addr_range.weighted_ranges([
                ((0, addr_q1), 3), ((addr_q1, addr_q2), 2), ((addr_q2, addr_max), 1)
            ])
        else:
            config_gen.seq_weighted.addr_range.uniform_range(0, addr_max)
            
        if ctrl_max >= 4:
            ctrl_q1 = ctrl_max // 4
            ctrl_q2 = ctrl_max // 2
            config_gen.seq_weighted.ctrl_range.weighted_ranges([
                ((0, ctrl_q1), 3), ((ctrl_q1, ctrl_q2), 2), ((ctrl_q2, ctrl_max), 1)
            ])
        else:
            config_gen.seq_weighted.ctrl_range.uniform_range(0, ctrl_max)
            
        if data0_max >= 4:
            data0_q1 = data0_max // 4
            data0_q2 = data0_max // 2
            config_gen.seq_weighted.data0_range.weighted_ranges([
                ((0, data0_q1), 3), ((data0_q1, data0_q2), 2), ((data0_q2, data0_max), 1)
            ])
        else:
            config_gen.seq_weighted.data0_range.uniform_range(0, data0_max)
            
        if data1_max >= 4:
            data1_q1 = data1_max // 4
            data1_q2 = data1_max // 2
            config_gen.seq_weighted.data1_range.weighted_ranges([
                ((0, data1_q1), 3), ((data1_q1, data1_q2), 2), ((data1_q2, data1_max), 1)
            ])
        else:
            config_gen.seq_weighted.data1_range.uniform_range(0, data1_max)

        # Customize seq_boundary_focus for edge case testing
        # Ensure valid ranges for boundary testing
        if addr_max >= 10:
            addr_boundary_size = min(5, addr_max // 2)
            config_gen.seq_boundary_focus.addr_range.weighted_ranges([
                ((0, addr_boundary_size), 1), 
                ((max(0, addr_max - addr_boundary_size), addr_max), 1)
            ])
        else:
            config_gen.seq_boundary_focus.addr_range.uniform_range(0, addr_max)
            
        if ctrl_max >= 4:
            ctrl_boundary_size = min(2, ctrl_max // 2)
            config_gen.seq_boundary_focus.ctrl_range.weighted_ranges([
                ((0, ctrl_boundary_size), 1), 
                ((max(0, ctrl_max - ctrl_boundary_size), ctrl_max), 1)
            ])
        else:
            config_gen.seq_boundary_focus.ctrl_range.uniform_range(0, ctrl_max)
            
        if data0_max >= 512:
            data0_boundary_size = min(255, data0_max // 2)
            config_gen.seq_boundary_focus.data0_range.weighted_ranges([
                ((0, data0_boundary_size), 1), 
                ((max(0, data0_max - data0_boundary_size), data0_max), 1)
            ])
        else:
            config_gen.seq_boundary_focus.data0_range.uniform_range(0, data0_max)
            
        if data1_max >= 512:
            data1_boundary_size = min(255, data1_max // 2)
            config_gen.seq_boundary_focus.data1_range.weighted_ranges([
                ((0, data1_boundary_size), 1), 
                ((max(0, data1_max - data1_boundary_size), data1_max), 1)
            ])
        else:
            config_gen.seq_boundary_focus.data1_range.uniform_range(0, data1_max)

        # Customize seq_mid_range for middle values
        # Ensure valid ranges for mid-range testing
        if addr_max >= 4:
            addr_start = addr_max // 4
            addr_end = (addr_max * 3) // 4
            config_gen.seq_mid_range.addr_range.uniform_range(addr_start, addr_end)
        else:
            config_gen.seq_mid_range.addr_range.uniform_range(0, addr_max)
            
        if ctrl_max >= 4:
            ctrl_start = ctrl_max // 4
            ctrl_end = (ctrl_max * 3) // 4
            config_gen.seq_mid_range.ctrl_range.uniform_range(ctrl_start, ctrl_end)
        else:
            config_gen.seq_mid_range.ctrl_range.uniform_range(0, ctrl_max)
            
        if data0_max >= 4:
            data0_start = data0_max // 4
            data0_end = (data0_max * 3) // 4
            config_gen.seq_mid_range.data0_range.uniform_range(data0_start, data0_end)
        else:
            config_gen.seq_mid_range.data0_range.uniform_range(0, data0_max)
            
        if data1_max >= 4:
            data1_start = data1_max // 4
            data1_end = (data1_max * 3) // 4
            config_gen.seq_mid_range.data1_range.uniform_range(data1_start, data1_end)
        else:
            config_gen.seq_mid_range.data1_range.uniform_range(0, data1_max)

        # Customize seq_sparse for sparse coverage
        # Handle small field widths with simpler ranges
        if addr_max >= 10:
            addr_low = addr_max // 10
            addr_mid_start = max(addr_low + 1, addr_max // 2 - addr_max // 20)
            addr_mid_end = min(addr_max - 1, addr_max // 2 + addr_max // 20)
            addr_high_start = max(addr_mid_end + 1, addr_max - addr_max // 10)
            config_gen.seq_sparse.addr_range.weighted_ranges([
                ((0, addr_low), 1), 
                ((addr_mid_start, addr_mid_end), 1), 
                ((addr_high_start, addr_max), 1)
            ])
        else:
            config_gen.seq_sparse.addr_range.uniform_range(0, addr_max)
            
        if ctrl_max >= 6:
            ctrl_low = max(1, ctrl_max // 10)
            ctrl_mid = ctrl_max // 2
            ctrl_high_start = max(ctrl_mid + 1, ctrl_max - ctrl_low)
            config_gen.seq_sparse.ctrl_range.weighted_ranges([
                ((0, ctrl_low), 1), 
                ((ctrl_mid, min(ctrl_max, ctrl_mid + ctrl_low)), 1), 
                ((ctrl_high_start, ctrl_max), 1)
            ])
        else:
            config_gen.seq_sparse.ctrl_range.uniform_range(0, ctrl_max)
            
        if data0_max >= 20:
            data0_low = data0_max // 10
            data0_mid_start = max(data0_low + 1, data0_max // 2 - data0_max // 20)
            data0_mid_end = min(data0_max - 1, data0_max // 2 + data0_max // 20)
            data0_high_start = max(data0_mid_end + 1, data0_max - data0_low)
            config_gen.seq_sparse.data0_range.weighted_ranges([
                ((0, data0_low), 1), 
                ((data0_mid_start, data0_mid_end), 1), 
                ((data0_high_start, data0_max), 1)
            ])
        else:
            config_gen.seq_sparse.data0_range.uniform_range(0, data0_max)
            
        if data1_max >= 20:
            data1_low = data1_max // 10
            data1_mid_start = max(data1_low + 1, data1_max // 2 - data1_max // 20)
            data1_mid_end = min(data1_max - 1, data1_max // 2 + data1_max // 20)
            data1_high_start = max(data1_mid_end + 1, data1_max - data1_low)
            config_gen.seq_sparse.data1_range.weighted_ranges([
                ((0, data1_low), 1), 
                ((data1_mid_start, data1_mid_end), 1), 
                ((data1_high_start, data1_max), 1)
            ])
        else:
            config_gen.seq_sparse.data1_range.uniform_range(0, data1_max)

    def set_randomizer_profile(self, profile_name):
        """Set randomizer profile for sequence generation"""
        if profile_name in self.randomizer_instances:
            self.sequence_randomizer = self.randomizer_instances[profile_name]
            self.use_randomization = True
            print(f"Set sequence randomizer to profile '{profile_name}'")
        else:
            print(f"Profile '{profile_name}' not found, keeping current randomizer")

    def get_available_randomizer_profiles(self):
        """Get list of available randomizer profiles"""
        return list(self.randomizer_instances.keys())

    def _get_field_width(self, field_name):
        """
        Get field width using new infrastructure patterns.

        Args:
            field_name: Name of the field

        Returns:
            Width in bits
        """
        try:
            if hasattr(self.field_config, 'get_field'):
                field_info = self.field_config.get_field(field_name)
                return field_info.bits if hasattr(field_info, 'bits') else field_info.get('bits', 32)
            else:
                # Fallback for dictionary-based config
                return self.field_config.get(field_name, {}).get('bits', 32)
        except (AttributeError, KeyError):
            # Default width if field not found
            return 32

    def _get_field_mask(self, field_name):
        """Optimized field mask calculation for large fields"""
        
        # Check if we're in large field mode
        if hasattr(self, 'large_field_mode') and self.large_field_mode:
            # Use simplified masks for large fields to avoid expensive calculations
            if field_name in ['data0', 'data1']:
                return 0xFFFFFFFF  # Simple 32-bit mask
            elif field_name == 'addr':
                return 0xFFF       # Simple 12-bit mask  
            elif field_name == 'ctrl':
                return 0x3F        # Simple 6-bit mask
            else:
                return 0xFFFFFFFF  # Default mask
        
        # Normal calculation for smaller fields
        field_width = self._get_field_width(field_name)
        if field_width > 32:
            field_width = 32  # Cap at 32 bits to prevent overflow
        
        return (1 << field_width) - 1

    def add_multi_field_transaction(self, addr=0, ctrl=0, data0=0, data1=0, delay=0):
        """
        Add a transaction with values for all fields - UNCHANGED API.

        Args:
            addr: Address value
            ctrl: Control value
            data0: Data0 value
            data1: Data1 value
            delay: Delay after transaction

        Returns:
            Self for method chaining
        """
        # Apply field masks using new infrastructure
        addr &= self._get_field_mask('addr')
        ctrl &= self._get_field_mask('ctrl')
        data0 &= self._get_field_mask('data0')
        data1 &= self._get_field_mask('data1')

        field_values = {
            'addr': addr,
            'ctrl': ctrl,
            'data0': data0,
            'data1': data1
        }

        # Use parent method with enhanced tracking
        result = self.add_transaction(field_values, delay)
        self.stats['multi_field_transactions'] += 1
        return result

    def add_incrementing_pattern(self, count, start_value=0, addr_step=1, ctrl_step=1,
                                data0_step=1, data1_step=1, delay=0):
        """
        Add transactions with incrementing values for all fields - UNCHANGED API.

        Args:
            count: Number of transactions to generate
            start_value: Starting value for all fields
            addr_step: Increment step for addr field
            ctrl_step: Increment step for ctrl field
            data0_step: Increment step for data0 field
            data1_step: Increment step for data1 field
            delay: Delay between transactions

        Returns:
            Self for method chaining
        """
        # Generate incrementing pattern with proper masking
        for i in range(count):
            addr = (start_value + i * addr_step) & self._get_field_mask('addr')
            ctrl = (start_value + i * ctrl_step) & self._get_field_mask('ctrl')
            data0 = (start_value + i * data0_step) & self._get_field_mask('data0')
            data1 = (start_value + i * data1_step) & self._get_field_mask('data1')

            self.add_multi_field_transaction(
                addr=addr,
                ctrl=ctrl,
                data0=data0,
                data1=data1,
                delay=delay
            )

        self.stats['pattern_tests'] += 1
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

    def add_random_pattern(self, count, delay=0, randomizer_profile='balanced'):
        """
        Add transactions with random values using FlexConfigGen randomizer.

        Args:
            count: Number of transactions to generate
            delay: Delay between transactions
            randomizer_profile: Profile to use for randomization

        Returns:
            Self for method chaining
        """
        # Set randomizer profile if specified
        if randomizer_profile and randomizer_profile in self.randomizer_instances:
            current_randomizer = self.randomizer_instances[randomizer_profile]
        else:
            current_randomizer = self.sequence_randomizer

        # Use FlexConfigGen randomizer for enhanced random generation
        if current_randomizer and self.use_randomization:
            for _ in range(count):
                # Generate constrained random values using FlexConfigGen randomizer
                field_values = current_randomizer.next()

                # Extract and apply field masks
                addr = field_values.get('addr_range', random.randint(0, 0xFFFFFFFF)) & self._get_field_mask('addr')
                ctrl = field_values.get('ctrl_range', random.randint(0, 0xFF)) & self._get_field_mask('ctrl')
                data0 = field_values.get('data0_range', random.randint(0, 0xFFFFFFFF)) & self._get_field_mask('data0')
                data1 = field_values.get('data1_range', random.randint(0, 0xFFFFFFFF)) & self._get_field_mask('data1')

                self.add_multi_field_transaction(
                    addr=addr,
                    ctrl=ctrl,
                    data0=data0,
                    data1=data1,
                    delay=delay
                )
        else:
            # Fallback to basic random generation if no randomizer available
            print("No FlexConfigGen randomizer available, using basic random generation")
            for _ in range(count):
                addr = random.randint(0, 0xFFFFFFFF) & self._get_field_mask('addr')
                ctrl = random.randint(0, 0xFF) & self._get_field_mask('ctrl')
                data0 = random.randint(0, 0xFFFFFFFF) & self._get_field_mask('data0')
                data1 = random.randint(0, 0xFFFFFFFF) & self._get_field_mask('data1')

                self.add_multi_field_transaction(
                    addr=addr,
                    ctrl=ctrl,
                    data0=data0,
                    data1=data1,
                    delay=delay
                )

        self.stats['pattern_tests'] += 1
        return self

    def add_burst_pattern(self, count, burst_size=None, addr_base=0, ctrl_base=0,
                            data0_start=0, data1_start=0, delay=0, inter_burst_delay=0):
        """
        Add burst pattern transactions for testing buffer depth and backpressure - ADDED METHOD.

        This method generates bursts of transactions that stress the buffer's capacity
        and test backpressure handling. Each burst contains consecutive transactions
        with incrementing data values.

        Args:
            count: Total number of transactions to generate
            burst_size: Size of each burst (default: auto-calculate based on buffer characteristics)
            addr_base: Base address value for all transactions
            ctrl_base: Base control value for all transactions
            data0_start: Starting value for data0 field
            data1_start: Starting value for data1 field
            delay: Delay between transactions within a burst
            inter_burst_delay: Additional delay between bursts

        Returns:
            Self for method chaining
        """
        # Auto-calculate burst size if not provided
        if burst_size is None:
            # Use a burst size that's likely to stress the buffer
            # Default to 8 transactions per burst (good for most buffer depths)
            burst_size = min(8, max(4, count // 4))

        # Get field masks
        addr_mask = self._get_field_mask('addr')
        ctrl_mask = self._get_field_mask('ctrl')
        data0_mask = self._get_field_mask('data0')
        data1_mask = self._get_field_mask('data1')

        # Apply base value masks
        addr_base &= addr_mask
        ctrl_base &= ctrl_mask

        transactions_added = 0
        burst_count = 0

        while transactions_added < count:
            # Calculate how many transactions in this burst
            remaining = count - transactions_added
            current_burst_size = min(burst_size, remaining)

            # Generate burst transactions
            for i in range(current_burst_size):
                # Calculate data values for this transaction
                data0_value = (data0_start + transactions_added + i) & data0_mask
                data1_value = (data1_start + transactions_added + i) & data1_mask

                # Add transaction to the burst
                self.add_multi_field_transaction(
                    addr=addr_base,
                    ctrl=ctrl_base,
                    data0=data0_value,
                    data1=data1_value,
                    delay=delay
                )

            transactions_added += current_burst_size
            burst_count += 1

            # Add inter-burst delay if not the last burst
            if transactions_added < count and inter_burst_delay > 0:
                # Add a dummy transaction with extra delay to create burst separation
                # This transaction has the same addr/ctrl but unique data
                data0_value = (data0_start + transactions_added) & data0_mask
                data1_value = (data1_start + transactions_added) & data1_mask

                self.add_multi_field_transaction(
                    addr=addr_base,
                    ctrl=ctrl_base,
                    data0=data0_value,
                    data1=data1_value,
                    delay=delay + inter_burst_delay
                )
                transactions_added += 1

        self.stats['burst_tests'] += burst_count
        self.stats['pattern_tests'] += 1
        return self

    def add_boundary_values(self, delay=0):
        """
        Add transactions with boundary values for all fields - ENHANCED with new infrastructure.

        Args:
            delay: Delay between transactions

        Returns:
            Self for method chaining
        """
        # Get field masks using new infrastructure
        addr_mask = self._get_field_mask('addr')
        ctrl_mask = self._get_field_mask('ctrl')
        data0_mask = self._get_field_mask('data0')
        data1_mask = self._get_field_mask('data1')

        # Comprehensive boundary test cases
        test_cases = [
            # All zeros
            {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': 0},

            # All ones (maximum values)
            {'addr': addr_mask, 'ctrl': ctrl_mask, 'data0': data0_mask, 'data1': data1_mask},

            # LSB only
            {'addr': 1, 'ctrl': 1, 'data0': 1, 'data1': 1},

            # MSB only (if field width > 1)
            {'addr': 1 << (self.addr_width - 1) if self.addr_width > 1 else 1,
                'ctrl': 1 << (self.ctrl_width - 1) if self.ctrl_width > 1 else 1,
                'data0': 1 << (self.data0_width - 1) if self.data0_width > 1 else 1,
                'data1': 1 << (self.data1_width - 1) if self.data1_width > 1 else 1},

            # All except LSB
            {'addr': addr_mask & ~1, 'ctrl': ctrl_mask & ~1,
                'data0': data0_mask & ~1, 'data1': data1_mask & ~1},

            # All except MSB
            {'addr': addr_mask & ~(1 << (self.addr_width - 1)) if self.addr_width > 1 else 0,
                'ctrl': ctrl_mask & ~(1 << (self.ctrl_width - 1)) if self.ctrl_width > 1 else 0,
                'data0': data0_mask & ~(1 << (self.data0_width - 1)) if self.data0_width > 1 else 0,
                'data1': data1_mask & ~(1 << (self.data1_width - 1)) if self.data1_width > 1 else 0},

            # Mid-range values
            {'addr': addr_mask >> 1, 'ctrl': ctrl_mask >> 1,
                'data0': data0_mask >> 1, 'data1': data1_mask >> 1},

            # Quarter values
            {'addr': addr_mask >> 2, 'ctrl': ctrl_mask >> 2,
                'data0': data0_mask >> 2, 'data1': data1_mask >> 2},

            # Three-quarter values
            {'addr': (addr_mask * 3) >> 2, 'ctrl': (ctrl_mask * 3) >> 2,
             'data0': (data0_mask * 3) >> 2, 'data1': (data1_mask * 3) >> 2},
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

        self.stats['boundary_tests'] += len(test_cases)
        return self

    def add_overflow_test(self, delay=0):
        """
        Add transactions with values that exceed field widths to test masking - ENHANCED.

        Args:
            delay: Delay between transactions

        Returns:
            Self for method chaining
        """
        # Create overflow values for each field
        addr_mask = self._get_field_mask('addr')
        addr_overflow = addr_mask + random.randint(1, 100)

        ctrl_mask = self._get_field_mask('ctrl')
        ctrl_overflow = ctrl_mask + random.randint(1, 20)

        data0_mask = self._get_field_mask('data0')
        data0_overflow = data0_mask + random.randint(1, 1000)

        data1_mask = self._get_field_mask('data1')
        data1_overflow = data1_mask + random.randint(1, 1000)

        # Test each field individually with overflow
        overflow_tests = [
            {'addr': addr_overflow, 'ctrl': 0, 'data0': 0, 'data1': 0},
            {'addr': 0, 'ctrl': ctrl_overflow, 'data0': 0, 'data1': 0},
            {'addr': 0, 'ctrl': 0, 'data0': data0_overflow, 'data1': 0},
            {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': data1_overflow},

            # All fields with overflow
            {'addr': addr_overflow, 'ctrl': ctrl_overflow,
                'data0': data0_overflow, 'data1': data1_overflow},

            # Maximum possible values (32-bit overflow)
            {'addr': 0xFFFFFFFF, 'ctrl': 0xFFFFFFFF,
                'data0': 0xFFFFFFFF, 'data1': 0xFFFFFFFF},
        ]

        # Add overflow test transactions
        for test_case in overflow_tests:
            self.add_multi_field_transaction(
                addr=test_case['addr'],
                ctrl=test_case['ctrl'],
                data0=test_case['data0'],
                data1=test_case['data1'],
                delay=delay
            )

        self.stats['overflow_tests'] += len(overflow_tests)
        return self

    def add_max_value_pattern(self, delay=0):
        """
        Add transactions with maximum values for each field - NEW method.

        Args:
            delay: Delay between transactions

        Returns:
            Self for method chaining
        """
        # Get field masks
        addr_mask = self._get_field_mask('addr')
        ctrl_mask = self._get_field_mask('ctrl')
        data0_mask = self._get_field_mask('data0')
        data1_mask = self._get_field_mask('data1')

        # Add transaction with all maximum values
        self.add_multi_field_transaction(
            addr=addr_mask,
            ctrl=ctrl_mask,
            data0=data0_mask,
            data1=data1_mask,
            delay=delay
        )

        return self

    def add_alternating_patterns(self, count, delay=0):
        """
        Add transactions with alternating bit patterns - NEW method.

        Args:
            count: Number of transactions to generate
            delay: Delay between transactions

        Returns:
            Self for method chaining
        """
        patterns = [
            0x55555555,  # 0101...
            0xAAAAAAAA,  # 1010...
            0x33333333,  # 0011...
            0xCCCCCCCC,  # 1100...
            0x0F0F0F0F,  # 00001111...
            0xF0F0F0F0,  # 11110000...
        ]

        for i in range(count):
            pattern = patterns[i % len(patterns)]
            
            self.add_multi_field_transaction(
                addr=pattern & self._get_field_mask('addr'),
                ctrl=pattern & self._get_field_mask('ctrl'),
                data0=pattern & self._get_field_mask('data0'),
                data1=pattern & self._get_field_mask('data1'),
                delay=delay
            )

        return self

    def set_randomizer_enhanced(self, randomizer_profile='balanced'):
        """
        Set up enhanced randomizer using FlexConfigGen profile - UPDATED method.

        Args:
            randomizer_profile: Profile name to use for randomization

        Returns:
            Self for method chaining
        """
        # Set randomizer profile using FlexConfigGen
        self.set_randomizer_profile(randomizer_profile)
        return self

    def get_enhanced_stats(self):
        """
        Get enhanced statistics including multi-field specific metrics - NEW method.

        Returns:
            Dictionary of enhanced statistics
        """
        base_stats = self.stats.copy()

        # Add field configuration details
        base_stats.update({
            'field_widths': {
                'addr': self.addr_width,
                'ctrl': self.ctrl_width,
                'data0': self.data0_width,
                'data1': self.data1_width
            },
            'field_masks': {
                'addr': hex(self._get_field_mask('addr')),
                'ctrl': hex(self._get_field_mask('ctrl')),
                'data0': hex(self._get_field_mask('data0')),
                'data1': hex(self._get_field_mask('data1'))
            },
            'total_unique_patterns': self.stats['boundary_tests'] +
                                    self.stats['overflow_tests'] +
                                    self.stats['pattern_tests'],
            'burst_tests': self.stats['burst_tests'],
            'available_randomizer_profiles': len(self.randomizer_instances),
            'current_randomizer_active': self.use_randomization
        })

        return base_stats

    # Preserve all existing APIs for test runner compatibility
    def clear(self):
        """Clear sequence data - UNCHANGED API."""
        super().clear() if hasattr(super(), 'clear') else None
        if hasattr(self, 'sequence_data'):
            self.sequence_data.clear()

        # Reset enhanced statistics
        self.stats.update({
            'multi_field_transactions': 0,
            'boundary_tests': 0,
            'overflow_tests': 0,
            'pattern_tests': 0,
            'burst_tests': 0
        })

    def get_transactions(self):
        """Get all transactions - UNCHANGED API for test runners."""
        if hasattr(self, 'sequence_data'):
            return self.sequence_data.copy()
        else:
            return []
