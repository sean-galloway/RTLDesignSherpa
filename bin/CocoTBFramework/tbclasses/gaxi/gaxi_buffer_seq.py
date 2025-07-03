"""
Updated GAXI Buffer Sequence Classes - Using New Unified Infrastructure

This module provides specialized sequence generators for GAXI buffer testing
with multi-field support (addr, ctrl, data0, data1) updated to leverage
the new unified infrastructure while preserving all existing APIs.

Key improvements:
- Uses GAXIComponentBase patterns for consistency
- Leverages unified FieldConfig.validate_and_create() patterns
- Uses FlexRandomizer infrastructure more effectively
- Integrates with base MemoryModel directly
- Preserves all existing APIs for test runner compatibility
"""

import itertools
import random
from typing import Any
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class GAXIBufferSequence(GAXISequence):
    """
    Extended sequence generator for GAXI buffer tests using new unified infrastructure.

    This class expands on the base GAXISequence to add specific patterns and
    sequences suitable for testing GAXI buffer components with multiple fields
    (addr, ctrl, data0, data1).

    Updated to use new infrastructure while preserving exact APIs for test runners.
    """

    def __init__(self, name, field_config, packet_class=GAXIPacket):
        """
        Initialize the GAXI buffer sequence using new infrastructure patterns.

        Args:
            name: Sequence name
            field_config: Field configuration for multi-field packets (dict or FieldConfig)
            packet_class: Class to use for packet creation
        """
        super().__init__(name, field_config, packet_class)

        # Normalize field_config using new infrastructure patterns
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        elif field_config is None:
            # Default multi-field configuration
            default_config = {
                'addr': {'bits': 16, 'start_bit': 0},
                'ctrl': {'bits': 8, 'start_bit': 16},
                'data0': {'bits': 32, 'start_bit': 24},
                'data1': {'bits': 32, 'start_bit': 56}
            }
            self.field_config = FieldConfig.validate_and_create(default_config)
        elif isinstance(field_config, FieldConfig):
            self.field_config = field_config
        else:
            raise TypeError(f"field_config must be FieldConfig, dict, or None, got {type(field_config)}")

        # Extract field widths using new infrastructure patterns
        self.addr_width = self._get_field_width('addr')
        self.ctrl_width = self._get_field_width('ctrl')
        self.data0_width = self._get_field_width('data0')
        self.data1_width = self._get_field_width('data1')

        # Enhanced statistics tracking
        self.stats.update({
            'multi_field_transactions': 0,
            'boundary_tests': 0,
            'overflow_tests': 0,
            'pattern_tests': 0,
            'burst_tests': 0
        })

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
        """
        Get field mask using new infrastructure patterns.

        Args:
            field_name: Name of the field

        Returns:
            Field mask value
        """
        field_width = self._get_field_width(field_name)
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

    def add_random_pattern(self, count, delay=0):
        """
        Add transactions with random values for all fields - ENHANCED with new infrastructure.

        Args:
            count: Number of transactions to generate
            delay: Delay between transactions

        Returns:
            Self for method chaining
        """
        # Use FlexRandomizer for better random generation if available
        if self.randomizer and self.use_randomization:
            for _ in range(count):
                # Generate constrained random values
                field_values = self.randomizer.generate_constrained_values()

                # Apply field masks using new infrastructure
                addr = field_values.get('addr', random.randint(0, 0xFFFFFFFF)) & self._get_field_mask('addr')
                ctrl = field_values.get('ctrl', random.randint(0, 0xFF)) & self._get_field_mask('ctrl')
                data0 = field_values.get('data0', random.randint(0, 0xFFFFFFFF)) & self._get_field_mask('data0')
                data1 = field_values.get('data1', random.randint(0, 0xFFFFFFFF)) & self._get_field_mask('data1')

                self.add_multi_field_transaction(
                    addr=addr,
                    ctrl=ctrl,
                    data0=data0,
                    data1=data1,
                    delay=delay
                )
        else:
            # Fallback to basic random generation
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
        Add transactions with maximum field values - NEW method for comprehensive testing.

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

        # Test each field at maximum value individually
        max_tests = [
            {'addr': addr_mask, 'ctrl': 0, 'data0': 0, 'data1': 0},
            {'addr': 0, 'ctrl': ctrl_mask, 'data0': 0, 'data1': 0},
            {'addr': 0, 'ctrl': 0, 'data0': data0_mask, 'data1': 0},
            {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': data1_mask},
        ]

        # Test pairs of fields at maximum
        max_tests.extend([
            {'addr': addr_mask, 'ctrl': ctrl_mask, 'data0': 0, 'data1': 0},
            {'addr': addr_mask, 'ctrl': 0, 'data0': data0_mask, 'data1': 0},
            {'addr': addr_mask, 'ctrl': 0, 'data0': 0, 'data1': data1_mask},
            {'addr': 0, 'ctrl': ctrl_mask, 'data0': data0_mask, 'data1': 0},
            {'addr': 0, 'ctrl': ctrl_mask, 'data0': 0, 'data1': data1_mask},
            {'addr': 0, 'ctrl': 0, 'data0': data0_mask, 'data1': data1_mask},
        ])

        # Test groups of three fields at maximum
        max_tests.extend([
            {'addr': addr_mask, 'ctrl': ctrl_mask, 'data0': data0_mask, 'data1': 0},
            {'addr': addr_mask, 'ctrl': ctrl_mask, 'data0': 0, 'data1': data1_mask},
            {'addr': addr_mask, 'ctrl': 0, 'data0': data0_mask, 'data1': data1_mask},
            {'addr': 0, 'ctrl': ctrl_mask, 'data0': data0_mask, 'data1': data1_mask},
        ])

        # Test all fields at maximum
        max_tests.append({
            'addr': addr_mask, 'ctrl': ctrl_mask,
            'data0': data0_mask, 'data1': data1_mask
        })

        # Add max value test transactions
        for test_case in max_tests:
            self.add_multi_field_transaction(
                addr=test_case['addr'],
                ctrl=test_case['ctrl'],
                data0=test_case['data0'],
                data1=test_case['data1'],
                delay=delay
            )

        self.stats['pattern_tests'] += len(max_tests)
        return self

    def add_alternating_patterns(self, count, delay=0):
        """
        Add transactions with alternating bit patterns across fields - ENHANCED.

        Args:
            count: Number of transactions to generate
            delay: Delay between transactions

        Returns:
            Self for method chaining
        """
        # Get field masks using new infrastructure
        addr_mask = self._get_field_mask('addr')
        ctrl_mask = self._get_field_mask('ctrl')
        data0_mask = self._get_field_mask('data0')
        data1_mask = self._get_field_mask('data1')

        # Create alternating patterns
        patterns = [
            # Alternating 0101... and 1010... patterns
            {'addr': 0x55555555 & addr_mask, 'ctrl': 0x55 & ctrl_mask,
                'data0': 0x55555555 & data0_mask, 'data1': 0x55555555 & data1_mask},
            {'addr': 0xAAAAAAAA & addr_mask, 'ctrl': 0xAA & ctrl_mask,
                'data0': 0xAAAAAAAA & data0_mask, 'data1': 0xAAAAAAAA & data1_mask},

            # Alternating bytes
            {'addr': 0x0F0F0F0F & addr_mask, 'ctrl': 0x0F & ctrl_mask,
                'data0': 0x0F0F0F0F & data0_mask, 'data1': 0x0F0F0F0F & data1_mask},
            {'addr': 0xF0F0F0F0 & addr_mask, 'ctrl': 0xF0 & ctrl_mask,
                'data0': 0xF0F0F0F0 & data0_mask, 'data1': 0xF0F0F0F0 & data1_mask},

            # Alternating words
            {'addr': 0x00FF00FF & addr_mask, 'ctrl': 0x00 & ctrl_mask,
                'data0': 0x00FF00FF & data0_mask, 'data1': 0x00FF00FF & data1_mask},
            {'addr': 0xFF00FF00 & addr_mask, 'ctrl': 0xFF & ctrl_mask,
                'data0': 0xFF00FF00 & data0_mask, 'data1': 0xFF00FF00 & data1_mask},
        ]

        # Repeat patterns for the requested count
        pattern_cycle = itertools.cycle(patterns)

        for _ in range(count):
            pattern = next(pattern_cycle)
            self.add_multi_field_transaction(
                addr=pattern['addr'],
                ctrl=pattern['ctrl'],
                data0=pattern['data0'],
                data1=pattern['data1'],
                delay=delay
            )

        self.stats['pattern_tests'] += 1
        return self

    def set_randomizer_enhanced(self, constraints_dict):
        """
        Set up enhanced randomizer for multi-field generation - NEW method.

        Args:
            constraints_dict: Enhanced constraints for multi-field generation

        Returns:
            Self for method chaining
        """
        # Set base randomizer
        self.set_randomizer(constraints_dict)

        # Add multi-field specific constraints if not present
        if 'addr' not in constraints_dict:
            addr_max = self._get_field_mask('addr')
            constraints_dict['addr'] = ([(0, addr_max)], [1.0])

        if 'ctrl' not in constraints_dict:
            ctrl_max = self._get_field_mask('ctrl')
            constraints_dict['ctrl'] = ([(0, ctrl_max)], [1.0])

        if 'data0' not in constraints_dict:
            data0_max = self._get_field_mask('data0')
            constraints_dict['data0'] = ([(0, data0_max)], [1.0])

        if 'data1' not in constraints_dict:
            data1_max = self._get_field_mask('data1')
            constraints_dict['data1'] = ([(0, data1_max)], [1.0])

        # Update randomizer with enhanced constraints
        self.randomizer = FlexRandomizer(constraints_dict)
        self.use_randomization = True

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
            'burst_tests': self.stats['burst_tests']
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
