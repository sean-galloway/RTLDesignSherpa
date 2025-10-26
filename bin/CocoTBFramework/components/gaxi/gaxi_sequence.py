# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXISequence
# Purpose: Updated GAXI Sequence - Leveraging Shared Infrastructure
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated GAXI Sequence - Leveraging Shared Infrastructure

This simplified version uses existing infrastructure more effectively:
- FlexRandomizer for value generation and constraints
- Built-in Packet field masking (no custom implementation needed)
- Standard dependency tracking patterns
- Better integration with GAXIComponentBase patterns
"""

import random
from collections import deque
from ..shared.field_config import FieldConfig
from ..shared.flex_randomizer import FlexRandomizer
from .gaxi_packet import GAXIPacket


class GAXISequence:
    """
    Enhanced GAXI sequence generator leveraging shared infrastructure.

    This simplified version eliminates custom field masking and uses existing
    infrastructure more effectively while preserving all existing APIs.
    """

    def __init__(self, name="basic", field_config=None, packet_class=None, log=None):
        """
        Initialize GAXI sequence with shared infrastructure.

        Args:
            name: Sequence name
            field_config: Field configuration (FieldConfig object or dictionary)
            packet_class: Packet class to use (defaults to GAXIPacket)
        """
        print(f"🔍 GAXISequence.__init__: Starting with name='{name}'")
        
        # Basic attributes (always fast)
        self.name = name
        self.packet_class = packet_class or GAXIPacket
        self.log = log
        
        # CRITICAL: Detect large field configurations and use simplified mode
        total_bits = 0
        if hasattr(field_config, 'get_total_bits'):
            total_bits = field_config.get_total_bits()
        
        print(f"🔍 GAXISequence.__init__: Field config total bits: {total_bits}")
        
        if total_bits > 50:  # Threshold for performance optimization
            print(f"⚠️  Large field config detected ({total_bits} bits) - using optimized initialization")
            
            # Direct assignment without expensive validation
            self.field_config = field_config
            
            # Simplified data structures to avoid expensive operations
            self.sequence_data = []
            self.randomizer = None
            self.use_randomization = False
            self.dependencies = {}
            self.stats = {
                'total_transactions': 0,
                'dependencies': 0,
                'randomized_transactions': 0
            }
            
            # Flag to use simplified mode in other methods
            self.large_field_mode = True
            
            print(f"🔍 GAXISequence.__init__: ✅ Optimized initialization completed")
            return
        
        # Normal initialization for smaller field configs
        print(f"🔍 GAXISequence.__init__: Using normal initialization for {total_bits} bits")
        
        # Normalize field_config using standard pattern
        if isinstance(field_config, FieldConfig):
            self.field_config = field_config
        elif isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        else:
            self.field_config = FieldConfig.create_data_only()

        # Standard initialization
        self.sequence_data = []
        self.randomizer = None
        self.use_randomization = False
        self.dependencies = {}
        self.stats = {
            'total_transactions': 0,
            'dependencies': 0,
            'randomized_transactions': 0
        }
        
        self.large_field_mode = False
        print(f"🔍 GAXISequence.__init__: ✅ Normal initialization completed")

    def set_randomizer(self, constraints_dict):
        """
        Set up randomizer for field value generation using FlexRandomizer.

        Args:
            constraints_dict: Dictionary of field constraints for FlexRandomizer

        Example:
            sequence.set_randomizer({
                'data': ([(0x0000, 0xFFFF), (0x10000, 0x1FFFF)], [0.7, 0.3]),
                'addr': ([(0, 1023)], [1.0])
            })
        """
        self.randomizer = FlexRandomizer(constraints_dict)
        self.use_randomization = True
        return self

    def add_transaction(self, field_values=None, delay=0, depends_on=None):
        """
        Add a transaction to the sequence.

        Field values will be automatically masked by Packet class - no custom masking needed.

        Args:
            field_values: Dictionary of field values (will be masked automatically by Packet)
            delay: Delay after this transaction
            depends_on: Index of transaction this depends on (None for no dependency)

        Returns:
            Index of the added transaction for dependency tracking
        """
        # Default field values
        field_values = field_values or {}

        # Store transaction data
        current_index = len(self.sequence_data)
        self.sequence_data.append((field_values, delay, depends_on))

        # Track dependencies
        if depends_on is not None:
            if depends_on >= current_index:
                raise ValueError(f"Dependency index {depends_on} must be less than current index {current_index}")
            self.dependencies[current_index] = depends_on
            self.stats['dependencies'] += 1

        # Update statistics
        self.stats['total_transactions'] += 1

        return current_index

    def add_data_transaction(self, data, delay=0, depends_on=None):
        """
        Add a simple data transaction.

        Args:
            data: Data value (will be automatically masked by Packet class)
            delay: Delay after transaction
            depends_on: Index of transaction this depends on

        Returns:
            Index of the added transaction
        """
        return self.add_transaction({'data': data}, delay, depends_on)

    def add_data_value(self, data, delay=0):
        """
        Add a transaction with a data value - backward compatibility.

        Args:
            data: Data value (will be automatically masked)
            delay: Delay after transaction

        Returns:
            Index of the added transaction
        """
        return self.add_data_transaction(data, delay)

    def add_data_value_with_dependency(self, data, delay=0, depends_on_index=None, dependency_type="after"):
        """
        Add a data transaction that depends on completion of a previous transaction - backward compatibility.

        Args:
            data: Data value (will be automatically masked)
            delay: Delay after transaction
            depends_on_index: Index of transaction this depends on
            dependency_type: Type of dependency (kept for compatibility, not used internally)

        Returns:
            Index of the added transaction
        """
        return self.add_data_transaction(data, delay, depends_on_index)

    def add_randomized_transaction(self, delay=0, depends_on=None, field_overrides=None):
        """
        Add a transaction with randomized field values using FlexRandomizer.

        Args:
            delay: Delay after transaction
            depends_on: Index of transaction this depends on
            field_overrides: Dictionary of field values to override random values

        Returns:
            Index of the added transaction
        """
        if not self.randomizer:
            raise ValueError("No randomizer set. Call set_randomizer() first.")

        # Generate random values for all constrained fields
        random_values = self.randomizer.next()

        # Apply any overrides
        if field_overrides:
            random_values.update(field_overrides)

        # Add transaction with generated values
        self.stats['randomized_transactions'] += 1
        return self.add_transaction(random_values, delay, depends_on)

    def add_burst(self, count, start_data=0, data_step=1, delay=0, dependency_chain=False):
        """
        Add a burst of transactions.

        Args:
            count: Number of transactions in burst
            start_data: Starting data value
            data_step: Step between data values
            delay: Delay between transactions
            dependency_chain: If True, each transaction depends on the previous

        Returns:
            List of transaction indexes
        """
        indexes = []

        for i in range(count):
            data = start_data + (i * data_step)
            depends_on = indexes[-1] if dependency_chain and indexes else None

            index = self.add_data_transaction(data, delay, depends_on)
            indexes.append(index)

        return indexes

    def add_data_incrementing(self, count, data_start=0, data_step=1, delay=0):
        """
        Add transactions with incrementing data values - backward compatibility.

        Args:
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions

        Returns:
            Self and list of indexes for method chaining
        """
        indexes = self.add_burst(count, data_start, data_step, delay)
        return self, indexes

    def add_pattern(self, pattern_name, data_width=32, delay=0):
        """
        Add common test patterns.

        Args:
            pattern_name: Type of pattern ('walking_ones', 'walking_zeros', 'alternating')
            data_width: Width of data field
            delay: Delay between pattern transactions

        Returns:
            List of transaction indexes
        """
        patterns = self._generate_test_pattern(pattern_name, data_width)
        indexes = []

        for pattern_value in patterns:
            index = self.add_data_transaction(pattern_value, delay)
            indexes.append(index)

        return indexes

    def add_walking_ones(self, data_width=32, delay=0):
        """Add transactions with walking ones pattern - backward compatibility."""
        return self.add_pattern('walking_ones', data_width, delay)

    def add_walking_zeros(self, data_width=32, delay=0):
        """Add transactions with walking zeros pattern - backward compatibility."""
        return self.add_pattern('walking_zeros', data_width, delay)

    def add_alternating_bits(self, data_width=32, delay=0):
        """Add transactions with alternating bit patterns - backward compatibility."""
        return self.add_pattern('alternating', data_width, delay)

    def _generate_test_pattern(self, pattern_name, data_width):
        """Generate common test patterns."""
        mask = (1 << data_width) - 1

        if pattern_name == 'walking_ones':
            return [1 << bit for bit in range(data_width)]
        elif pattern_name == 'walking_zeros':
            all_ones = mask
            return [all_ones & ~(1 << bit) for bit in range(data_width)]
        elif pattern_name == 'alternating':
            return [
                0x55555555 & mask,  # 0101...
                0xAAAAAAAA & mask,  # 1010...
                0x33333333 & mask,  # 0011...
                0xCCCCCCCC & mask,  # 1100...
                0x0F0F0F0F & mask,  # 00001111...
                0xF0F0F0F0 & mask,  # 11110000...
                0x00FF00FF & mask,  # 00000000 11111111...
                0xFF00FF00 & mask,  # 11111111 00000000...
                0x0000FFFF & mask,  # 16 zeros, 16 ones
                0xFFFF0000 & mask,  # 16 ones, 16 zeros
            ]
        else:
            raise ValueError(f"Unknown pattern: {pattern_name}")

    def add_burst_with_dependencies(self, count, data_start=0, data_step=1, delay=0, dependency_spacing=1):
        """
        Add a burst of transactions where each one depends on a previous one - backward compatibility.

        Args:
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions
            dependency_spacing: How many transactions back to depend on (1=previous transaction)

        Returns:
            Self and list of transaction indexes
        """
        indexes = []

        # Add the first transaction (no dependency)
        first_index = self.add_data_transaction(data_start, delay)
        indexes.append(first_index)

        # Add remaining transactions with dependencies
        for i in range(1, count):
            data_value = data_start + (i * data_step)

            # Calculate dependency index
            if i < dependency_spacing:
                depends_on = first_index
            else:
                depends_on = indexes[i - dependency_spacing]

            # Add transaction with dependency
            index = self.add_data_transaction(data_value, delay, depends_on)
            indexes.append(index)

        return self, indexes

    def add_dependency_chain(self, count, data_start=0, data_step=1, delay=0):
        """
        Add a chain of transactions where each depends on the previous one - backward compatibility.
        """
        return self.add_burst_with_dependencies(count, data_start, data_step, delay, 1)

    def generate_packets(self, count=None):
        """
        Generate packets from the sequence.

        Uses Packet class built-in field masking - no custom masking implementation needed.

        Args:
            count: Number of packets to generate (None for all)

        Returns:
            List of generated packets with dependency information
        """
        if count is None:
            count = len(self.sequence_data)

        packets = []

        for i in range(min(count, len(self.sequence_data))):
            field_values, delay, depends_on = self.sequence_data[i]

            # Create packet using class constructor (handles field masking automatically)
            packet = self.packet_class(self.field_config, **field_values)

            # Add sequence metadata
            packet.sequence_index = i
            packet.sequence_delay = delay
            if depends_on is not None:
                packet.depends_on_index = depends_on
                packet.dependency_type = "completion"  # Standard dependency type

            packets.append(packet)

        return packets

    def generate_packets_with_randomization(self, count):
        """
        Generate packets with randomized values using FlexRandomizer.

        Args:
            count: Number of packets to generate

        Returns:
            List of packets with randomized field values
        """
        if not self.randomizer:
            raise ValueError("No randomizer set. Call set_randomizer() first.")

        packets = []

        for i in range(count):
            # Generate random values
            random_values = self.randomizer.next()

            # Create packet using class constructor (handles field masking automatically)
            packet = self.packet_class(self.field_config, **random_values)
            packet.sequence_index = i
            packet.sequence_delay = 0  # Default delay for random packets

            packets.append(packet)
            self.stats['randomized_transactions'] += 1

        return packets

    def get_dependency_order(self):
        """
        Get the order in which transactions should be executed based on dependencies.

        Returns:
            List of transaction indexes in dependency-resolved order
        """
        if not self.dependencies:
            # No dependencies - sequential order
            return list(range(len(self.sequence_data)))

        # Simple topological sort for dependency resolution
        resolved = []
        remaining = set(range(len(self.sequence_data)))

        while remaining:
            # Find transactions with no unresolved dependencies
            ready = []
            for idx in remaining:
                if idx not in self.dependencies or self.dependencies[idx] in resolved:
                    ready.append(idx)

            if not ready:
                raise ValueError("Circular dependency detected in sequence")

            # Add ready transactions in index order
            ready.sort()
            resolved.extend(ready)
            remaining -= set(ready)

        return resolved

    def validate_dependencies(self):
        """
        Validate that all dependencies are resolvable.

        Returns:
            True if valid, raises ValueError if invalid
        """
        for idx, depends_on in self.dependencies.items():
            if depends_on >= idx:
                raise ValueError(f"Transaction {idx} cannot depend on future transaction {depends_on}")
            if depends_on >= len(self.sequence_data):
                raise ValueError(f"Transaction {idx} depends on non-existent transaction {depends_on}")

        # Check for circular dependencies using dependency order
        try:
            self.get_dependency_order()
        except ValueError as e:
            raise ValueError(f"Dependency validation failed: {e}")

        return True

    def get_dependency_graph(self):
        """
        Get a representation of the transaction dependencies - backward compatibility.

        Returns:
            Dictionary mapping transaction indexes to their dependencies
        """
        return {
            'dependencies': self.dependencies.copy(),
            'dependency_types': {idx: 'completion' for idx in self.dependencies.keys()},
            'transaction_count': self.stats['total_transactions']
        }

    def get_stats(self):
        """Get sequence generation statistics."""
        stats = self.stats.copy()

        if self.stats['total_transactions'] > 0:
            stats['dependency_percentage'] = (self.stats['dependencies'] / self.stats['total_transactions']) * 100
            if self.use_randomization:
                stats['randomization_percentage'] = (self.stats['randomized_transactions'] / self.stats['total_transactions']) * 100

        stats['sequence_length'] = len(self.sequence_data)
        stats['uses_randomization'] = self.use_randomization
        stats['has_dependencies'] = len(self.dependencies) > 0

        return stats

    def reset(self):
        """Reset sequence to empty state."""
        self.sequence_data.clear()
        self.dependencies.clear()
        self.stats = {
            'total_transactions': 0,
            'dependencies': 0,
            'randomized_transactions': 0
        }

    def __len__(self):
        """Return number of transactions in sequence."""
        return len(self.sequence_data)

    def __str__(self):
        """String representation of sequence."""
        return (f"GAXISequence '{self.name}': {len(self.sequence_data)} transactions, "
                f"{len(self.dependencies)} dependencies")

    # Factory methods for common sequence types
    @classmethod
    def create_burst_sequence(cls, name, count, start_data=0, data_step=1,
                            field_config=None, dependency_chain=False):
        """Create a burst sequence with incrementing data."""
        sequence = cls(name, field_config)
        sequence.add_burst(count, start_data, data_step, dependency_chain=dependency_chain)
        return sequence

    @classmethod
    def create_pattern_sequence(cls, name, pattern_name, data_width=32, field_config=None):
        """Create a sequence with test patterns."""
        sequence = cls(name, field_config)
        sequence.add_pattern(pattern_name, data_width)
        return sequence

    @classmethod
    def create_randomized_sequence(cls, name, constraints, count, field_config=None):
        """Create a sequence with randomized values."""
        sequence = cls(name, field_config)
        sequence.set_randomizer(constraints)

        # Add randomized transactions
        for _ in range(count):
            sequence.add_randomized_transaction()

        return sequence

    @classmethod
    def create_dependency_chain(cls, name="dependency_chain", count=5,
                                data_start=0, data_step=1, delay=0):
        """
        Create a sequence with transactions forming a dependency chain - backward compatibility.
        """
        sequence = cls(name)
        sequence.add_dependency_chain(count, data_start, data_step, delay)
        return sequence
