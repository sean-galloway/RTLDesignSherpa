"""
FIFO Sequence Implementation with Transaction Dependency Tracking

This module provides sequence generation for FIFO transactions with built-in
dependency tracking, leveraging existing Packet and PacketFactory infrastructure.
"""
import random
from collections import deque

from ..field_config import FieldConfig
from ..packet_factory import PacketFactory
from ..flex_randomizer import FlexRandomizer
from .fifo_packet import FIFOPacket


class FIFOSequence:
    """
    Generates sequences of FIFO transactions with dependency tracking.

    Leverages existing PacketFactory and Packet infrastructure while providing
    FIFO-specific features like dependency tracking and test pattern generation.
    """

    def __init__(self, name="basic", field_config=None, packet_class=FIFOPacket):
        """
        Initialize the FIFO sequence.

        Args:
            name: Sequence name
            field_config: Field configuration (FieldConfig object or dictionary)
            packet_class: Class to use for packet creation
        """
        self.name = name
        self.packet_class = packet_class

        # Handle field_config conversion
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        elif field_config is None:
            # Default: single data field
            self.field_config = FieldConfig.create_data_only()
        else:
            self.field_config = field_config

        # Create packet factory to leverage existing infrastructure
        self.packet_factory = PacketFactory(packet_class, self.field_config)

        # Sequence data
        self.field_data_seq = {}  # Dictionary of field_name -> list of values
        self.delay_seq = []       # Delays between transactions

        # Transaction dependency tracking (unique feature)
        self.dependencies = {}    # Maps transaction index -> dependency index
        self.dependency_types = {} # Maps transaction index -> dependency type

        # Randomization options
        self.use_random_selection = False
        self.master_randomizer = None
        self.slave_randomizer = None

        # Generated packets
        self.packets = deque()

        # Iterators for sequences
        self.field_iters = {}
        self.delay_iter = None

        # FIFO-specific parameters
        self.fifo_capacity = 8   # Default FIFO capacity for modeling
        self.fifo_depth = 0      # Current modeled FIFO depth
        self.back_pressure = 0.0  # Probability of back-pressure (0.0 to 1.0)

        # Statistics
        self.stats = {
            'total_transactions': 0,
            'dependencies': 0
        }

    def add_transaction(self, field_values=None, delay=0):
        """
        Add a transaction to the sequence.

        Args:
            field_values: Dictionary of field values
            delay: Delay after this transaction

        Returns:
            Index of the added transaction for dependency tracking
        """
        # Add field values (Packet class handles masking automatically)
        field_values = field_values or {}
        for field_name, value in field_values.items():
            if field_name not in self.field_data_seq:
                self.field_data_seq[field_name] = []
            self.field_data_seq[field_name].append(value)

        # Add delay
        self.delay_seq.append(delay)

        # Update statistics
        self.stats['total_transactions'] += 1

        # Return the index of this transaction for dependency tracking
        return self.stats['total_transactions'] - 1

    def add_transaction_with_dependency(self, field_values=None, delay=0, 
                                       depends_on_index=None, dependency_type="after"):
        """
        Add a transaction that depends on completion of a previous transaction.

        Args:
            field_values: Dictionary of field values
            delay: Delay after this transaction
            depends_on_index: Index of transaction this depends on
            dependency_type: Type of dependency ("after", "immediate", "conditional")

        Returns:
            Index of the added transaction
        """
        # Add the transaction normally
        current_index = self.add_transaction(field_values, delay)

        # Store dependency information if provided
        if depends_on_index is not None:
            if depends_on_index >= current_index:
                raise ValueError(f"Dependency index {depends_on_index} must be less than current index {current_index}")

            self.dependencies[current_index] = depends_on_index
            self.dependency_types[current_index] = dependency_type

            # Update statistics
            self.stats['dependencies'] += 1

        return current_index

    def add_data_value(self, data, delay=0):
        """
        Add a transaction with a data value.

        Args:
            data: Data value
            delay: Delay after transaction

        Returns:
            Index of the added transaction
        """
        return self.add_transaction({'data': data}, delay)

    def add_data_value_with_dependency(self, data, delay=0, depends_on_index=None, dependency_type="after"):
        """
        Add a data transaction that depends on completion of a previous transaction.

        Args:
            data: Data value
            delay: Delay after transaction
            depends_on_index: Index of transaction this depends on
            dependency_type: Type of dependency

        Returns:
            Index of the added transaction
        """
        return self.add_transaction_with_dependency({'data': data}, delay, depends_on_index, dependency_type)

    def set_random_selection(self, enable=True):
        """
        Enable/disable random selection from sequences.

        Args:
            enable: True to enable random selection, False to use sequential

        Returns:
            Self for method chaining
        """
        self.use_random_selection = enable
        return self

    def set_master_randomizer(self, randomizer):
        """
        Set the randomizer to use for master timing constraints.

        Args:
            randomizer: FlexRandomizer instance

        Returns:
            Self for method chaining
        """
        self.master_randomizer = randomizer
        return self

    def set_slave_randomizer(self, randomizer):
        """
        Set the randomizer to use for slave timing constraints.

        Args:
            randomizer: FlexRandomizer instance

        Returns:
            Self for method chaining
        """
        self.slave_randomizer = randomizer
        return self

    def set_fifo_parameters(self, capacity=8, back_pressure=0.0):
        """
        Set FIFO-specific parameters for more realistic sequence generation.

        Args:
            capacity: FIFO capacity in entries
            back_pressure: Probability of back-pressure (0.0 to 1.0)

        Returns:
            Self for method chaining
        """
        self.fifo_capacity = capacity
        self.back_pressure = max(0.0, min(1.0, back_pressure))  # Clamp to [0.0, 1.0]
        return self

    def reset_iterators(self):
        """Reset all sequence iterators to the beginning."""
        self.field_iters = {}
        for field_name, values in self.field_data_seq.items():
            self.field_iters[field_name] = iter(values)
        self.delay_iter = iter(self.delay_seq) if self.delay_seq else iter([0])
        self.fifo_depth = 0  # Reset modeled FIFO depth

    def next_field_value(self, field_name):
        """
        Get the next value for a specific field from the sequence.

        Args:
            field_name: Name of the field

        Returns:
            Next value for the field, or None if field not in sequence
        """
        if field_name not in self.field_data_seq:
            return None

        if self.use_random_selection:
            return random.choice(self.field_data_seq[field_name])

        try:
            if field_name not in self.field_iters:
                self.field_iters[field_name] = iter(self.field_data_seq[field_name])
            return next(self.field_iters[field_name])
        except (StopIteration, TypeError):
            # Reset iterator and try again
            self.field_iters[field_name] = iter(self.field_data_seq[field_name])
            return next(self.field_iters[field_name])

    def generate_packet(self, apply_fifo_metadata=True):
        """
        Generate the next packet in the sequence using PacketFactory.

        Args:
            apply_fifo_metadata: Whether to apply FIFO depth and capacity metadata

        Returns:
            Next FIFO packet with dependency information
        """
        # Collect field values for this packet
        field_values = {}
        for field_name in self.field_data_seq:
            value = self.next_field_value(field_name)
            if value is not None:
                field_values[field_name] = value

        # Use PacketFactory to create packet (handles masking automatically)
        packet = self.packet_factory.create_packet(**field_values)

        # Apply randomizers if available
        if self.master_randomizer:
            packet.set_master_randomizer(self.master_randomizer)
        if self.slave_randomizer:
            packet.set_slave_randomizer(self.slave_randomizer)

        return packet

    def generate_packets(self, count=None, apply_fifo_metadata=True):
        """
        Generate multiple packets using PacketFactory.

        Args:
            count: Number of packets to generate, or None for all in sequence
            apply_fifo_metadata: Whether to apply FIFO depth and capacity metadata

        Returns:
            List of generated packets with dependency information
        """
        # Clear previous packets
        self.packets.clear()

        # Reset iterators
        self.reset_iterators()

        # Default to length of first field's sequence if count not specified
        if count is None and self.field_data_seq:
            first_field = next(iter(self.field_data_seq))
            count = len(self.field_data_seq[first_field])
        elif count is None:
            count = 0

        # Generate packets
        for i in range(count):
            packet = self.generate_packet(apply_fifo_metadata)

            # Add dependency information to the packet
            if i in self.dependencies:
                packet.depends_on_index = self.dependencies[i]
                packet.dependency_type = self.dependency_types.get(i, "after")

            self.packets.append(packet)

        return list(self.packets)

    # High-level pattern generation methods (leveraging Packet masking)
    def add_data_incrementing(self, count, data_start=0, data_step=1, delay=0):
        """
        Add transactions with incrementing data values.

        Args:
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions

        Returns:
            Tuple of (self, list of transaction indexes)
        """
        indexes = []
        for i in range(count):
            data_value = data_start + (i * data_step)
            index = self.add_data_value(data_value, delay=delay)
            indexes.append(index)
        return self, indexes

    def add_walking_ones(self, data_width=32, delay=0):
        """
        Add transactions with walking ones pattern.

        Args:
            data_width: Width of data in bits
            delay: Delay between transactions

        Returns:
            Tuple of (self, list of transaction indexes)
        """
        indexes = []
        for bit in range(data_width):
            pattern = 1 << bit
            index = self.add_data_value(pattern, delay=delay)
            indexes.append(index)
        return self, indexes

    def add_walking_zeros(self, data_width=32, delay=0):
        """
        Add transactions with walking zeros pattern.

        Args:
            data_width: Width of data in bits
            delay: Delay between transactions

        Returns:
            Tuple of (self, list of transaction indexes)
        """
        # Create all ones mask based on field configuration
        if self.field_config.has_field('data'):
            field_width = self.field_config.get_field('data').bits
            all_ones = (1 << field_width) - 1
        else:
            all_ones = (1 << data_width) - 1

        indexes = []
        for bit in range(data_width):
            pattern = all_ones & ~(1 << bit)
            index = self.add_data_value(pattern, delay=delay)
            indexes.append(index)
        return self, indexes

    def add_random_data(self, count, delay=0):
        """
        Add transactions with random data.

        Args:
            count: Number of transactions
            delay: Delay between transactions

        Returns:
            Tuple of (self, list of transaction indexes)
        """
        indexes = []
        for _ in range(count):
            data = random.randint(0, 0xFFFFFFFF)  # Packet will mask automatically
            index = self.add_data_value(data, delay=delay)
            indexes.append(index)
        return self, indexes

    def add_dependency_chain(self, count, data_start=0, data_step=1, delay=0):
        """
        Add a chain of transactions where each depends on the previous one.

        Args:
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions

        Returns:
            Tuple of (self, list of transaction indexes)
        """
        indexes = []

        # Add the first transaction (no dependency)
        first_index = self.add_data_value(data_start, delay=delay)
        indexes.append(first_index)

        # Add remaining transactions with dependencies
        for i in range(1, count):
            data_value = data_start + (i * data_step)
            depends_on = indexes[i - 1]  # Depend on previous transaction

            index = self.add_transaction_with_dependency(
                {'data': data_value},
                delay=delay,
                depends_on_index=depends_on
            )
            indexes.append(index)

        return self, indexes

    def get_dependency_graph(self):
        """
        Get a representation of the transaction dependencies.

        Returns:
            Dictionary mapping transaction indexes to their dependencies
        """
        return {
            'dependencies': self.dependencies.copy(),
            'dependency_types': self.dependency_types.copy(),
            'transaction_count': self.stats['total_transactions']
        }

    def get_stats(self):
        """
        Get statistics about the sequence generation.

        Returns:
            Dictionary with statistics
        """
        stats = self.stats.copy()
        
        if self.stats['total_transactions'] > 0:
            if self.stats['dependencies'] > 0:
                stats['dependency_percentage'] = (self.stats['dependencies'] / self.stats['total_transactions']) * 100
            else:
                stats['dependency_percentage'] = 0

            # FIFO-specific stats
            stats['fifo_capacity'] = self.fifo_capacity
            stats['back_pressure'] = self.back_pressure
        else:
            stats['dependency_percentage'] = 0

        return stats

    # Factory methods for creating common test sequences
    @classmethod
    def create_dependency_chain(cls, name="dependency_chain", count=5,
                               data_start=0, data_step=1, delay=0):
        """
        Create a sequence with transactions forming a dependency chain.

        Args:
            name: Sequence name
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions

        Returns:
            Configured FIFOSequence instance with dependency chain
        """
        sequence = cls(name)
        sequence.add_dependency_chain(count, data_start=data_start, data_step=data_step, delay=delay)
        return sequence

    @classmethod
    def create_data_stress_test(cls, name="data_stress", data_width=32, delay=1):
        """
        Create a comprehensive data stress test sequence.

        Args:
            name: Sequence name
            data_width: Width of data in bits
            delay: Delay between pattern groups

        Returns:
            Configured FIFOSequence for stress testing data patterns
        """
        sequence = cls(name)

        # Add walking patterns
        sequence.add_walking_ones(data_width, delay=0)
        sequence.add_walking_zeros(data_width, delay=0)

        # Add corner values
        sequence.add_data_value(0x00000000, delay=0)  # All zeros
        sequence.add_data_value(0xFFFFFFFF, delay=0)  # All ones (will be masked by Packet)
        sequence.add_data_value(0x55555555, delay=0)  # Alternating
        sequence.add_data_value(0xAAAAAAAA, delay=0)  # Alternating

        # Add random values
        sequence.add_random_data(10, delay=0)

        return sequence

    @classmethod
    def create_burst_sequence(cls, name="burst", count=10, data_start=0x1000):
        """
        Create a simple burst sequence.

        Args:
            name: Sequence name
            count: Number of transactions
            data_start: Starting data value

        Returns:
            Configured FIFOSequence
        """
        sequence = cls(name)
        sequence.add_data_incrementing(count, data_start=data_start, data_step=1, delay=0)
        return sequence
