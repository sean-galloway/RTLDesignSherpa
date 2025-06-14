"""
FIFO Sequence Implementation with Transaction Dependency Tracking

This module provides sequence generation for FIFO transactions with built-in
dependency tracking, leveraging existing Packet and PacketFactory infrastructure.
Enhanced to use your existing statistics and infrastructure.
"""
import random
from collections import deque

from ..field_config import FieldConfig
from ..packet_factory import PacketFactory, TransactionHandler
from ..flex_randomizer import FlexRandomizer
from ..master_statistics import MasterStatistics
from .fifo_packet import FIFOPacket


class FIFOSequence:
    """
    Generates sequences of FIFO transactions with dependency tracking.

    Leverages existing PacketFactory and statistics infrastructure while providing
    FIFO-specific features like dependency tracking and test pattern generation.
    """

    def __init__(self, name="basic", field_config=None, packet_class=FIFOPacket, log=None):
        """
        Initialize the FIFO sequence.

        Args:
            name: Sequence name
            field_config: Field configuration (FieldConfig object or dictionary)
            packet_class: Class to use for packet creation
            log: Logger instance
        """
        self.name = name
        self.packet_class = packet_class
        self.log = log

        # Handle field_config conversion using existing infrastructure
        if isinstance(field_config, dict):
            self.field_config = FieldConfig.validate_and_create(field_config)
        elif field_config is None:
            # Default: single data field using existing factory method
            self.field_config = FieldConfig.create_data_only()
        else:
            self.field_config = field_config

        # Create packet factory to leverage existing infrastructure
        self.packet_factory = PacketFactory(packet_class, self.field_config)

        # Use existing statistics infrastructure instead of custom stats
        self.stats = MasterStatistics()

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

        # Transaction counter for dependency tracking
        self.transaction_counter = 0

        if self.log:
            self.log.info(f"FIFOSequence '{name}' initialized with {len(self.field_config)} fields")

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

        # Update transaction counter
        current_index = self.transaction_counter
        self.transaction_counter += 1

        # Use existing statistics infrastructure
        start_time = self.stats.record_transaction_start()

        if self.log:
            self.log.debug(f"Added transaction {current_index} to sequence '{self.name}': {field_values}")

        # Return the index of this transaction for dependency tracking
        return current_index

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

            if self.log:
                self.log.debug(f"Transaction {current_index} depends on {depends_on_index} (type: {dependency_type})")

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
        Generate multiple packets using PacketFactory with enhanced statistics.

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
            # Record packet generation start for statistics
            start_time = self.stats.record_transaction_start()
            
            packet = self.generate_packet(apply_fifo_metadata)

            # Add dependency information to the packet
            if i in self.dependencies:
                packet.depends_on_index = self.dependencies[i]
                packet.dependency_type = self.dependency_types.get(i, "after")

            # Complete transaction for statistics
            self.stats.record_transaction_complete(start_time, packet.get_total_bits() // 8)

            self.packets.append(packet)

        if self.log:
            self.log.info(f"Generated {len(self.packets)} packets for sequence '{self.name}'")

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
            'transaction_count': self.transaction_counter
        }

    def get_stats(self):
        """
        Get statistics about the sequence generation using existing infrastructure.

        Returns:
            Dictionary with statistics
        """
        # Get base statistics from existing infrastructure
        base_stats = self.stats.get_stats()
        
        # Add sequence-specific statistics
        sequence_stats = {
            'sequence_name': self.name,
            'total_transactions': self.transaction_counter,
            'dependencies_count': len(self.dependencies),
            'field_count': len(self.field_config),
            'fifo_capacity': self.fifo_capacity,
            'back_pressure': self.back_pressure,
            'random_selection': self.use_random_selection
        }

        if self.transaction_counter > 0:
            sequence_stats['dependency_percentage'] = (len(self.dependencies) / self.transaction_counter) * 100
        else:
            sequence_stats['dependency_percentage'] = 0

        # Merge base stats with sequence-specific stats
        return {**base_stats, **sequence_stats}

    def clear(self):
        """Clear the sequence and reset all counters."""
        self.field_data_seq.clear()
        self.delay_seq.clear()
        self.dependencies.clear()
        self.dependency_types.clear()
        self.packets.clear()
        self.field_iters.clear()
        
        # Reset statistics using existing infrastructure
        self.stats.reset()
        self.transaction_counter = 0
        
        if self.log:
            self.log.info(f"Cleared sequence '{self.name}'")

    # Factory methods for creating common test sequences
    @classmethod
    def create_dependency_chain(cls, name="dependency_chain", count=5,
                               data_start=0, data_step=1, delay=0, log=None):
        """
        Create a sequence with transactions forming a dependency chain.

        Args:
            name: Sequence name
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions
            log: Logger instance

        Returns:
            Configured FIFOSequence instance with dependency chain
        """
        sequence = cls(name, log=log)
        sequence.add_dependency_chain(count, data_start=data_start, data_step=data_step, delay=delay)
        return sequence

    @classmethod
    def create_fifo_capacity_test(cls, name="capacity_test", capacity=8, log=None):
        """
        Create a test sequence designed to test FIFO capacity limits.

        Args:
            name: Sequence name
            capacity: FIFO capacity to test
            log: Logger instance

        Returns:
            Configured FIFOSequence for capacity testing
        """
        sequence = cls(name, log=log)
        
        # Set FIFO parameters
        sequence.set_fifo_parameters(capacity=capacity)
        
        # Test 1: Fill exactly to capacity
        sequence.add_data_incrementing(capacity, data_start=0x1000, data_step=1, delay=0)
        
        # Test 2: Try to overfill (capacity + 2)
        sequence.add_data_incrementing(capacity + 2, data_start=0x2000, data_step=1, delay=0)
        
        # Test 3: Burst patterns that stress capacity
        burst_size = max(1, capacity // 2)
        for i in range(3):  # 3 bursts
            sequence.add_data_incrementing(burst_size, data_start=0x3000 + (i * 0x100), data_step=1, delay=0)
            # Add gap between bursts
            if i < 2:  # Don't add delay after last burst
                sequence.add_data_value(0x4000 + i, delay=capacity // 2)
        
        # Test 4: Single packets with capacity-aware delays
        for i in range(capacity):
            delay = 0 if i < capacity // 2 else 1  # Slow down toward the end
            sequence.add_data_value(0x5000 + i, delay=delay)
        
        if log:
            log.info(f"Created capacity test sequence '{name}' for capacity={capacity} "
                   f"with {sequence.transaction_counter} transactions")
        
        return sequence

    @classmethod
    def create_data_stress_test(cls, name="data_stress", data_width=32, delay=1, log=None):
        """
        Create a comprehensive data stress test sequence.

        Args:
            name: Sequence name
            data_width: Width of data in bits
            delay: Delay between pattern groups
            log: Logger instance

        Returns:
            Configured FIFOSequence for stress testing data patterns
        """
        sequence = cls(name, log=log)

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
    def create_burst_sequence(cls, name="burst", count=10, data_start=0x1000, log=None):
        """
        Create a simple burst sequence.

        Args:
            name: Sequence name
            count: Number of transactions
            data_start: Starting data value
            log: Logger instance

        Returns:
            Configured FIFOSequence
        """
        sequence = cls(name, log=log)
        sequence.add_data_incrementing(count, data_start=data_start, data_step=1, delay=0)
        return sequence

    @classmethod
    def create_comprehensive_test(cls, name="comprehensive", field_config=None, 
                                 packets_per_pattern=10, include_dependencies=True, log=None,
                                 capacity=None, data_width=None):
        """
        Create a comprehensive test sequence with multiple patterns.

        Args:
            name: Sequence name
            field_config: Field configuration to use
            packets_per_pattern: Number of packets per test pattern
            include_dependencies: Whether to include dependency tests
            log: Logger instance
            capacity: FIFO capacity for testing (optional)
            data_width: Data width override (optional)

        Returns:
            Configured FIFOSequence with comprehensive test patterns
        """
        sequence = cls(name, field_config=field_config, log=log)
        
        # Set FIFO capacity if provided
        if capacity is not None:
            sequence.set_fifo_parameters(capacity=capacity)
        
        # Get data width from parameter, field config, or default
        if data_width is not None:
            actual_data_width = data_width
        elif field_config and field_config.has_field('data'):
            actual_data_width = field_config.get_field('data').bits
        elif field_config and field_config.has_field('data0'):
            actual_data_width = field_config.get_field('data0').bits
        else:
            actual_data_width = 32

        # Add various test patterns
        
        # 1. Basic incremental pattern
        sequence.add_data_incrementing(packets_per_pattern, data_start=0x1000, data_step=1, delay=0)
        
        # 2. Walking ones pattern
        sequence.add_walking_ones(min(actual_data_width, packets_per_pattern), delay=0)
        
        # 3. Walking zeros pattern  
        sequence.add_walking_zeros(min(actual_data_width, packets_per_pattern), delay=0)
        
        # 4. Random data pattern
        sequence.add_random_data(packets_per_pattern, delay=0)
        
        # 5. Corner case values
        corner_values = [0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA]
        for i, value in enumerate(corner_values):
            sequence.add_data_value(value, delay=0)
        
        # 6. Dependency chain if requested
        if include_dependencies:
            sequence.add_dependency_chain(
                count=min(5, packets_per_pattern), 
                data_start=0x5000, 
                data_step=0x100, 
                delay=1
            )
        
        if log:
            log.info(f"Created comprehensive test sequence '{name}' with {sequence.transaction_counter} transactions, "
                   f"data_width={actual_data_width}, capacity={capacity}")
        
        return sequence

    @classmethod
    def create_corner_case_test(cls, name="corner_cases", field_config=None, log=None):
        """
        Create a sequence focused on corner case testing.

        Args:
            name: Sequence name
            field_config: Field configuration to use
            log: Logger instance

        Returns:
            Configured FIFOSequence with corner case patterns
        """
        sequence = cls(name, field_config=field_config, log=log)
        
        # Multi-field corner cases if field config supports it
        if field_config:
            field_names = field_config.field_names()
            
            # All zeros
            zero_values = {fname: 0 for fname in field_names}
            sequence.add_transaction(zero_values, delay=0)
            
            # All max values
            max_values = {}
            for fname in field_names:
                if field_config.has_field(fname):
                    field_def = field_config.get_field(fname)
                    max_values[fname] = (1 << field_def.bits) - 1
            sequence.add_transaction(max_values, delay=0)
            
            # Alternating patterns for each field
            for i in range(8):  # 8 different alternating patterns
                alt_values = {}
                for fname in field_names:
                    if field_config.has_field(fname):
                        field_def = field_config.get_field(fname)
                        # Create alternating pattern based on field width
                        if i % 2 == 0:
                            alt_values[fname] = 0x55555555 & ((1 << field_def.bits) - 1)
                        else:
                            alt_values[fname] = 0xAAAAAAAA & ((1 << field_def.bits) - 1)
                sequence.add_transaction(alt_values, delay=0)
        else:
            # Simple data-only corner cases
            corner_values = [
                0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
                0x12345678, 0x87654321, 0xDEADBEEF, 0xCAFEBABE
            ]
            for value in corner_values:
                sequence.add_data_value(value, delay=0)
        
        if log:
            log.info(f"Created corner case test sequence '{name}' with {sequence.transaction_counter} transactions")
        
        return sequence

    @classmethod  
    def create_performance_test(cls, name="performance", count=50, burst_size=10, 
                               data_start=0x8000, log=None):
        """
        Create a performance-focused test sequence with bursts.

        Args:
            name: Sequence name
            count: Total number of transactions
            burst_size: Size of each burst
            data_start: Starting data value
            log: Logger instance

        Returns:
            Configured FIFOSequence optimized for performance testing
        """
        sequence = cls(name, log=log)
        
        transactions_added = 0
        current_data = data_start
        
        while transactions_added < count:
            # Add a burst of back-to-back transactions
            burst_count = min(burst_size, count - transactions_added)
            
            for i in range(burst_count):
                sequence.add_data_value(current_data, delay=0)  # No delay within burst
                current_data += 1
                transactions_added += 1
            
            # Add a small gap between bursts (except for the last burst)
            if transactions_added < count:
                sequence.add_data_value(current_data, delay=2)  # 2-cycle gap between bursts
                current_data += 1
                transactions_added += 1
        
        if log:
            log.info(f"Created performance test sequence '{name}' with {transactions_added} transactions in bursts of {burst_size}")
        
        return sequence

    @classmethod
    def create_mixed_pattern_test(cls, name="mixed_patterns", field_config=None, 
                                 pattern_size=8, log=None):
        """
        Create a sequence with mixed test patterns for thorough validation.

        Args:
            name: Sequence name
            field_config: Field configuration to use
            pattern_size: Size of each pattern group
            log: Logger instance

        Returns:
            Configured FIFOSequence with mixed patterns
        """
        sequence = cls(name, field_config=field_config, log=log)
        
        data_width = 32
        if field_config and field_config.has_field('data'):
            data_width = field_config.get_field('data').bits
        elif field_config and field_config.has_field('data0'):
            data_width = field_config.get_field('data0').bits
        
        # Pattern 1: Incremental
        sequence.add_data_incrementing(pattern_size, data_start=0x0100, data_step=1, delay=0)
        
        # Pattern 2: Powers of 2
        for i in range(min(pattern_size, data_width)):
            sequence.add_data_value(1 << i, delay=0)
        
        # Pattern 3: Fibonacci-like sequence
        a, b = 1, 1
        for i in range(pattern_size):
            sequence.add_data_value(a & 0xFFFFFFFF, delay=0)  # Mask to 32-bit
            a, b = b, a + b
        
        # Pattern 4: Random with specific seed for reproducibility
        import random
        random.seed(0x12345)  # Fixed seed for reproducible "random" patterns
        for i in range(pattern_size):
            sequence.add_data_value(random.randint(0, 0xFFFFFFFF), delay=0)
        
        # Pattern 5: Alternating high/low
        for i in range(pattern_size):
            if i % 2 == 0:
                sequence.add_data_value(0x0000FFFF, delay=0)
            else:
                sequence.add_data_value(0xFFFF0000, delay=0)
        
        if log:
            log.info(f"Created mixed pattern test sequence '{name}' with {sequence.transaction_counter} transactions")
        
        return sequence
