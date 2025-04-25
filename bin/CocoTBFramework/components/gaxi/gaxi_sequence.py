"""
Enhanced GAXI Sequence Implementation with Transaction Dependency Tracking

This module provides a powerful sequence generator for GAXI transactions
with built-in masking features and enhanced dependency tracking capabilities
designed to model complex transaction relationships.
"""
import random
from collections import deque
from ..field_config import FieldConfig
from ..flex_randomizer import FlexRandomizer
from .gaxi_packet import GAXIPacket


class GAXISequence:
    """
    Generates sequences of GAXI transactions for testing with built-in masking
    and transaction dependency tracking.

    This class creates test patterns for GAXI transactions with dependency tracking,
    allowing for the creation of complex sequences where transactions depend on
    the completion of previous transactions.
    """

    def __init__(self, name="basic", field_config=None, packet_class=GAXIPacket):
        """
        Initialize the GAXI sequence.

        Args:
            name: Sequence name
            field_config: Field configuration (FieldConfig object or dictionary)
            packet_class: Class to use for packet creation
        """
        self.name = name
        self.packet_class = packet_class or GAXIPacket

        # Handle field_config as either FieldConfig object or dictionary
        if isinstance(field_config, FieldConfig):
            self.field_config = field_config.to_dict()
        else:
            # Default field configuration: just 'data' field
            self.field_config = field_config or {
                'data': {
                    'bits': 32,
                    'default': 0,
                    'format': 'hex',
                    'display_width': 8,
                    'active_bits': (31, 0),
                    'description': 'Data'
                }
            }

        # Calculate and store field masks for all fields
        self.field_masks = self._calculate_field_masks()

        # Sequence parameters
        self.field_data_seq = {} # Dictionary of field_name -> list of values
        self.delay_seq = []      # Delays between transactions

        # Transaction dependency tracking
        self.dependencies = {}   # Maps transaction index -> dependency index
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
        
        # Statistics
        self.stats = {
            'total_transactions': 0,
            'masked_values': 0,
            'field_stats': {},
            'dependencies': 0
        }

    def _calculate_field_masks(self):
        """
        Calculate masks for all fields based on their bit widths.
        
        Returns:
            Dictionary of field_name -> bit mask
        """
        masks = {}
        for field_name, field_def in self.field_config.items():
            if 'bits' in field_def:
                bits = field_def['bits']
                masks[field_name] = (1 << bits) - 1
            else:
                # Default to 32-bit mask if bits not specified
                masks[field_name] = 0xFFFFFFFF
        return masks

    def mask_field_value(self, field_name, value):
        """
        Mask a value according to the corresponding field's bit width.
        
        Args:
            field_name: Field name
            value: Value to mask
            
        Returns:
            Masked value that fits within the field's bit width
        """
        if field_name in self.field_masks:
            mask = self.field_masks[field_name]
            masked_value = value & mask
            
            # Update statistics if masking occurred
            if masked_value != value:
                self.stats['masked_values'] += 1
                if field_name not in self.stats['field_stats']:
                    self.stats['field_stats'][field_name] = 0
                self.stats['field_stats'][field_name] += 1
                
                # Warning message about masked value
                print(f"WARNING: Value 0x{value:X} for field '{field_name}' exceeds field width, masked to 0x{masked_value:X}")
            
            return masked_value
        return value  # No mask available for this field

    def add_transaction(self, field_values=None, delay=0):
        """
        Add a transaction to the sequence with automatic field value masking.
        
        Args:
            field_values: Dictionary of field values
            delay: Delay after this transaction
            
        Returns:
            Index of the added transaction for dependency tracking
        """
        # Add field values with automatic masking
        field_values = field_values or {}
        for field_name, value in field_values.items():
            # Mask the value to fit within field width
            masked_value = self.mask_field_value(field_name, value)
            
            # Add to sequence
            if field_name not in self.field_data_seq:
                self.field_data_seq[field_name] = []
            self.field_data_seq[field_name].append(masked_value)
                
        # Add delay
        self.delay_seq.append(delay)
        
        # Update statistics
        self.stats['total_transactions'] += 1
            
        # Return the index of this transaction for dependency tracking
        return self.stats['total_transactions'] - 1

    def add_transaction_with_dependency(self, field_values=None, delay=0, depends_on_index=None, dependency_type="after"):
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
            data: Data value (will be automatically masked)
            delay: Delay after transaction
            
        Returns:
            Index of the added transaction
        """
        return self.add_transaction({'data': data}, delay)

    def add_data_value_with_dependency(self, data, delay=0, depends_on_index=None, dependency_type="after"):
        """
        Add a data transaction that depends on completion of a previous transaction.
        
        Args:
            data: Data value (will be automatically masked)
            delay: Delay after transaction
            depends_on_index: Index of transaction this depends on
            dependency_type: Type of dependency ("after", "immediate", "conditional")
            
        Returns:
            Index of the added transaction
        """
        return self.add_transaction_with_dependency({'data': data}, delay, depends_on_index, dependency_type)

    def add_delay(self, clocks):
        """
        Add a delay to the sequence.

        Args:
            clocks: Number of clock cycles to delay
            
        Returns:
            Self for method chaining
        """
        # If there are existing transactions, update the delay of the last one
        if self.field_data_seq.get('data', []):
            self.delay_seq[-1] += clocks
        # Otherwise, record the delay to be applied to the next transaction
        else:
            self.delay_seq.append(clocks)
            
        return self

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

    def reset_iterators(self):
        """Reset all sequence iterators to the beginning."""
        self.field_iters = {}
        for field_name, values in self.field_data_seq.items():
            self.field_iters[field_name] = iter(values)
        self.delay_iter = iter(self.delay_seq) if self.delay_seq else iter([0])

    def next_field_value(self, field_name):
        """
        Get the next value for a specific field from the sequence.
        
        Args:
            field_name: Name of the field
            
        Returns:
            Next value for the field, or None if field not in sequence
        """
        # If field isn't in sequence, return None
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

    def next_delay(self):
        """
        Get the next delay value from the sequence.

        Returns:
            Next delay value in clock cycles
        """
        if not self.delay_seq:
            return 0

        if self.use_random_selection:
            return random.choice(self.delay_seq)

        try:
            return next(self.delay_iter)
        except (StopIteration, TypeError):
            self.delay_iter = iter(self.delay_seq)
            return next(self.delay_iter)

    def generate_packet(self):
        """
        Generate the next packet in the sequence.

        Returns:
            Next GAXI packet with masked field values
        """
        # Create packet
        packet = self.packet_class(self.field_config)
        
        # Set fields from sequence data
        for field_name in self.field_data_seq:
            value = self.next_field_value(field_name)
            if value is not None and hasattr(packet, field_name):
                setattr(packet, field_name, value)
                
        return packet

    def generate_packets(self, count=None):
        """
        Generate multiple packets.

        Args:
            count: Number of packets to generate, or None for all in sequence

        Returns:
            List of generated packets
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
            packet = self.generate_packet()
            # Add dependency information to the packet as metadata
            if i in self.dependencies:
                packet.depends_on_index = self.dependencies[i]
                packet.dependency_type = self.dependency_types.get(i, "after")
            
            self.packets.append(packet)

        return list(self.packets)

    def get_packet(self, index=0):
        """
        Get a specific packet from the generated list.

        Args:
            index: Packet index

        Returns:
            Packet at specified index
        """
        if not self.packets:
            self.generate_packets()

        if not self.packets:
            return None

        if self.use_random_selection:
            return random.choice(self.packets)

        return self.packets[index % len(self.packets)]

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
        # Calculate more statistics
        if self.stats['total_transactions'] > 0:
            self.stats['masking_percentage'] = (self.stats['masked_values'] / self.stats['total_transactions']) * 100
            if self.stats['dependencies'] > 0:
                self.stats['dependency_percentage'] = (self.stats['dependencies'] / self.stats['total_transactions']) * 100
            else:
                self.stats['dependency_percentage'] = 0
        else:
            self.stats['masking_percentage'] = 0
            self.stats['dependency_percentage'] = 0
            
        return self.stats

    def resolve_dependencies(self, completed_transactions=None):
        """
        Determine which transactions are ready to execute based on dependencies.
        
        Args:
            completed_transactions: Set of transaction indexes that have completed
            
        Returns:
            Set of transaction indexes that are ready to execute
        """
        completed_transactions = completed_transactions or set()
        ready_transactions = set()
        
        for i in range(self.stats['total_transactions']):
            # If already completed, skip
            if i in completed_transactions:
                continue
                
            # If no dependencies, it's ready
            if i not in self.dependencies:
                ready_transactions.add(i)
                continue
                
            # Check if dependency is satisfied
            depends_on = self.dependencies[i]
            if depends_on in completed_transactions:
                ready_transactions.add(i)
                
        return ready_transactions

    # ========================================================================
    # Extended Data Operation Methods
    # ========================================================================
    
    def add_data_incrementing(self, count, data_start=0, data_step=1, delay=0):
        """
        Add transactions with incrementing data values.
        
        Args:
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        indexes = []
        for i in range(count):
            data_value = data_start + (i * data_step)
            index = self.add_data_value(data_value, delay=delay)
            indexes.append(index)
            
        return self, indexes
        
    def add_data_pattern(self, patterns, delay=0):
        """
        Add transactions with various data patterns.
        
        Args:
            patterns: List of data patterns to use
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        indexes = []
        for pattern in patterns:
            index = self.add_data_value(pattern, delay=delay)
            indexes.append(index)
                
        return self, indexes
        
    def add_walking_ones(self, data_width=32, delay=0):
        """
        Add transactions with walking ones pattern.
        
        Args:
            data_width: Width of data in bits
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
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
            Self for method chaining
        """
        # Create all ones mask
        all_ones = (1 << data_width) - 1
        
        indexes = []
        for bit in range(data_width):
            pattern = all_ones & ~(1 << bit)
            index = self.add_data_value(pattern, delay=delay)
            indexes.append(index)
                
        return self, indexes
        
    def add_alternating_bits(self, data_width=32, delay=0):
        """
        Add transactions with alternating bit patterns.
        
        Args:
            data_width: Width of data in bits
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create alternating patterns
        patterns = [
            0x55555555 & ((1 << data_width) - 1),  # 0101...
            0xAAAAAAAA & ((1 << data_width) - 1),  # 1010...
            0x33333333 & ((1 << data_width) - 1),  # 0011...
            0xCCCCCCCC & ((1 << data_width) - 1),  # 1100...
            0x0F0F0F0F & ((1 << data_width) - 1),  # 00001111...
            0xF0F0F0F0 & ((1 << data_width) - 1),  # 11110000...
            0x00FF00FF & ((1 << data_width) - 1),  # 00000000 11111111...
            0xFF00FF00 & ((1 << data_width) - 1),  # 11111111 00000000...
            0x0000FFFF & ((1 << data_width) - 1),  # 16 zeros, 16 ones
            0xFFFF0000 & ((1 << data_width) - 1),  # 16 ones, 16 zeros
        ]
        
        # Add transactions for each pattern
        indexes = []
        for pattern in patterns:
            index = self.add_data_value(pattern, delay=delay)
            indexes.append(index)
                
        return self, indexes
        
    def add_burst_with_dependencies(self, count, data_start=0, data_step=1, delay=0, dependency_spacing=1):
        """
        Add a burst of transactions where each one depends on a previous one.
        
        Args:
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            delay: Delay between transactions
            dependency_spacing: How many transactions back to depend on (1=previous transaction)
            
        Returns:
            Self for method chaining and list of transaction indexes
        """
        indexes = []
        
        # Add the first transaction (no dependency)
        first_index = self.add_data_value(data_start, delay=delay)
        indexes.append(first_index)
        
        # Add remaining transactions with dependencies
        for i in range(1, count):
            data_value = data_start + (i * data_step)
            
            # Calculate dependency index
            if i < dependency_spacing:
                # First few transactions depend on the first one
                depends_on = first_index
            else:
                # Later transactions depend on earlier ones based on spacing
                depends_on = indexes[i - dependency_spacing]
                
            # Add transaction with dependency
            index = self.add_transaction_with_dependency(
                {'data': data_value}, 
                delay=delay, 
                depends_on_index=depends_on
            )
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
            Self for method chaining and list of transaction indexes
        """
        return self.add_burst_with_dependencies(
            count, 
            data_start=data_start, 
            data_step=data_step, 
            delay=delay, 
            dependency_spacing=1
        )

    # Factory methods return dependency chain information
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
            Configured GAXISequence instance with dependency chain
        """
        sequence = cls(name)
        sequence, indexes = sequence.add_dependency_chain(
            count, 
            data_start=data_start, 
            data_step=data_step, 
            delay=delay
        )
        return sequence
