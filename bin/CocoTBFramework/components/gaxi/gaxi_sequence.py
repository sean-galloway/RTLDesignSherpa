"""
Enhanced GAXI Sequence Implementation for Generating Test Patterns

This module provides a powerful sequence generator for GAXI transactions
with built-in masking features and enhanced capabilities designed to be
inherited and extended by future classes.
"""
import random
from collections import deque
from ..field_config import FieldConfig
from ..flex_randomizer import FlexRandomizer
from .gaxi_packet import GAXIPacket


class GAXISequence:
    """
    Generates sequences of GAXI transactions for testing with built-in masking.

    This class creates test patterns for GAXI transactions with default configuration
    focusing on 'data' field, providing automatic field value masking and extensibility.
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
        self.packet_class = packet_class

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
            'field_stats': {}
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
            Self for method chaining
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
            
        return self

    def add_data_value(self, data, delay=0):
        """
        Add a transaction with a data value.
        
        Args:
            data: Data value (will be automatically masked)
            delay: Delay after transaction
            
        Returns:
            Self for method chaining
        """
        return self.add_transaction({'data': data}, delay)

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
        for _ in range(count):
            packet = self.generate_packet()
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

    def get_stats(self):
        """
        Get statistics about the sequence generation.
        
        Returns:
            Dictionary with statistics
        """
        # Calculate more statistics
        if self.stats['total_transactions'] > 0:
            self.stats['masking_percentage'] = (self.stats['masked_values'] / self.stats['total_transactions']) * 100
        else:
            self.stats['masking_percentage'] = 0
            
        return self.stats

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
        for i in range(count):
            data_value = data_start + (i * data_step)
            self.add_data_value(data_value, delay=delay)
            
        return self
        
    def add_data_pattern(self, patterns, delay=0):
        """
        Add transactions with various data patterns.
        
        Args:
            patterns: List of data patterns to use
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        for pattern in patterns:
            self.add_data_value(pattern, delay=delay)
                
        return self
        
    def add_walking_ones(self, data_width=32, delay=0):
        """
        Add transactions with walking ones pattern.
        
        Args:
            data_width: Width of data in bits
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        for bit in range(data_width):
            pattern = 1 << bit
            self.add_data_value(pattern, delay=delay)
                
        return self
        
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
        
        for bit in range(data_width):
            pattern = all_ones & ~(1 << bit)
            self.add_data_value(pattern, delay=delay)
                
        return self
        
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
        for pattern in patterns:
            self.add_data_value(pattern, delay=delay)
                
        return self
        
    def add_random_data(self, count, data_mask=None, delay=0):
        """
        Add transactions with random data.
        
        Args:
            count: Number of transactions
            data_mask: Mask to apply to random data
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Determine data width
        if 'data' in self.field_config:
            data_width = self.field_config['data'].get('bits', 32)
        else:
            data_width = 32
            
        # Create mask if not provided
        if data_mask is None:
            data_mask = (1 << data_width) - 1
            
        # Add transactions with random data
        for _ in range(count):
            data = random.randint(0, 0xFFFFFFFF) & data_mask
            self.add_data_value(data, delay=delay)
            
        return self
        
    def add_data_corners(self, data_width=32, delay=0):
        """
        Add transactions with data values at the "corners" of the data space.
        
        Args:
            data_width: Width of data in bits
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create mask for data width
        mask = (1 << data_width) - 1
        
        # Define corner patterns
        patterns = [
            0x00000000,                      # All zeros
            mask,                           # All ones
            0x00000001,                      # Just LSB
            1 << (data_width - 1),           # Just MSB
            0x00000003,                      # Two LSBs
            mask & ~0x00000001,             # All except LSB
            mask & ~(1 << (data_width - 1)), # All except MSB
            0x55555555 & mask,               # Alternating 0101...
            0xAAAAAAAA & mask,               # Alternating 1010...
        ]
        
        # Add transactions for each pattern
        for pattern in patterns:
            self.add_data_value(pattern, delay=delay)
                
        return self

    def add_overflow_test(self, data_width=32, delay=0):
        """
        Add transactions that test values larger than the field width to verify masking.
        
        Args:
            data_width: Width of data in bits
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create mask for data width
        mask = (1 << data_width) - 1
        
        # These values will be automatically masked by add_data_value
        patterns = [
            mask + 1,                      # Just over the max
            mask + 2,                      # Just over the max + 1
            0xFFFFFFFF,                    # All ones (32-bit)
            0xFFFFFFFF << data_width,      # All ones shifted beyond the field
            random.randint(0, 0xFFFFFFFF)  # Random value that may exceed field width
        ]
        
        # Add transactions for each pattern
        for pattern in patterns:
            self.add_data_value(pattern, delay=delay)
                
        return self

    def add_fibonacci_sequence(self, count, delay=0):
        """
        Add transactions with Fibonacci sequence data values.
        
        Args:
            count: Number of transactions (Fibonacci numbers to generate)
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        a, b = 0, 1
        
        for _ in range(count):
            self.add_data_value(a, delay=delay)
            a, b = b, a + b
            
        return self

    def add_prime_sequence(self, count, delay=0):
        """
        Add transactions with prime number data values.
        
        Args:
            count: Number of prime numbers to generate
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        def is_prime(n):
            """Simple prime checker"""
            if n < 2:
                return False
            for i in range(2, int(n ** 0.5) + 1):
                if n % i == 0:
                    return False
            return True
        
        # Generate prime numbers
        primes = []
        num = 2
        while len(primes) < count:
            if is_prime(num):
                primes.append(num)
            num += 1
        
        # Add transactions with prime data values
        for prime in primes:
            self.add_data_value(prime, delay=delay)
            
        return self

    # ========================================================================
    # Enhanced Factory Methods for creating common test sequences
    # ========================================================================
    
    @classmethod
    def create_alternating(cls, name="alternating", data_values=None, count=10):
        """
        Create an alternating pattern of data values.

        Args:
            name: Sequence name
            data_values: List of data values (random if None)
            count: Number of transactions if data_values is None

        Returns:
            Configured GAXISequence instance
        """
        sequence = cls(name)

        # Generate data values if not provided
        if data_values is None:
            data_values = [random.randint(0, 0xFFFFFFFF) for _ in range(count)]

        # Create alternating pattern
        for data in data_values:
            # Add with small delay between each value
            sequence.add_data_value(data, delay=2)

        return sequence

    @classmethod
    def create_burst(cls, name="burst", count=10, pattern_type="increment"):
        """
        Create a burst pattern with no delays between transactions.

        Args:
            name: Sequence name
            count: Number of transactions
            pattern_type: Type of data pattern ("increment", "random", "alternating")

        Returns:
            Configured GAXISequence instance
        """
        sequence = cls(name)

        if pattern_type == "increment":
            # Incrementing values
            for i in range(count):
                sequence.add_data_value(i, delay=0)  # No delay for burst mode
        
        elif pattern_type == "random":
            # Random values
            for _ in range(count):
                value = random.randint(0, 0xFFFFFFFF)
                sequence.add_data_value(value, delay=0)  # No delay for burst mode
        
        elif pattern_type == "alternating":
            # Alternating 0x55/0xAA pattern
            for i in range(count):
                value = 0x55555555 if i % 2 == 0 else 0xAAAAAAAA
                sequence.add_data_value(value, delay=0)  # No delay for burst mode
        
        else:
            raise ValueError(f"Unknown pattern_type: {pattern_type}")

        # Set fast randomizer defaults
        sequence.set_master_randomizer(FlexRandomizer({
            'valid_delay': ([[0, 0]], [1]),  # No delay
        }))

        sequence.set_slave_randomizer(FlexRandomizer({
            'ready_delay': ([[0, 0]], [1]),  # No delay
        }))

        return sequence

    @classmethod
    def create_data_stress(cls, name="data_stress", data_width=32, delay=0):
        """
        Create a comprehensive data stress test sequence.
        
        Args:
            name: Sequence name
            data_width: Width of data in bits
            delay: Delay between sequences
            
        Returns:
            Configured GAXISequence for stress testing data patterns
        """
        sequence = cls(name)
        
        # Add walking ones pattern
        sequence.add_walking_ones(data_width, delay)
        
        # Add walking zeros pattern
        sequence.add_walking_zeros(data_width, delay)
        
        # Add alternating bits patterns
        sequence.add_alternating_bits(data_width, delay)
        
        # Add corner values
        sequence.add_data_corners(data_width, delay)
        
        # Add overflow values to test masking
        sequence.add_overflow_test(data_width, delay)
        
        # Add random values
        sequence.add_random_data(10, delay=delay)
        
        return sequence

    @classmethod
    def create_delay_variation(cls, name="delay_variation", data_pattern=None, count=10):
        """
        Create a sequence with varying delays to test timing behavior.
        
        Args:
            name: Sequence name
            data_pattern: Function to generate data values or None for sequential
            count: Number of transactions to generate
            
        Returns:
            Configured GAXISequence with varying delays
        """
        sequence = cls(name)
        
        # Generate data and delays
        for i in range(count):
            # Generate data
            if callable(data_pattern):
                data = data_pattern(i)
            elif data_pattern is not None:
                data = data_pattern
            else:
                data = i  # Sequential data
                
            # Generate delay pattern: 0, 1, 0, 2, 0, 3, ...
            delay = i // 2 if i % 2 == 1 else 0
            
            # Add transaction
            sequence.add_data_value(data, delay=delay)
            
        return sequence

    @classmethod
    def create_interleaved_sequences(cls, name="interleaved", count=10, primary_delay=0, secondary_delay=5):
        """
        Create interleaved sequences with primary (fast) and secondary (slow) data.
        
        Args:
            name: Sequence name
            count: Number of transactions (pairs) to generate
            primary_delay: Delay for primary transactions
            secondary_delay: Delay for secondary transactions
            
        Returns:
            Configured GAXISequence with interleaved primary/secondary data
        """
        sequence = cls(name)
        
        for i in range(count):
            # Primary pattern (fast, incrementing)
            sequence.add_data_value(i, delay=primary_delay)
            
            # Secondary pattern (slow, derived)
            secondary_value = i * 0x100 + 0xFF
            sequence.add_data_value(secondary_value, delay=secondary_delay)
            
        return sequence

    @classmethod
    def create_comprehensive_test(cls, name="comprehensive", data_width=32):
        """
        Create a comprehensive test with many different patterns.
        
        Args:
            name: Sequence name
            data_width: Width of data in bits
            
        Returns:
            Configured GAXISequence with multiple test patterns
        """
        sequence = cls(name)
        
        # Basic tests
        sequence.add_data_value(0, delay=0)  # All zeros
        sequence.add_data_value((1 << data_width) - 1, delay=0)  # All ones
        
        # Standard test patterns
        sequence.add_walking_ones(data_width, delay=1)
        sequence.add_walking_zeros(data_width, delay=1)
        sequence.add_alternating_bits(data_width, delay=1)
        
        # Corner cases
        sequence.add_data_corners(data_width, delay=2)
        
        # Overflow testing
        sequence.add_overflow_test(data_width, delay=2)
        
        # Varying data patterns
        sequence.add_data_incrementing(10, data_start=0, data_step=0x100, delay=0)
        sequence.add_fibonacci_sequence(10, delay=1)
        sequence.add_prime_sequence(10, delay=1)
        
        # Random data
        sequence.add_random_data(10, delay=3)
        
        return sequence
