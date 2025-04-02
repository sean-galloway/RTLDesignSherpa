"""
FIFO Sequence Implementation for Generating Test Patterns
"""
import random
from collections import deque
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

class FIFOSequence:
    """
    Generates sequences of FIFO transactions for testing.

    This class creates test patterns of FIFO transactions that can be
    executed in a test environment. Supports FIFO-specific field structure
    with addr, ctrl, data0 and data1 fields.
    """

    def __init__(self, name="basic", field_config=None, packet_class=FIFOPacket):
        """
        Initialize the FIFO sequence.

        Args:
            name: Sequence name
            field_config: Field configuration dictionary
            packet_class: Class to use for packet creation
        """
        self.name = name
        self.packet_class = packet_class

        # Default field configuration with addr, ctrl, data0, data1 fields
        self.field_config = field_config or {
            'addr': {
                'bits': 4,
                'default': 0,
                'format': 'hex',
                'display_width': 2,
                'active_bits': (3, 0),
                'description': 'Address'
            },
            'ctrl': {
                'bits': 4,
                'default': 0,
                'format': 'hex',
                'display_width': 2,
                'active_bits': (3, 0),
                'description': 'Control'
            },
            'data0': {
                'bits': 4,
                'default': 0,
                'format': 'hex',
                'display_width': 2,
                'active_bits': (3, 0),
                'description': 'Data 0'
            },
            'data1': {
                'bits': 4,
                'default': 0,
                'format': 'hex',
                'display_width': 2,
                'active_bits': (3, 0),
                'description': 'Data 1'
            }
        }

        # Sequence parameters
        self.addr_seq = []       # Address values
        self.ctrl_seq = []       # Control values
        self.data0_seq = []      # Data0 values
        self.data1_seq = []      # Data1 values
        self.delay_seq = []      # Delays between transactions

        # Randomization options
        self.use_random_selection = False
        self.master_randomizer = None
        self.slave_randomizer = None

        # Generated packets
        self.packets = deque()

        # Iterators for sequences
        self.addr_iter = None
        self.ctrl_iter = None
        self.data0_iter = None
        self.data1_iter = None
        self.delay_iter = None

    def add_transaction(self, addr, ctrl, data0, data1):
        """
        Add a transaction with all fields to the sequence.

        Args:
            addr: Address value
            ctrl: Control value
            data0: Data0 value
            data1: Data1 value
        """
        self.addr_seq.append(addr)
        self.ctrl_seq.append(ctrl)
        self.data0_seq.append(data0)
        self.data1_seq.append(data1)
        
        return self

    def add_delay(self, clocks):
        """
        Add a delay to the sequence.

        Args:
            clocks: Number of clock cycles to delay
        """
        self.delay_seq.append(clocks)
        return self

    def set_random_selection(self, enable=True):
        """
        Enable/disable random selection from sequences.

        Args:
            enable: True to enable random selection, False to use sequential
        """
        self.use_random_selection = enable
        return self

    def set_master_randomizer(self, randomizer):
        """
        Set the randomizer to use for master timing constraints.

        Args:
            randomizer: FlexRandomizer instance
        """
        self.master_randomizer = randomizer
        return self

    def set_slave_randomizer(self, randomizer):
        """
        Set the randomizer to use for slave timing constraints.

        Args:
            randomizer: FlexRandomizer instance
        """
        self.slave_randomizer = randomizer
        return self

    def reset_iterators(self):
        """Reset all sequence iterators to the beginning."""
        self.addr_iter = iter(self.addr_seq)
        self.ctrl_iter = iter(self.ctrl_seq)
        self.data0_iter = iter(self.data0_seq)
        self.data1_iter = iter(self.data1_seq)
        self.delay_iter = iter(self.delay_seq) if self.delay_seq else iter([0])

    def next_addr(self):
        """
        Get the next address from the sequence.

        Returns:
            Next address value
        """
        if self.use_random_selection:
            return random.choice(self.addr_seq)

        try:
            return next(self.addr_iter)
        except (StopIteration, TypeError):
            self.addr_iter = iter(self.addr_seq)
            return next(self.addr_iter)

    def next_ctrl(self):
        """
        Get the next control value from the sequence.

        Returns:
            Next control value
        """
        if self.use_random_selection:
            return random.choice(self.ctrl_seq)

        try:
            return next(self.ctrl_iter)
        except (StopIteration, TypeError):
            self.ctrl_iter = iter(self.ctrl_seq)
            return next(self.ctrl_iter)

    def next_data0(self):
        """
        Get the next data0 value from the sequence.

        Returns:
            Next data0 value
        """
        if self.use_random_selection:
            return random.choice(self.data0_seq)

        try:
            return next(self.data0_iter)
        except (StopIteration, TypeError):
            self.data0_iter = iter(self.data0_seq)
            return next(self.data0_iter)

    def next_data1(self):
        """
        Get the next data1 value from the sequence.

        Returns:
            Next data1 value
        """
        if self.use_random_selection:
            return random.choice(self.data1_seq)

        try:
            return next(self.data1_iter)
        except (StopIteration, TypeError):
            self.data1_iter = iter(self.data1_seq)
            return next(self.data1_iter)

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
            Next FIFO packet
        """
        # Create packet
        packet = self.packet_class(self.field_config)
        
        # Set field values
        packet.addr = self.next_addr()
        packet.ctrl = self.next_ctrl()
        packet.data0 = self.next_data0()
        packet.data1 = self.next_data1()

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

        # Default to length of seq if count not specified
        # Use the minimum sequence length to ensure we have all fields
        if count is None:
            seq_lens = [len(self.addr_seq), len(self.ctrl_seq), 
                        len(self.data0_seq), len(self.data1_seq)]
            count = min(filter(lambda x: x > 0, seq_lens))

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

        if self.use_random_selection:
            return random.choice(self.packets)

        return self.packets[index % len(self.packets)]

    @classmethod
    def create_sequential(cls, name="sequential", num_transactions=10,
                            start_value=0, increment=1, field_config=None):
        """
        Create a sequential address and data pattern sequence.

        Args:
            name: Sequence name
            num_transactions: Number of transactions to create
            start_value: Starting value for all fields
            increment: Increment between values
            field_config: Field configuration

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, field_config)

        # Create sequential field values
        for i in range(num_transactions):
            addr_val = (start_value + i * increment) & 0xF  # Assuming 4-bit addr
            ctrl_val = (start_value + i * increment) & 0xF  # Assuming 4-bit ctrl
            data0_val = (start_value + i * increment) & 0xF  # Assuming 4-bit data
            data1_val = (start_value + i * increment + 1) & 0xF  # Slightly different for data1
            
            sequence.add_transaction(addr_val, ctrl_val, data0_val, data1_val)
            
            # Add small delay between transactions
            sequence.add_delay(1)

        # Reset iterators
        sequence.reset_iterators()

        return sequence
        
    @classmethod
    def create_alternating(cls, name="alternating", num_values=10,
                            data_values=None, field_config=None):
        """
        Create an alternating data pattern sequence.

        Args:
            name: Sequence name
            num_values: Number of transactions to generate
            data_values: List of data values to alternate (random if None)
            field_config: Field configuration

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, field_config)

        # Generate data values if not provided
        if data_values is None:
            data_values = [i % 16 for i in range(num_values)]
        
        # Create transactions with alternating values
        for i in range(num_values):
            addr = i % 16
            ctrl = (i + 4) % 16
            data0 = data_values[i % len(data_values)]
            data1 = (data_values[i % len(data_values)] + 8) % 16
            
            sequence.add_transaction(addr, ctrl, data0, data1)
            sequence.add_delay(2)

        # Reset iterators
        sequence.reset_iterators()

        return sequence

    @classmethod
    def create_burst(cls, name="burst", num_values=10,
                        data_values=None, field_config=None):
        """
        Create a burst pattern with continuous data values.

        Args:
            name: Sequence name
            num_values: Number of transactions to generate
            data_values: List of data values (random if None)
            field_config: Field configuration

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, field_config)

        # Generate data values if not provided
        if data_values is None:
            data_values = [random.randint(0, 15) for _ in range(num_values)]
            
        # Create burst transactions with minimal delay
        for i in range(num_values):
            addr = i % 16
            ctrl = (i >> 4) % 16
            data0 = data_values[i % len(data_values)]
            data1 = (data_values[i % len(data_values)] ^ 0xF) % 16  # Invert bits for data1
            
            sequence.add_transaction(addr, ctrl, data0, data1)
            sequence.add_delay(0)  # No delay for burst mode

        # Set fast randomizer defaults for burst mode
        sequence.set_master_randomizer(FlexRandomizer({
            'write_delay': ([[0, 0]], [1]),  # No delay
        }))

        sequence.set_slave_randomizer(FlexRandomizer({
            'read_delay': ([[0, 0]], [1]),  # No delay
        }))

        # Reset iterators
        sequence.reset_iterators()

        return sequence

    @classmethod
    def create_random(cls, name="random", num_transactions=20, 
                        data_range=(0, 15), field_config=None):
        """
        Create a random sequence of values.

        Args:
            name: Sequence name
            num_transactions: Total number of transactions
            data_range: Tuple of (min, max) for random values
            field_config: Field configuration

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, field_config)

        # Generate random values
        min_val, max_val = data_range
        
        for _ in range(num_transactions):
            addr = random.randint(min_val, max_val)
            ctrl = random.randint(min_val, max_val)
            data0 = random.randint(min_val, max_val)
            data1 = random.randint(min_val, max_val)
            
            sequence.add_transaction(addr, ctrl, data0, data1)
            
            # Random delay between 0-5 cycles
            sequence.add_delay(random.randint(0, 5))

        # Enable random selection
        sequence.set_random_selection(True)

        # Reset iterators
        sequence.reset_iterators()

        return sequence

    @classmethod
    def create_data_pattern(cls, name="data_pattern", field_config=None):
        """
        Create a sequence with various test data patterns.

        Args:
            name: Sequence name
            field_config: Field configuration

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, field_config)

        # Common test patterns for 4-bit values
        patterns = [
            (0, 0, 0, 0),            # All zeros
            (15, 15, 15, 15),        # All ones
            (5, 5, 5, 5),            # 0101
            (10, 10, 10, 10),        # 1010
            (3, 3, 3, 3),            # 0011
            (12, 12, 12, 12),        # 1100
            (7, 7, 7, 7),            # 0111
            (8, 8, 8, 8),            # 1000
            (9, 6, 9, 6),            # Mixed patterns
            (6, 9, 6, 9)             # Mixed patterns inverted
        ]

        # Add each pattern
        for addr, ctrl, data0, data1 in patterns:
            sequence.add_transaction(addr, ctrl, data0, data1)
            sequence.add_delay(2)

        # Reset iterators
        sequence.reset_iterators()

        return sequence
        
    @classmethod
    def create_counting(cls, name="counting", start_value=0, count=16,
                        wrap_value=None, field_config=None):
        """
        Create a simple counting sequence (useful for FIFO depth testing).

        Args:
            name: Sequence name
            start_value: Starting value
            count: Number of transactions to generate
            wrap_value: Value to wrap back to start_value (None for no wrap)
            field_config: Field configuration

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, field_config)
        
        current = start_value
        
        for i in range(count):
            # Generate counting values with different patterns for each field
            addr = current & 0xF
            ctrl = (current >> 4) & 0xF
            data0 = current & 0xF
            data1 = ((current & 0xF) ^ 0xF) & 0xF  # Inverted lower 4 bits
            
            sequence.add_transaction(addr, ctrl, data0, data1)
            
            # Increment with optional wrapping
            current += 1
            if wrap_value is not None and current >= wrap_value:
                current = start_value
                
            sequence.add_delay(1)
            
        # Reset iterators
        sequence.reset_iterators()
        
        return sequence

    @classmethod
    def create_complementary(cls, name="complementary", num_transactions=10, field_config=None):
        """
        Create a sequence where data0 and data1 are complementary (bitwise NOT).

        Args:
            name: Sequence name
            num_transactions: Number of transactions to generate
            field_config: Field configuration

        Returns:
            Configured FIFOSequence instance
        """
        sequence = cls(name, field_config)
        
        for i in range(num_transactions):
            addr = i & 0xF
            ctrl = (i >> 2) & 0xF
            data0 = (i * 3) & 0xF
            data1 = (~data0) & 0xF  # Complement of data0
            
            sequence.add_transaction(addr, ctrl, data0, data1)
            sequence.add_delay(1)
            
        # Reset iterators
        sequence.reset_iterators()
        
        return sequence
