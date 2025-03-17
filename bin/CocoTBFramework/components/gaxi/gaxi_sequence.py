"""
GAXI Sequence Implementation for Generating Test Patterns
"""
import random
from collections import deque
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

class GAXISequence:
    """
    Generates sequences of GAXI transactions for testing.

    Similar to APBSequence, this class creates test patterns of GAXI
    transactions that can be executed in a test environment.
    """

    def __init__(self, name="basic", field_config=None, packet_class=GAXIPacket):
        """
        Initialize the GAXI sequence.

        Args:
            name: Sequence name
            field_config: Field configuration dictionary
            packet_class: Class to use for packet creation
        """
        self.name = name
        self.packet_class = packet_class

        # Default field configuration with cmd/addr/data
        self.field_config = field_config or {
            'cmd': {
                'bits': 1,
                'default': 0,
                'format': 'bin',
                'display_width': 1,
                'active_bits': (0, 0),
                'description': 'Command (0=Read, 1=Write)'
            },
            'addr': {
                'bits': 32,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (31, 0),
                'description': 'Address'
            },
            'data': {
                'bits': 32,
                'default': 0,
                'format': 'hex',
                'display_width': 8,
                'active_bits': (31, 0),
                'description': 'Data'
            }
        }

        # Sequence parameters
        self.cmd_seq = []        # Write (1) or Read (0)
        self.addr_seq = []       # Addresses to access
        self.data_seq = []       # Data values for writes
        self.delay_seq = []      # Delays between transactions

        # Randomization options
        self.use_random_selection = False
        self.master_randomizer = None
        self.slave_randomizer = None

        # Generated packets
        self.packets = deque()

        # Iterators for sequences
        self.cmd_iter = None
        self.addr_iter = None
        self.data_iter = None
        self.delay_iter = None

    def add_write(self, addr, data):
        """
        Add a write transaction to the sequence.

        Args:
            addr: Address to write to
            data: Data to write
        """
        self.cmd_seq.append(1)   # 1 = Write
        self.addr_seq.append(addr)
        self.data_seq.append(data)

        return self

    def add_read(self, addr):
        """
        Add a read transaction to the sequence.

        Args:
            addr: Address to read from
        """
        self.cmd_seq.append(0)   # 0 = Read
        self.addr_seq.append(addr)

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
        self.cmd_iter = iter(self.cmd_seq)
        self.addr_iter = iter(self.addr_seq)
        self.data_iter = iter(self.data_seq)
        if self.delay_seq:
            self.delay_iter = iter(self.delay_seq)
        else:
            # Default to no delay if none specified
            self.delay_iter = iter([0])

    def next_cmd(self):
        """
        Get the next command (read/write) from the sequence.

        Returns:
            0 for read, 1 for write
        """
        if self.use_random_selection:
            return random.choice(self.cmd_seq)

        try:
            return next(self.cmd_iter)
        except (StopIteration, TypeError):
            self.cmd_iter = iter(self.cmd_seq)
            return next(self.cmd_iter)

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

    def next_data(self):
        """
        Get the next data value from the sequence.

        Returns:
            Next data value
        """
        if self.use_random_selection:
            return random.choice(self.data_seq)

        try:
            return next(self.data_iter)
        except (StopIteration, TypeError):
            self.data_iter = iter(self.data_seq)
            return next(self.data_iter)

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
            Next GAXI packet
        """
        # Get next values from sequence
        cmd = self.next_cmd()
        addr = self.next_addr()

        # Create packet
        packet = self.packet_class(self.field_config)
        packet.cmd = cmd
        packet.addr = addr

        # Add data for write commands
        if cmd == 1:  # Write
            packet.data = self.next_data()

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

        # Default to length of cmd_seq if count not specified
        if count is None:
            count = len(self.cmd_seq)

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
    def create_alternating(cls, name="alternating", base_addr=0, num_registers=10,
                           data_values=None, field_config=None):
        """
        Create an alternating write/read pattern sequence.

        Args:
            name: Sequence name
            base_addr: Base address for transactions
            num_registers: Number of registers to test
            data_values: List of data values (random if None)
            field_config: Field configuration

        Returns:
            Configured GAXISequence instance
        """
        sequence = cls(name, field_config)

        # Generate data values if not provided
        if data_values is None:
            data_values = [random.randint(0, 0xFFFFFFFF) for _ in range(num_registers)]

        # Create alternating write/read pattern
        for i in range(num_registers):
            addr = base_addr + (i * 4)  # Assuming 4-byte alignment
            data = data_values[i % len(data_values)]

            # Add write followed by read
            sequence.add_write(addr, data)
            sequence.add_read(addr)

            # Add small delay between each pair
            sequence.add_delay(2)

        # Reset iterators
        sequence.reset_iterators()

        return sequence

    @classmethod
    def create_burst(cls, name="burst", base_addr=0, num_registers=10,
                     data_values=None, field_config=None):
        """
        Create a burst pattern with all writes followed by all reads.

        Args:
            name: Sequence name
            base_addr: Base address for transactions
            num_registers: Number of registers to test
            data_values: List of data values (random if None)
            field_config: Field configuration

        Returns:
            Configured GAXISequence instance
        """
        sequence = cls(name, field_config)

        # Generate data values if not provided
        if data_values is None:
            data_values = [random.randint(0, 0xFFFFFFFF) for _ in range(num_registers)]

        # First all writes
        for i in range(num_registers):
            addr = base_addr + (i * 4)  # Assuming 4-byte alignment
            data = data_values[i % len(data_values)]
            sequence.add_write(addr, data)
            sequence.add_delay(0)  # No delay for burst mode

        # Then all reads
        for i in range(num_registers):
            addr = base_addr + (i * 4)
            sequence.add_read(addr)
            sequence.add_delay(0)  # No delay for burst mode

        # Set fast randomizer defaults
        sequence.set_master_randomizer(FlexRandomizer({
            'valid_delay': ([[0, 0]], [1]),  # No delay
        }))

        sequence.set_slave_randomizer(FlexRandomizer({
            'ready_delay': ([[0, 0]], [1]),  # No delay
        }))

        # Reset iterators
        sequence.reset_iterators()

        return sequence

    @classmethod
    def create_random(cls, name="random", base_addr=0, num_transactions=20,
                      addr_count=10, data_values=None, field_config=None):
        """
        Create a random mix of reads and writes.

        Args:
            name: Sequence name
            base_addr: Base address for transactions
            num_transactions: Total number of transactions
            addr_count: Number of unique addresses to use
            data_values: List of data values (random if None)
            field_config: Field configuration

        Returns:
            Configured GAXISequence instance
        """
        sequence = cls(name, field_config)

        # Generate data values if not provided
        if data_values is None:
            data_values = [random.randint(0, 0xFFFFFFFF) for _ in range(20)]

        # Generate address list
        addr_list = [base_addr + (i * 4) for i in range(addr_count)]

        # Generate random mix of reads and writes
        write_probability = 0.7  # 70% writes

        for _ in range(num_transactions):
            addr = random.choice(addr_list)

            if random.random() < write_probability:  # Write
                data = random.choice(data_values)
                sequence.add_write(addr, data)
            else:  # Read
                sequence.add_read(addr)

            # Random delay
            sequence.add_delay(random.randint(0, 5))

        # Enable random selection
        sequence.set_random_selection(True)

        # Reset iterators
        sequence.reset_iterators()

        return sequence

    @classmethod
    def create_address_sweep(cls, name="addr_sweep", base_addr=0,
                            num_addresses=16, data_pattern=None, field_config=None):
        """
        Create an address sweep pattern that writes and reads across a range.

        Args:
            name: Sequence name
            base_addr: Base address for transactions
            num_addresses: Number of addresses to sweep
            data_pattern: Function to generate data based on address, or None for address+0xA0
            field_config: Field configuration

        Returns:
            Configured GAXISequence instance
        """
        sequence = cls(name, field_config)

        # Default data pattern
        if data_pattern is None:
            data_pattern = lambda addr: addr + 0xA0000000

        # First sweep writes
        for i in range(num_addresses):
            addr = base_addr + (i * 4)
            data = data_pattern(addr)
            sequence.add_write(addr, data)
            sequence.add_delay(1)

        # Then sweep reads
        for i in range(num_addresses):
            addr = base_addr + (i * 4)
            sequence.add_read(addr)
            sequence.add_delay(1)

        # Reset iterators
        sequence.reset_iterators()

        return sequence

    @classmethod
    def create_data_pattern(cls, name="data_pattern", addr=0,
                         data_patterns=None, field_config=None):
        """
        Create a sequence that writes and reads various data patterns to a single address.

        Args:
            name: Sequence name
            addr: Address to test
            data_patterns: List of data patterns to test
            field_config: Field configuration

        Returns:
            Configured GAXISequence instance
        """
        sequence = cls(name, field_config)

        # Default test patterns if not provided
        if data_patterns is None:
            data_patterns = [
                0x00000000,  # All zeros
                0xFFFFFFFF,  # All ones
                0xAAAAAAAA,  # Alternating bits
                0x55555555,  # Alternating bits (inverted)
                0xA5A5A5A5,  # Alternating nibbles
                0x5A5A5A5A,  # Alternating nibbles (inverted)
                0x00FF00FF,  # Alternating bytes
                0xFF00FF00,  # Alternating bytes (inverted)
                0x0000FFFF,  # Half and half
                0xFFFF0000,  # Half and half (inverted)
            ]

        # Write and read each pattern
        for data in data_patterns:
            sequence.add_write(addr, data)
            sequence.add_delay(1)
            sequence.add_read(addr)
            sequence.add_delay(2)

        # Reset iterators
        sequence.reset_iterators()

        return sequence