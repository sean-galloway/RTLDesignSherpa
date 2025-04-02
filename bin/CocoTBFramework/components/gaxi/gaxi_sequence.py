"""
GAXI Sequence Implementation for Generating Test Patterns

This module provides a powerful sequence generator for GAXI transactions
with operations tailored to address and data fields, while maintaining
flexibility for custom field configurations.
"""
import random
from collections import deque
from typing import List, Dict, Any, Optional, Callable, Union, Tuple
from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.flex_randomizer import FlexRandomizer


class GAXISequence:
    """
    Generates sequences of GAXI transactions for testing.

    This class creates test patterns of GAXI transactions with support
    for various field configurations, while providing common operations
    for address and data fields.
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
            # Default field configuration if none provided
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

        # Determine field types available in the configuration
        self.field_info = self._analyze_field_config()

        # Sequence parameters
        self.cmd_seq = []        # Write (1) or Read (0)
        self.field_data_seq = {} # Dictionary of field_name -> list of values
        self.delay_seq = []      # Delays between transactions

        # Randomization options
        self.use_random_selection = False
        self.master_randomizer = None
        self.slave_randomizer = None

        # Generated packets
        self.packets = deque()

        # Iterators for sequences
        self.cmd_iter = None
        self.field_iters = {}
        self.delay_iter = None

    def _analyze_field_config(self):
        """
        Analyze field configuration to identify address, data, and other fields.
        
        Returns:
            Dictionary with field type information
        """
        info = {
            'has_cmd': False,
            'has_addr': False,
            'has_data': False,
            'cmd_field': None,
            'addr_field': None,
            'data_fields': [],
            'ctrl_fields': [],
            'other_fields': [],
            'all_fields': list(self.field_config.keys())
        }
        
        # Identify command field (typically 'cmd')
        cmd_candidates = ['cmd', 'command', 'op', 'opcode']
        for field in cmd_candidates:
            if field in self.field_config:
                info['has_cmd'] = True
                info['cmd_field'] = field
                break
                
        # Identify address field (typically 'addr')
        addr_candidates = ['addr', 'address', 'adr']
        for field in addr_candidates:
            if field in self.field_config:
                info['has_addr'] = True
                info['addr_field'] = field
                break
                
        # Identify data fields (could be 'data', 'data0', 'data1', etc.)
        data_pattern = 'data'
        for field in self.field_config:
            if field == data_pattern or field.startswith(data_pattern):
                info['has_data'] = True
                info['data_fields'].append(field)
                
        # Identify control fields
        ctrl_pattern = 'ctrl'
        for field in self.field_config:
            if field == ctrl_pattern or field.startswith(ctrl_pattern):
                info['ctrl_fields'].append(field)
                
        # Any other fields
        for field in self.field_config:
            if (field != info['cmd_field'] and 
                field != info['addr_field'] and
                field not in info['data_fields'] and
                field not in info['ctrl_fields']):
                info['other_fields'].append(field)
                
        return info

    def add_transaction(self, cmd=1, field_values=None, delay=0):
        """
        Add a transaction to the sequence.
        
        Args:
            cmd: Command value (typically 1=write, 0=read)
            field_values: Dictionary of field values
            delay: Delay after this transaction
            
        Returns:
            Self for method chaining
        """
        # Add command
        self.cmd_seq.append(cmd)
        
        # Add field values
        field_values = field_values or {}
        for field_name, value in field_values.items():
            if field_name not in self.field_data_seq:
                self.field_data_seq[field_name] = []
            self.field_data_seq[field_name].append(value)
                
        # Add delay
        self.delay_seq.append(delay)
            
        return self

    def add_write(self, addr, data=None, extra_fields=None, delay=0):
        """
        Add a write transaction to the sequence.
        
        This method supports both single-data and multi-data configurations.
        For multi-data, the data parameter can be a dictionary of data field values.

        Args:
            addr: Address value
            data: Data value (can be a single value or dictionary for multi-data)
            extra_fields: Additional field values
            delay: Delay after transaction
            
        Returns:
            Self for method chaining
        """
        # Prepare field values dictionary
        field_values = extra_fields or {}
        
        # Add address if this configuration has an address field
        if self.field_info['addr_field']:
            field_values[self.field_info['addr_field']] = addr
            
        # Add data based on configuration and parameter type
        if isinstance(data, dict):
            # Multi-data configuration with dictionary parameter
            for field_name, value in data.items():
                field_values[field_name] = value
        elif data is not None and self.field_info['data_fields']:
            # Single data value - assign to first data field
            field_values[self.field_info['data_fields'][0]] = data
            
        # Add transaction
        return self.add_transaction(1, field_values, delay)

    def add_read(self, addr, extra_fields=None, delay=0):
        """
        Add a read transaction to the sequence.
        
        Args:
            addr: Address value
            extra_fields: Additional field values
            delay: Delay after transaction
            
        Returns:
            Self for method chaining
        """
        # Prepare field values dictionary
        field_values = extra_fields or {}
        
        # Add address if this configuration has an address field
        if self.field_info['addr_field']:
            field_values[self.field_info['addr_field']] = addr
            
        # Add transaction
        return self.add_transaction(0, field_values, delay)

    def add_delay(self, clocks):
        """
        Add a delay to the sequence.

        Args:
            clocks: Number of clock cycles to delay
            
        Returns:
            Self for method chaining
        """
        # If there are existing transactions, update the delay of the last one
        if self.cmd_seq:
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
        self.cmd_iter = iter(self.cmd_seq)
        self.field_iters = {}
        for field_name, values in self.field_data_seq.items():
            self.field_iters[field_name] = iter(values)
        self.delay_iter = iter(self.delay_seq) if self.delay_seq else iter([0])

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
            Next GAXI packet
        """
        # Create packet
        packet = self.packet_class(self.field_config)
        
        # Get next command
        cmd = self.next_cmd()
        
        # Set cmd field if packet has one
        if self.field_info['cmd_field'] and hasattr(packet, self.field_info['cmd_field']):
            setattr(packet, self.field_info['cmd_field'], cmd)
        
        # Set other fields from sequence data
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

    # ========================================================================
    # Address Operation Methods
    # ========================================================================
    
    def add_addr_incrementing(self, start_addr, count, addr_step=4, 
                            cmd=1, data_pattern=None, delay=0):
        """
        Add transactions with incrementing addresses.
        
        Args:
            start_addr: Starting address
            count: Number of transactions
            addr_step: Step size between addresses
            cmd: Command (1=write, 0=read)
            data_pattern: Function to generate data based on address index (for writes)
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Use index × constant as default data pattern if none provided
        if data_pattern is None and cmd == 1:
            data_pattern = lambda idx: idx * 0x10001
            
        for i in range(count):
            addr = start_addr + (i * addr_step)
            
            if cmd == 1:  # Write
                data = data_pattern(i) if callable(data_pattern) else data_pattern
                self.add_write(addr, data, delay=delay)
            else:  # Read
                self.add_read(addr, delay=delay)
                
        return self
        
    def add_addr_random(self, addr_range, count, cmd=1, 
                        data_pattern=None, avoid_duplicates=False, delay=0):
        """
        Add transactions with random addresses.
        
        Args:
            addr_range: Tuple of (min_addr, max_addr)
            count: Number of transactions
            cmd: Command (1=write, 0=read)
            data_pattern: Function to generate data based on address (for writes)
            avoid_duplicates: If True, ensure addresses are unique
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        min_addr, max_addr = addr_range
        addr_step = 4  # Assume 4-byte alignment

        # Adjust range for alignment
        min_addr = (min_addr + addr_step - 1) & ~(addr_step - 1)
        max_addr = max_addr & ~(addr_step - 1)

        # Generate addresses
        if avoid_duplicates:
            # Calculate max possible addresses in range
            max_addrs = (max_addr - min_addr) // addr_step + 1
            count = min(count, max_addrs)

            # Generate unique random addresses
            addresses = random.sample(
                range(min_addr, max_addr + 1, addr_step), count
            )
        else:
            # Generate potentially duplicate addresses
            addresses = [
                random.randrange(min_addr, max_addr + 1, addr_step)
                for _ in range(count)
            ]

        # Add transactions
        for addr in addresses:
            if cmd == 1:  # Write
                if callable(data_pattern):
                    data = data_pattern(addr)
                elif data_pattern is not None:
                    data = data_pattern
                else:
                    data = addr ^ 0xA5A5A5A5  # Default XOR pattern

                self.add_write(addr, data, delay=delay)
            else:  # Read
                self.add_read(addr, delay=delay)

        return self
        
    def add_addr_boundary(self, boundary_size, count_per_region=3, cmd=1, 
                        data_pattern=None, delay=0):
        """
        Add transactions at bottom/middle/top of address boundaries.
        
        Args:
            boundary_size: Size of each address boundary
            count_per_region: Number of transactions per boundary region
            cmd: Command (1=write, 0=read)
            data_pattern: Function to generate data based on address (for writes)
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        addr_step = 4  # Assume 4-byte alignment
        
        # Define regions within boundary
        regions = [
            (0, boundary_size // 10),                    # Bottom of boundary
            (boundary_size // 2 - boundary_size // 10,   # Middle of boundary
                boundary_size // 2 + boundary_size // 10),
            (boundary_size - boundary_size // 10 - addr_step,  # Top of boundary
                boundary_size - addr_step)
        ]
        
        # Add transactions for each region
        for region_start, region_end in regions:
            for i in range(count_per_region):
                # Calculate address within this region
                if count_per_region > 1:
                    region_size = region_end - region_start
                    step = region_size // (count_per_region - 1) if count_per_region > 1 else region_size
                    addr = region_start + i * step
                else:
                    addr = (region_start + region_end) // 2
                    
                # Align address
                addr = addr & ~(addr_step - 1)
                
                if cmd == 1:  # Write
                    if callable(data_pattern):
                        data = data_pattern(addr)
                    elif data_pattern is not None:
                        data = data_pattern
                    else:
                        data = addr ^ 0xA5A5A5A5  # Default XOR pattern
                        
                    self.add_write(addr, data, delay=delay)
                else:  # Read
                    self.add_read(addr, delay=delay)
                    
        return self
        
    def add_addr_sweep(self, start_addr, num_addresses, addr_step=4, cmd=1, 
                        data_pattern=None, delay=0):
        """
        Add an address sweep across a range.
        
        Args:
            start_addr: Starting address
            num_addresses: Number of addresses to sweep
            addr_step: Step size between addresses
            cmd: Command (1=write, 0=read)
            data_pattern: Function to generate data based on address (for writes)
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Add transactions for address sweep
        for i in range(num_addresses):
            addr = start_addr + (i * addr_step)
            
            if cmd == 1:  # Write
                if callable(data_pattern):
                    data = data_pattern(addr)
                elif data_pattern is not None:
                    data = data_pattern
                else:
                    data = addr + 0xA0000000  # Default offset pattern
                    
                self.add_write(addr, data, delay=delay)
            else:  # Read
                self.add_read(addr, delay=delay)
                
        return self

    # ========================================================================
    # Data Operation Methods
    # ========================================================================
    
    def add_data_incrementing(self, addr, count, data_start=0, 
                            data_step=1, data_field=None, delay=0):
        """
        Add write transactions with incrementing data values.
        
        Args:
            addr: Address to write to
            count: Number of transactions
            data_start: Starting data value
            data_step: Step size between data values
            data_field: Specific data field for multi-data configurations
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        for i in range(count):
            data_value = data_start + (i * data_step)
            
            # Handle multi-data configurations
            if data_field and data_field in self.field_info['data_fields']:
                data = {data_field: data_value}
            else:
                data = data_value
                
            self.add_write(addr, data, delay=delay)
            
        return self
        
    def add_data_pattern(self, addr, patterns, read_back=True, delay=0):
        """
        Add transactions with various data patterns.
        
        Args:
            addr: Address to write to
            patterns: List of data patterns to write
            read_back: If True, add a read after each write
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        for pattern in patterns:
            # Write pattern
            self.add_write(addr, pattern, delay=delay)
            
            # Optionally read back
            if read_back:
                self.add_read(addr, delay=delay)
                
        return self
        
    def add_walking_ones(self, addr, data_width=32, read_back=True, delay=0):
        """
        Add transactions with walking ones pattern.
        
        Args:
            addr: Address to write to
            data_width: Width of data in bits
            read_back: If True, add a read after each write
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        for bit in range(data_width):
            pattern = 1 << bit
            
            # Write pattern
            self.add_write(addr, pattern, delay=delay)
            
            # Optionally read back
            if read_back:
                self.add_read(addr, delay=delay)
                
        return self
        
    def add_walking_zeros(self, addr, data_width=32, read_back=True, delay=0):
        """
        Add transactions with walking zeros pattern.
        
        Args:
            addr: Address to write to
            data_width: Width of data in bits
            read_back: If True, add a read after each write
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Create all ones mask
        all_ones = (1 << data_width) - 1
        
        for bit in range(data_width):
            pattern = all_ones & ~(1 << bit)
            
            # Write pattern
            self.add_write(addr, pattern, delay=delay)
            
            # Optionally read back
            if read_back:
                self.add_read(addr, delay=delay)
                
        return self
        
    def add_alternating_bits(self, addr, data_width=32, read_back=True, delay=0):
        """
        Add transactions with alternating bit patterns.
        
        Args:
            addr: Address to write to
            data_width: Width of data in bits
            read_back: If True, add a read after each write
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
            # Write pattern
            self.add_write(addr, pattern, delay=delay)
            
            # Optionally read back
            if read_back:
                self.add_read(addr, delay=delay)
                
        return self
        
    def add_random_data(self, addr, count, data_mask=None, delay=0):
        """
        Add write transactions with random data.
        
        Args:
            addr: Address to write to
            count: Number of transactions
            data_mask: Mask to apply to random data
            delay: Delay between transactions
            
        Returns:
            Self for method chaining
        """
        # Determine data width
        if self.field_info['data_fields']:
            data_field = self.field_info['data_fields'][0]
            if data_field in self.field_config:
                data_width = self.field_config[data_field].get('bits', 32)
            else:
                data_width = 32
        else:
            data_width = 32
            
        # Create mask if not provided
        if data_mask is None:
            data_mask = (1 << data_width) - 1
            
        # Add transactions with random data
        for _ in range(count):
            data = random.randint(0, 0xFFFFFFFF) & data_mask
            self.add_write(addr, data, delay=delay)
            
        return self
        
    def add_data_corners(self, addr, data_width=32, read_back=True, delay=0):
        """
        Add transactions with data values at the "corners" of the data space.
        
        Args:
            addr: Address to write to
            data_width: Width of data in bits
            read_back: If True, add a read after each write
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
            # Write pattern
            self.add_write(addr, pattern, delay=delay)
            
            # Optionally read back
            if read_back:
                self.add_read(addr, delay=delay)
                
        return self

    # ========================================================================
    # Factory Methods to Create Common Sequence Types
    # ========================================================================
    
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
            sequence.add_write(addr, data, delay=0)  # No delay for burst mode

        # Then all reads
        for i in range(num_registers):
            addr = base_addr + (i * 4)
            sequence.add_read(addr, delay=0)  # No delay for burst mode

        # Set fast randomizer defaults
        sequence.set_master_randomizer(FlexRandomizer({
            'valid_delay': ([[0, 0]], [1]),  # No delay
        }))

        sequence.set_slave_randomizer(FlexRandomizer({
            'ready_delay': ([[0, 0]], [1]),  # No delay
        }))

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
            data = data_pattern(addr) if callable(data_pattern) else data_pattern
            sequence.add_write(addr, data, delay=1)

        # Then sweep reads
        for i in range(num_addresses):
            addr = base_addr + (i * 4)
            sequence.add_read(addr, delay=1)

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
            sequence.add_write(addr, data, delay=1)
            sequence.add_read(addr, delay=2)

        return sequence
    
    @classmethod
    def create_multi_data_sequence(cls, name="multi_data", addr_width=4, ctrl_width=4, 
                                    data_width=8, num_data=2, pattern_type="incremental", 
                                    num_transactions=10, field_config=None):
        """
        Create a sequence specifically for multi-data buffers (with data0, data1, etc).
        
        Args:
            name: Sequence name
            addr_width: Width of address field in bits
            ctrl_width: Width of control field in bits
            data_width: Width of each data field in bits
            num_data: Number of data fields (data0, data1, etc.)
            pattern_type: Type of pattern to generate ("incremental", "alternating", "random")
            num_transactions: Number of transactions to generate
            field_config: Field configuration
            
        Returns:
            Configured GAXISequence for multi-data testing
        """
        # Create field config if not provided
        if field_config is None:
            field_config = {}
            
            # Add address field
            field_config['addr'] = {
                'bits': addr_width,
                'default': 0,
                'format': 'hex',
                'display_width': (addr_width + 3) // 4,
                'active_bits': (addr_width-1, 0),
                'description': 'Address'
            }
            
            # Add control field
            field_config['ctrl'] = {
                'bits': ctrl_width,
                'default': 0,
                'format': 'hex',
                'display_width': (ctrl_width + 3) // 4,
                'active_bits': (ctrl_width-1, 0),
                'description': 'Control'
            }
            
            # Add data fields
            for i in range(num_data):
                field_config[f'data{i}'] = {
                    'bits': data_width,
                    'default': 0,
                    'format': 'hex',
                    'display_width': (data_width + 3) // 4,
                    'active_bits': (data_width-1, 0),
                    'description': f'Data {i}'
                }
                
        # Create sequence
        sequence = cls(name, field_config)
        
        # Calculate field masks
        addr_mask = (1 << addr_width) - 1
        ctrl_mask = (1 << ctrl_width) - 1
        data_mask = (1 << data_width) - 1
        
        # Helper function to generate alternating bits
        def gen_alternating_ones(width):
            result = 0
            for i in range(0, width, 2):
                result |= (1 << i)
            return result
            
        def invert_bits(value, width):
            mask = (1 << width) - 1
            return (~value) & mask
        
        # Generate pattern based on specified type
        if pattern_type == "incremental":
            for i in range(num_transactions):
                # Use different prime multipliers for each field to ensure variation
                addr = (i * 3) & addr_mask
                ctrl = (i * 5) & ctrl_mask
                
                # Create data dictionary
                data_dict = {}
                for j in range(num_data):
                    data_dict[f'data{j}'] = ((i * (7 + j*2)) & data_mask)
                    
                # Add transaction
                sequence.add_write(addr, data_dict, {'ctrl': ctrl}, delay=1)
                
        elif pattern_type == "alternating":
            for i in range(num_transactions):
                # Different patterns in each loop
                if i % 4 == 0:
                    # All 1s in addr, alternating in ctrl and data
                    addr = addr_mask
                    ctrl = gen_alternating_ones(ctrl_width)
                    
                    data_dict = {}
                    for j in range(num_data):
                        if j % 2 == 0:
                            data_dict[f'data{j}'] = gen_alternating_ones(data_width)
                        else:
                            data_dict[f'data{j}'] = invert_bits(gen_alternating_ones(data_width), data_width)
                            
                elif i % 4 == 1:
                    # All 0s in addr, inverted alternating in ctrl and data
                    addr = 0
                    ctrl = invert_bits(gen_alternating_ones(ctrl_width), ctrl_width)
                    
                    data_dict = {}
                    for j in range(num_data):
                        if j % 2 == 0:
                            data_dict[f'data{j}'] = invert_bits(gen_alternating_ones(data_width), data_width)
                        else:
                            data_dict[f'data{j}'] = gen_alternating_ones(data_width)
                            
                elif i % 4 == 2:
                    # Alternating in addr, all 1s in ctrl, all 0s in data0, all 1s in data1, etc.
                    addr = gen_alternating_ones(addr_width)
                    ctrl = ctrl_mask
                    
                    data_dict = {}
                    for j in range(num_data):
                        data_dict[f'data{j}'] = data_mask if j % 2 else 0
                        
                else:
                    # Inverted alternating in addr, all 0s in ctrl, all 1s in data0, all 0s in data1, etc.
                    addr = invert_bits(gen_alternating_ones(addr_width), addr_width)
                    ctrl = 0
                    
                    data_dict = {}
                    for j in range(num_data):
                        data_dict[f'data{j}'] = 0 if j % 2 else data_mask
                        
                # Add transaction
                sequence.add_write(addr, data_dict, {'ctrl': ctrl}, delay=1)
                
        elif pattern_type == "random":
            for _ in range(num_transactions):
                # Random values for each field
                addr = random.randint(0, addr_mask)
                ctrl = random.randint(0, ctrl_mask)
                
                data_dict = {}
                for j in range(num_data):
                    data_dict[f'data{j}'] = random.randint(0, data_mask)
                    
                # Add transaction
                sequence.add_write(addr, data_dict, {'ctrl': ctrl}, delay=1)
                
        else:
            raise ValueError(f"Invalid pattern_type: {pattern_type}")
            
        return sequence
    
    @classmethod
    def create_full_empty_test(cls, name="full_empty", depth=10, 
                                addr_width=4, data_width=32, field_config=None):
        """
        Create a sequence to test buffer full and empty conditions.
        
        Args:
            name: Sequence name
            depth: Buffer depth
            addr_width: Width of address field
            data_width: Width of data field
            field_config: Field configuration
            
        Returns:
            Configured GAXISequence for full/empty testing
        """
        sequence = cls(name, field_config)
        
        # Calculate masks
        addr_mask = (1 << addr_width) - 1
        data_mask = (1 << data_width) - 1
        
        # Part 1: Fill buffer completely (test full condition)
        # Generate 2x depth packets to ensure full condition
        for i in range(depth * 2):
            addr = i & addr_mask
            data = i & data_mask
            
            # Add write with no delay to quickly fill buffer
            sequence.add_write(addr, data, delay=0)
            
        # Part 2: Configure sequence for empty test
        # Set randomizers for slow producer, fast consumer
        sequence.set_master_randomizer(FlexRandomizer({
            'valid_delay': ([[10, 20]], [1]),  # Long delays between writes
        }))
        
        sequence.set_slave_randomizer(FlexRandomizer({
            'ready_delay': ([[0, 0]], [1]),  # No delay for reads
        }))
            
        return sequence
    
    @classmethod
    def create_clock_ratio_test(cls, name="clock_ratio", addr_width=4, data_width=32, 
                                num_transactions=20, field_config=None):
        """
        Create a sequence specifically for testing different clock ratios in async buffers.
        
        Args:
            name: Sequence name
            addr_width: Width of address field
            data_width: Width of data field
            num_transactions: Number of transactions to generate
            field_config: Field configuration
            
        Returns:
            Configured GAXISequence for clock ratio testing
        """
        sequence = cls(name, field_config)
        
        # Calculate masks
        addr_mask = (1 << addr_width) - 1
        data_mask = (1 << data_width) - 1
        
        # Generate transactions with varying delays
        for i in range(num_transactions):
            addr = i & addr_mask
            data = i & data_mask
            
            # Add write with varying delays to stress CDC logic
            delay = 0 if i % 5 == 0 else (i % 3) + 1
            sequence.add_write(addr, data, delay=delay)
            
        return sequence
    
    @classmethod
    def create_stress_test(cls, name="stress", num_transactions=50, 
                            addr_width=4, data_width=32, field_config=None):
        """
        Create a comprehensive stress test sequence with various patterns.
        
        Args:
            name: Sequence name
            num_transactions: Total number of transactions
            addr_width: Width of address field
            data_width: Width of data field
            field_config: Field configuration
            
        Returns:
            Configured GAXISequence for stress testing
        """
        sequence = cls(name, field_config)
        
        # Calculate masks
        addr_mask = (1 << addr_width) - 1
        data_mask = (1 << data_width) - 1
        
        # Divide transactions into different phases
        phase_count = min(num_transactions // 5, 10)  # At least 5 phases, max 10 each
        
        # Phase 1: Back-to-back writes
        for i in range(phase_count):
            addr = i & addr_mask
            data = i & data_mask
            sequence.add_write(addr, data, delay=0)
            
        # Phase 2: Random addresses with maximum data values
        for i in range(phase_count):
            addr = random.randint(0, addr_mask)
            data = data_mask  # All 1s
            sequence.add_write(addr, data, delay=random.randint(0, 3))
            
        # Phase 3: Sequential addresses with walking ones
        for i in range(min(phase_count, data_width)):
            addr = (phase_count + i) & addr_mask
            data = 1 << (i % data_width)
            sequence.add_write(addr, data, delay=1)
            
        # Phase 4: Alternating reads and writes
        for i in range(phase_count):
            addr = (2*phase_count + i) & addr_mask
            if i % 2 == 0:
                data = (i * 0x55) & data_mask
                sequence.add_write(addr, data, delay=0)
            else:
                sequence.add_read(addr, delay=0)
                
        # Phase 5: Burst with long delay
        addr = (3*phase_count) & addr_mask
        for i in range(phase_count):
            data = (i * 0xFF) & data_mask
            sequence.add_write(addr, data, delay=0)
            
        # Add long delay at the end
        sequence.add_delay(20)
            
        return sequence
