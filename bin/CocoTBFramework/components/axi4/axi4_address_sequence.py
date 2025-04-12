"""
AXI4 Address Sequence

This module provides specialized sequence generators for AXI4 address channels (AW/AR).
It focuses on address generation with proper AXI4 protocol compliance, supporting
different burst types, sizes, and alignment requirements.
"""

import random
from typing import List, Dict, Any, Optional, Tuple, Union
from collections import deque

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet
from CocoTBFramework.components.axi4.axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG
)


class AXI4AddressSequence:
    """
    AXI4 Address Sequence generator with protocol awareness.
    
    This class provides utilities for creating sequences of AXI4 address transactions
    that comply with the AXI4 protocol rules, including proper burst configuration,
    address alignment, and sizing.
    """

    # AXI4 burst types
    BURST_FIXED = 0
    BURST_INCR = 1
    BURST_WRAP = 2
    
    # AXI4 burst sizes (log2 of number of bytes)
    SIZE_1B = 0    # 1 byte
    SIZE_2B = 1    # 2 bytes
    SIZE_4B = 2    # 4 bytes
    SIZE_8B = 3    # 8 bytes
    SIZE_16B = 4   # 16 bytes
    SIZE_32B = 5   # 32 bytes
    SIZE_64B = 6   # 64 bytes
    SIZE_128B = 7  # 128 bytes
    
    # AXI4 protection types
    PROT_UNPRIVILEGED = 0
    PROT_PRIVILEGED = 1
    PROT_SECURE = 0
    PROT_NONSECURE = 2
    PROT_DATA = 0
    PROT_INSTRUCTION = 4
    
    # AXI4 cache types
    CACHE_DEVICE_NON_BUFFERABLE = 0x0
    CACHE_DEVICE_BUFFERABLE = 0x1
    CACHE_NORMAL_NON_CACHEABLE_NON_BUFFERABLE = 0x2
    CACHE_NORMAL_NON_CACHEABLE_BUFFERABLE = 0x3
    CACHE_WRITE_THROUGH_NO_ALLOCATE = 0x6
    CACHE_WRITE_THROUGH_READ_ALLOCATE = 0xA
    CACHE_WRITE_THROUGH_WRITE_ALLOCATE = 0xE
    CACHE_WRITE_BACK_NO_ALLOCATE = 0x7
    CACHE_WRITE_BACK_READ_ALLOCATE = 0xB
    CACHE_WRITE_BACK_WRITE_ALLOCATE = 0xF
    CACHE_WRITE_BACK_READ_WRITE_ALLOCATE = 0xF

    def __init__(self, name: str = "axi4_addr", 
                 channel: str = "AW", 
                 id_width: int = 8, 
                 addr_width: int = 32, 
                 user_width: int = 1):
        """
        Initialize the AXI4 Address Sequence.

        Args:
            name: Sequence name
            channel: AXI4 channel ('AW' or 'AR')
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            user_width: Width of user field in bits
        """
        self.name = name
        self.channel = channel.upper()
        
        if self.channel not in ['AW', 'AR']:
            raise ValueError(f"Channel must be either 'AW' or 'AR', got '{channel}'")
        
        self.id_width = id_width
        self.addr_width = addr_width
        self.user_width = user_width
        
        # Select appropriate field config based on channel
        if self.channel == 'AW':
            self.field_config = self._adjust_field_config(AXI4_AW_FIELD_CONFIG)
        else:  # AR
            self.field_config = self._adjust_field_config(AXI4_AR_FIELD_CONFIG)
        
        # Initialize sequence data
        self.addr_sequence = []
        self.id_sequence = []
        self.len_sequence = []
        self.size_sequence = []
        self.burst_sequence = []
        self.lock_sequence = []
        self.cache_sequence = []
        self.prot_sequence = []
        self.qos_sequence = []
        self.region_sequence = []
        self.user_sequence = []
        
        # Calculated properties
        self.addr_mask = (1 << addr_width) - 1
        
        # Randomization options
        self.randomizer = None
        self.use_random_selection = False
        
        # Generated packets
        self.packets = deque()
        
        # Iterators for sequences
        self.addr_iter = None
        self.id_iter = None
        self.len_iter = None
        self.size_iter = None
        self.burst_iter = None
        self.lock_iter = None
        self.cache_iter = None
        self.prot_iter = None
        self.qos_iter = None
        self.region_iter = None
        self.user_iter = None
        
        # Statistics
        self.stats = {
            'total_transactions': 0,
            'alignment_fixes': 0,
            'protocol_violations': 0
        }

    def _adjust_field_config(self, field_config: FieldConfig) -> FieldConfig:
        """
        Adjust field configuration for specified widths.
        
        Args:
            field_config: Base field configuration
            
        Returns:
            Adjusted field configuration
        """
        # Create a copy to avoid modifying the original
        adjusted_config = field_config
        
        # Update ID width
        if self.channel == 'AW':
            if adjusted_config.has_field('awid'):
                adjusted_config.update_field_width('awid', self.id_width)
        else:  # AR
            if adjusted_config.has_field('arid'):
                adjusted_config.update_field_width('arid', self.id_width)
        
        # Update address width
        if self.channel == 'AW':
            if adjusted_config.has_field('awaddr'):
                adjusted_config.update_field_width('awaddr', self.addr_width)
        else:  # AR
            if adjusted_config.has_field('araddr'):
                adjusted_config.update_field_width('araddr', self.addr_width)
        
        # Update user width
        if self.channel == 'AW':
            if adjusted_config.has_field('awuser'):
                adjusted_config.update_field_width('awuser', self.user_width)
        else:  # AR
            if adjusted_config.has_field('aruser'):
                adjusted_config.update_field_width('aruser', self.user_width)
        
        return adjusted_config

    def add_transaction(self, 
                        addr: int, 
                        id_value: int = 0, 
                        burst_len: int = 0, 
                        burst_size: int = 2, 
                        burst_type: int = 1, 
                        lock: int = 0, 
                        cache: int = 0, 
                        prot: int = 0, 
                        qos: int = 0, 
                        region: int = 0, 
                        user: int = 0) -> 'AXI4AddressSequence':
        """
        Add an address transaction to the sequence with AXI4 protocol validation.
        
        Args:
            addr: Target address
            id_value: Transaction ID
            burst_len: Burst length (0 = 1 beat, 1 = 2 beats, etc., max 255)
            burst_size: Burst size (0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes, etc.)
            burst_type: Burst type (0 = FIXED, 1 = INCR, 2 = WRAP)
            lock: Lock type (0 = Normal, 1 = Exclusive)
            cache: Cache type
            prot: Protection type
            qos: Quality of Service
            region: Region identifier
            user: User signal
            
        Returns:
            Self for method chaining
        """
        # Validate and adjust values for AXI4 protocol compliance
        adjusted_addr, aligned = self._align_address(addr, burst_size)
        if not aligned:
            self.stats['alignment_fixes'] += 1
        
        # Validate burst parameters
        valid, msg = self._validate_burst_params(adjusted_addr, burst_len, burst_size, burst_type)
        if not valid:
            self.stats['protocol_violations'] += 1
            print(f"WARNING: {msg}")
            
            # Try to fix common issues
            if burst_type == self.BURST_WRAP:
                # For WRAP bursts, round burst_len to a power of 2
                orig_len = burst_len
                # Find the nearest power of 2 minus 1 (for burst_len)
                p2 = 1
                while p2 < (burst_len + 1):
                    p2 *= 2
                burst_len = p2 - 1
                print(f"  Adjusted burst length from {orig_len} to {burst_len} for WRAP burst")
        
        # Add to sequence
        self.addr_sequence.append(adjusted_addr)
        self.id_sequence.append(id_value)
        self.len_sequence.append(burst_len)
        self.size_sequence.append(burst_size)
        self.burst_sequence.append(burst_type)
        self.lock_sequence.append(lock)
        self.cache_sequence.append(cache)
        self.prot_sequence.append(prot)
        self.qos_sequence.append(qos)
        self.region_sequence.append(region)
        self.user_sequence.append(user)
        
        # Update statistics
        self.stats['total_transactions'] += 1
            
        return self

    def _align_address(self, addr: int, size: int) -> Tuple[int, bool]:
        """
        Align address according to AXI4 requirements.
        
        Args:
            addr: Address to align
            size: Burst size (log2 of number of bytes)
            
        Returns:
            Tuple of (aligned_address, was_already_aligned)
        """
        # Calculate byte alignment requirement (2^size)
        alignment = 1 << size
        mask = alignment - 1
        
        # Check if address is already aligned
        is_aligned = (addr & mask) == 0
        
        # Align address (clear low bits)
        aligned_addr = addr & ~mask
        
        return aligned_addr, is_aligned

    def _validate_burst_params(self, addr: int, len_value: int, size: int, burst_type: int) -> Tuple[bool, str]:
        """
        Validate burst parameters according to AXI4 protocol rules.
        
        Args:
            addr: Starting address
            len_value: Burst length (0 = 1 transfer, 255 = 256 transfers)
            size: Transfer size (log2 of number of bytes)
            burst_type: Burst type (0 = FIXED, 1 = INCR, 2 = WRAP)
            
        Returns:
            Tuple of (is_valid, error_message)
        """
        # Check burst type
        if burst_type not in [0, 1, 2]:
            return False, f"Invalid burst type: {burst_type}"
        
        # Check burst length
        if len_value < 0 or len_value > 255:
            return False, f"Burst length {len_value} out of range (0-255)"
        
        # Check burst size
        if size < 0 or size > 7:
            return False, f"Burst size {size} out of range (0-7)"
        
        # Check alignment
        byte_count = 1 << size
        if addr % byte_count != 0:
            return False, f"Address 0x{addr:X} not aligned for size {size} ({byte_count} bytes)"
        
        # Special checks for WRAP bursts
        if burst_type == self.BURST_WRAP:
            # WRAP bursts need length to be 2, 4, 8, or 16
            if (len_value + 1) not in [2, 4, 8, 16]:
                return False, f"WRAP burst length must be 1, 3, 7, or 15 (for 2, 4, 8, or 16 transfers)"
            
            # Check 4KB boundary crossing
            burst_bytes = (len_value + 1) * byte_count
            end_addr = addr + burst_bytes - 1
            
            if (addr & ~0xFFF) != (end_addr & ~0xFFF):
                return False, f"WRAP burst crosses 4KB boundary: 0x{addr:X} to 0x{end_addr:X}"
                
        # For INCR bursts, check 4KB boundary crossing
        if burst_type == self.BURST_INCR:
            burst_bytes = (len_value + 1) * byte_count
            end_addr = addr + burst_bytes - 1
            
            if (addr & ~0xFFF) != (end_addr & ~0xFFF):
                # This is allowed, but warn about potential inefficiency
                return True, f"INCR burst crosses 4KB boundary: 0x{addr:X} to 0x{end_addr:X} (allowed but inefficient)"
        
        return True, "Valid burst parameters"

    def calculate_burst_addresses(self, 
                                addr: int, 
                                len_value: int, 
                                size: int, 
                                burst_type: int) -> List[int]:
        """
        Calculate all addresses in a burst according to AXI4 protocol rules.
        
        Args:
            addr: Starting address
            len_value: Burst length (0 = 1 transfer, 255 = 256 transfers)
            size: Transfer size (log2 of number of bytes)
            burst_type: Burst type (0 = FIXED, 1 = INCR, 2 = WRAP)
            
        Returns:
            List of addresses in the burst
        """
        addresses = []
        byte_count = 1 << size
        
        # Ensure address is aligned
        aligned_addr, _ = self._align_address(addr, size)
        
        # Generate addresses for each transfer in the burst
        for i in range(len_value + 1):
            if burst_type == self.BURST_FIXED:
                # Fixed burst - same address for all transfers
                next_addr = aligned_addr
                
            elif burst_type == self.BURST_INCR:
                # Incrementing burst - increment address by byte count
                next_addr = aligned_addr + (i * byte_count)
                
            elif burst_type == self.BURST_WRAP:
                # Wrapping burst - wrap at boundaries based on burst size
                
                # Calculate the wrap boundary
                burst_length = len_value + 1
                wrap_size = burst_length * byte_count
                wrap_mask = wrap_size - 1
                wrap_boundary = aligned_addr & ~wrap_mask
                
                # Calculate address for this beat
                next_addr = wrap_boundary + ((aligned_addr + (i * byte_count)) & wrap_mask)
                
            else:
                # Invalid burst type
                raise ValueError(f"Invalid burst type: {burst_type}")
            
            addresses.append(next_addr)
        
        return addresses

    def set_random_selection(self, enable: bool = True) -> 'AXI4AddressSequence':
        """
        Enable/disable random selection from sequences.

        Args:
            enable: True to enable random selection, False to use sequential
            
        Returns:
            Self for method chaining
        """
        self.use_random_selection = enable
        return self

    def set_randomizer(self, randomizer: FlexRandomizer) -> 'AXI4AddressSequence':
        """
        Set the randomizer for timing constraints.

        Args:
            randomizer: FlexRandomizer instance
            
        Returns:
            Self for method chaining
        """
        self.randomizer = randomizer
        return self

    def reset_iterators(self):
        """Reset all sequence iterators to the beginning."""
        self.addr_iter = iter(self.addr_sequence)
        self.id_iter = iter(self.id_sequence)
        self.len_iter = iter(self.len_sequence)
        self.size_iter = iter(self.size_sequence)
        self.burst_iter = iter(self.burst_sequence)
        self.lock_iter = iter(self.lock_sequence)
        self.cache_iter = iter(self.cache_sequence)
        self.prot_iter = iter(self.prot_sequence)
        self.qos_iter = iter(self.qos_sequence)
        self.region_iter = iter(self.region_sequence)
        self.user_iter = iter(self.user_sequence)

    def _next_value(self, sequence: List[Any], iterator: Optional[Any]) -> Any:
        """
        Get the next value from a sequence with proper iterator handling.
        
        Args:
            sequence: List of values
            iterator: Iterator for the sequence
            
        Returns:
            Next value in the sequence
        """
        if not sequence:
            return 0
            
        if self.use_random_selection:
            return random.choice(sequence)
            
        try:
            if iterator is None:
                iterator = iter(sequence)
            return next(iterator)
        except StopIteration:
            # Reset iterator and try again
            iterator = iter(sequence)
            return next(iterator)

    def generate_packet(self) -> AXI4Packet:
        """
        Generate the next address packet in the sequence.

        Returns:
            AXI4 address packet (AW or AR)
        """
        # Get field values from sequences
        addr = self._next_value(self.addr_sequence, self.addr_iter)
        id_value = self._next_value(self.id_sequence, self.id_iter)
        len_value = self._next_value(self.len_sequence, self.len_iter)
        size = self._next_value(self.size_sequence, self.size_iter)
        burst = self._next_value(self.burst_sequence, self.burst_iter)
        lock = self._next_value(self.lock_sequence, self.lock_iter)
        cache = self._next_value(self.cache_sequence, self.cache_iter)
        prot = self._next_value(self.prot_sequence, self.prot_iter)
        qos = self._next_value(self.qos_sequence, self.qos_iter)
        region = self._next_value(self.region_sequence, self.region_iter)
        user = self._next_value(self.user_sequence, self.user_iter)
        
        # Create appropriate packet type
        if self.channel == 'AW':
            packet = AXI4Packet.create_aw_packet(
                awid=id_value,
                awaddr=addr,
                awlen=len_value,
                awsize=size,
                awburst=burst,
                awlock=lock,
                awcache=cache,
                awprot=prot,
                awqos=qos,
                awregion=region,
                awuser=user
            )
        else:  # AR
            packet = AXI4Packet.create_ar_packet(
                arid=id_value,
                araddr=addr,
                arlen=len_value,
                arsize=size,
                arburst=burst,
                arlock=lock,
                arcache=cache,
                arprot=prot,
                arqos=qos,
                arregion=region,
                aruser=user
            )
        
        return packet

    def generate_packets(self, count: Optional[int] = None) -> List[AXI4Packet]:
        """
        Generate multiple address packets.

        Args:
            count: Number of packets to generate, or None for all in sequence

        Returns:
            List of generated packets
        """
        # Clear previous packets
        self.packets.clear()

        # Reset iterators
        self.reset_iterators()

        # Default to length of sequence if count not specified
        if count is None and self.addr_sequence:
            count = len(self.addr_sequence)
        elif count is None:
            count = 0

        # Generate packets
        for _ in range(count):
            packet = self.generate_packet()
            self.packets.append(packet)

        return list(self.packets)

    def get_packet(self, index: int = 0) -> Optional[AXI4Packet]:
        """
        Get a specific packet from the generated list.

        Args:
            index: Packet index

        Returns:
            Packet at specified index or None if no packets
        """
        if not self.packets:
            self.generate_packets()

        if not self.packets:
            return None

        if self.use_random_selection:
            return random.choice(self.packets)

        return self.packets[index % len(self.packets)]

    def get_stats(self) -> Dict[str, Any]:
        """
        Get statistics about the sequence generation.
        
        Returns:
            Dictionary with statistics
        """
        return self.stats

    # ========================================================================
    # Factory Methods
    # ========================================================================
    
    @classmethod
    def create_sequential_addresses(cls, 
                                  start_addr: int = 0, 
                                  count: int = 10, 
                                  increment: int = 4, 
                                  id_value: int = 0, 
                                  burst_size: int = 2, 
                                  channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence of incrementing addresses.
        
        Args:
            start_addr: Starting address
            count: Number of transactions
            increment: Address increment between transactions
            id_value: Transaction ID to use
            burst_size: Burst size (log2 of number of bytes)
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="sequential", channel=channel)
        
        # Calculate proper alignment
        aligned_addr, _ = sequence._align_address(start_addr, burst_size)
        
        # Add aligned addresses
        for i in range(count):
            addr = aligned_addr + (i * increment)
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_size=burst_size,
                burst_type=cls.BURST_INCR,
                lock=1  # Set LOCK=1 for exclusive access
            )
            
        return sequence

    @classmethod
    def create_4k_boundary_test(cls, 
                              channel: str = "AW",
                              id_value: int = 0) -> 'AXI4AddressSequence':
        """
        Create a sequence of transactions that test 4KB boundary cases.
        
        Args:
            channel: AXI4 channel ('AW' or 'AR')
            id_value: Transaction ID to use
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="4k_boundary_test", channel=channel)
        
        # Test cases near 4KB boundaries
        test_cases = [
            # (address, burst_len, burst_size)
            (0x00000FF0, 3, 2),  # Near 4KB boundary with 4-byte size
            (0x00000FF8, 1, 2),  # Just before 4KB boundary
            (0x00001000, 7, 2),  # At 4KB boundary
            (0x00001FF0, 3, 2),  # Near second 4KB boundary
            (0x00000FE0, 7, 2),  # Cross 4KB boundary
            (0x00001000 - 4, 1, 2),  # Straddle 4KB boundary
        ]
        
        for addr, burst_len, burst_size in test_cases:
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=cls.BURST_INCR  # Use INCR bursts
            )
            
        return sequence

    @classmethod
    def create_protection_variations(cls, 
                                   start_addr: int = 0, 
                                   id_value: int = 0, 
                                   channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence with various protection attribute combinations.
        
        Args:
            start_addr: Starting address
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="prot_variations", channel=channel)
        
        # Protection values to test
        prot_values = [
            cls.PROT_UNPRIVILEGED | cls.PROT_SECURE | cls.PROT_DATA,            # 0: Unprivileged, secure, data
            cls.PROT_PRIVILEGED | cls.PROT_SECURE | cls.PROT_DATA,              # 1: Privileged, secure, data
            cls.PROT_UNPRIVILEGED | cls.PROT_NONSECURE | cls.PROT_DATA,         # 2: Unprivileged, non-secure, data
            cls.PROT_PRIVILEGED | cls.PROT_NONSECURE | cls.PROT_DATA,           # 3: Privileged, non-secure, data
            cls.PROT_UNPRIVILEGED | cls.PROT_SECURE | cls.PROT_INSTRUCTION,     # 4: Unprivileged, secure, instruction
            cls.PROT_PRIVILEGED | cls.PROT_SECURE | cls.PROT_INSTRUCTION,       # 5: Privileged, secure, instruction
            cls.PROT_UNPRIVILEGED | cls.PROT_NONSECURE | cls.PROT_INSTRUCTION,  # 6: Unprivileged, non-secure, instruction
            cls.PROT_PRIVILEGED | cls.PROT_NONSECURE | cls.PROT_INSTRUCTION     # 7: Privileged, non-secure, instruction
        ]
        
        # Add transactions with different protection attributes
        for i, prot in enumerate(prot_values):
            addr = start_addr + (i * 4)  # Increment by 4 bytes
            
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=0,  # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR,
                prot=prot
            )
            
        return sequence

    @classmethod
    def create_cache_variations(cls, 
                              start_addr: int = 0, 
                              id_value: int = 0, 
                              channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence with various cache attribute combinations.
        
        Args:
            start_addr: Starting address
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="cache_variations", channel=channel)
        
        # Common cache values to test
        cache_values = [
            cls.CACHE_DEVICE_NON_BUFFERABLE,
            cls.CACHE_DEVICE_BUFFERABLE,
            cls.CACHE_NORMAL_NON_CACHEABLE_NON_BUFFERABLE,
            cls.CACHE_NORMAL_NON_CACHEABLE_BUFFERABLE,
            cls.CACHE_WRITE_THROUGH_NO_ALLOCATE,
            cls.CACHE_WRITE_THROUGH_READ_ALLOCATE,
            cls.CACHE_WRITE_THROUGH_WRITE_ALLOCATE,
            cls.CACHE_WRITE_BACK_NO_ALLOCATE,
            cls.CACHE_WRITE_BACK_READ_ALLOCATE,
            cls.CACHE_WRITE_BACK_WRITE_ALLOCATE
        ]
        
        # Add transactions with different cache attributes
        for i, cache in enumerate(cache_values):
            addr = start_addr + (i * 4)  # Increment by 4 bytes
            
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=0,  # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR,
                cache=cache
            )
            
        return sequence

    @classmethod
    def create_qos_variations(cls, 
                            start_addr: int = 0, 
                            id_value: int = 0, 
                            channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence with different QoS values.
        
        Args:
            start_addr: Starting address
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="qos_variations", channel=channel)
        
        # QoS values to test (0-15)
        qos_values = [0, 1, 2, 4, 8, 15]
        
        # Add transactions with different QoS values
        for i, qos in enumerate(qos_values):
            addr = start_addr + (i * 4)  # Increment by 4 bytes
            
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=0,  # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR,
                qos=qos
            )
            
        return sequence

    @classmethod
    def create_random_transactions(cls, 
                                 count: int = 10, 
                                 addr_range: Tuple[int, int] = (0, 0xFFFF), 
                                 id_range: Tuple[int, int] = (0, 15),
                                 channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence of random but legal AXI4 transactions.
        
        Args:
            count: Number of transactions to generate
            addr_range: (min, max) address range
            id_range: (min, max) ID range
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="random_transactions", channel=channel)
        
        # Possible burst types
        burst_types = [cls.BURST_FIXED, cls.BURST_INCR, cls.BURST_WRAP]
        
        # Possible burst sizes (0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes, etc.)
        burst_sizes = [0, 1, 2, 3]  # 1, 2, 4, 8 bytes
        
        # For WRAP bursts, valid lengths are 1, 3, 7, 15 (for 2, 4, 8, 16 transfers)
        wrap_lengths = [1, 3, 7, 15]
        
        for _ in range(count):
            # Generate random values
            id_value = random.randint(id_range[0], id_range[1])
            burst_size = random.choice(burst_sizes)
            burst_type = random.choice(burst_types)
            
            # Determine burst length based on burst type
            if burst_type == cls.BURST_WRAP:
                burst_len = random.choice(wrap_lengths)
            else:
                burst_len = random.randint(0, 15)  # 1-16 transfers
            
            # Generate aligned address within range
            byte_count = 1 << burst_size
            addr_min = addr_range[0] - (addr_range[0] % byte_count)  # Align to burst size
            addr_max = addr_range[1] - ((addr_range[1] % byte_count) + byte_count)  # Ensure not beyond range
            
            if addr_max < addr_min:
                addr_max = addr_min  # Ensure valid range
                
            # Generate random aligned address
            addr = random.randint(addr_min, addr_max)
            if addr % byte_count != 0:
                addr = (addr // byte_count) * byte_count  # Ensure alignment
            
            # For WRAP bursts, ensure we don't cross 4KB boundaries
            if burst_type == cls.BURST_WRAP:
                # Calculate burst bytes
                burst_bytes = (burst_len + 1) * byte_count
                if (addr & ~0xFFF) != ((addr + burst_bytes - 1) & ~0xFFF):
                    # Align to lower 4KB boundary plus offset to avoid crossing
                    addr = (addr & ~0xFFF) | (addr & (burst_bytes - 1))
            
            # Add the transaction
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=burst_type
            )
            
        return sequence

    @classmethod
    def create_comprehensive_test(cls, channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a comprehensive test sequence combining various AXI4 address features.
        
        Args:
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence with a variety of transaction types
        """
        sequence = cls(name="comprehensive_test", channel=channel)
        
        # Add sequential single-beat transactions
        addr = 0x1000
        for i in range(5):
            sequence.add_transaction(
                addr=addr + (i * 4),
                id_value=0,
                burst_len=0,   # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR
            )
        
        # Add INCR burst transactions with different IDs
        addr = 0x2000
        for i in range(3):
            sequence.add_transaction(
                addr=addr + (i * 32),
                id_value=i + 1,
                burst_len=7,   # 8 beats
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR
            )
        
        # Add WRAP burst transactions
        addr = 0x3000
        for i, length in enumerate([1, 3, 7, 15]):  # 2, 4, 8, 16 transfers
            sequence.add_transaction(
                addr=addr + (i * 64),
                id_value=5,
                burst_len=length,
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_WRAP
            )
        
        # Add FIXED burst transactions
        addr = 0x4000
        for i in range(3):
            sequence.add_transaction(
                addr=addr + (i * 16),
                id_value=6,
                burst_len=3,   # 4 beats
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_FIXED
            )
        
        # Add transactions with exclusive access
        addr = 0x5000
        for i in range(2):
            sequence.add_transaction(
                addr=addr + (i * 4),
                id_value=7,
                burst_len=0,   # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR,
                lock=1  # Exclusive access
            )
        
        # Add transactions with different protection attributes
        addr = 0x6000
        for prot in range(8):  # All 8 combinations of protection bits
            sequence.add_transaction(
                addr=addr + (prot * 4),
                id_value=8,
                burst_len=0,   # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR,
                prot=prot
            )
        
        # Add transactions with different cache attributes
        addr = 0x7000
        for cache in [0, 3, 7, 15]:  # Selected cache types
            sequence.add_transaction(
                addr=addr + (cache * 4),
                id_value=9,
                burst_len=0,   # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR,
                cache=cache
            )
        
        # Add transactions with different QoS values
        addr = 0x8000
        for qos in [0, 4, 8, 15]:  # Selected QoS values
            sequence.add_transaction(
                addr=addr + (qos * 4),
                id_value=10,
                burst_len=0,   # Single beat
                burst_size=2,  # 4 bytes
                burst_type=cls.BURST_INCR,
                qos=qos
            )
        
        # Add transactions that test 4KB boundary crossing
        sequence.add_transaction(
            addr=0x0000FFE0,
            id_value=11,
            burst_len=7,   # 8 beats
            burst_size=2,  # 4 bytes
            burst_type=cls.BURST_INCR
        )
        
        # Add transactions with different burst sizes
        addr = 0x9000
        for size in range(4):  # 1, 2, 4, 8 bytes
            sequence.add_transaction(
                addr=addr + (1 << (size + 4)),  # Ensure proper alignment
                id_value=12,
                burst_len=3,   # 4 beats
                burst_size=size,
                burst_type=cls.BURST_INCR
            )
        
        return sequence
                burst_type=cls.BURST_INCR  # Use INCR bursts
            )
            
        return sequence

    @classmethod
    def create_incrementing_bursts(cls, 
                                 start_addr: int = 0, 
                                 count: int = 10, 
                                 burst_len: int = 7, 
                                 burst_size: int = 2, 
                                 id_value: int = 0,
                                 channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence of incrementing burst transactions.
        
        Args:
            start_addr: Starting address
            count: Number of transactions
            burst_len: Burst length (0 = 1 transfer, 7 = 8 transfers)
            burst_size: Burst size (log2 of number of bytes)
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="incr_bursts", channel=channel)
        
        # Calculate proper alignment
        aligned_addr, _ = sequence._align_address(start_addr, burst_size)
        
        # Calculate byte count for this burst size
        byte_count = 1 << burst_size
        
        # Add bursts with properly spaced addresses
        for i in range(count):
            # Calculate next burst address (after previous burst)
            addr = aligned_addr + (i * (burst_len + 1) * byte_count)
            
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=cls.BURST_INCR  # Use INCR bursts
            )
            
        return sequence

    @classmethod
    def create_wrapping_bursts(cls, 
                             start_addr: int = 0, 
                             count: int = 4, 
                             burst_lens: List[int] = [1, 3, 7, 15],
                             burst_size: int = 2, 
                             id_value: int = 0,
                             channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence of wrapping burst transactions.
        
        Args:
            start_addr: Starting address
            count: Number of transactions
            burst_lens: List of burst lengths to use (should be 2^n-1 for WRAP bursts)
            burst_size: Burst size (log2 of number of bytes)
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="wrap_bursts", channel=channel)
        
        # Calculate proper alignment
        aligned_addr, _ = sequence._align_address(start_addr, burst_size)
        
        # Calculate byte count for this burst size
        byte_count = 1 << burst_size
        
        # Add bursts with properly spaced addresses
        addr = aligned_addr
        for i in range(count):
            # Select a burst length from the provided list
            burst_len = burst_lens[i % len(burst_lens)]
            
            # For WRAP bursts, ensure len+1 is a power of 2 (2, 4, 8, 16)
            if (burst_len + 1) & (burst_len) != 0:
                # Find the nearest power of 2 minus 1
                p2 = 1
                while p2 < (burst_len + 1):
                    p2 *= 2
                burst_len = p2 - 1
            
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=cls.BURST_WRAP  # Use WRAP bursts
            )
            
            # Calculate next burst address (increment by burst size)
            burst_bytes = (burst_len + 1) * byte_count
            addr += burst_bytes
            
        return sequence

    @classmethod
    def create_fixed_bursts(cls, 
                          addresses: List[int], 
                          burst_len: int = 7, 
                          burst_size: int = 2, 
                          id_value: int = 0,
                          channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence of fixed burst transactions.
        
        Args:
            addresses: List of addresses to use
            burst_len: Burst length (0 = 1 transfer, 7 = 8 transfers)
            burst_size: Burst size (log2 of number of bytes)
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="fixed_bursts", channel=channel)
        
        # Add a fixed burst for each address
        for addr in addresses:
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=cls.BURST_FIXED  # Use FIXED bursts
            )
            
        return sequence

    @classmethod
    def create_varied_ids(cls, 
                        start_addr: int = 0, 
                        count: int = 10, 
                        id_values: List[int] = [0, 1, 2, 3],
                        burst_size: int = 2, 
                        channel: str = "AW") -> 'AXI4AddressSequence':
        """
        Create a sequence with varying transaction IDs.
        
        Args:
            start_addr: Starting address
            count: Number of transactions
            id_values: List of IDs to use
            burst_size: Burst size (log2 of number of bytes)
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="varied_ids", channel=channel)
        
        # Calculate proper alignment
        aligned_addr, _ = sequence._align_address(start_addr, burst_size)
        
        # Calculate byte count for this burst size
        byte_count = 1 << burst_size
        
        # Add transactions with different IDs
        for i in range(count):
            # Calculate address
            addr = aligned_addr + (i * byte_count)
            
            # Select ID from the list
            id_value = id_values[i % len(id_values)]
            
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_size=burst_size,
                burst_type=cls.BURST_INCR  # Use INCR bursts
            )
            
        return sequence

    @classmethod
    def create_exclusive_accesses(cls, 
                                addresses: List[int], 
                                id_value: int = 0, 
                                burst_size: int = 2,
                                channel: str = "AR") -> 'AXI4AddressSequence':
        """
        Create a sequence of exclusive access transactions.
        
        Args:
            addresses: List of addresses to use
            id_value: Transaction ID to use
            burst_size: Burst size (log2 of number of bytes)
            channel: AXI4 channel ('AW' or 'AR')
            
        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="exclusive", channel=channel)
        
        # Add exclusive access for each address
        for addr in addresses:
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_size=burst_size,