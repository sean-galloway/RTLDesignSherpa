"""
AXI4 Address Sequence

This module provides specialized sequence generators for AXI4 address channels (AW/AR).
It focuses on address generation with proper AXI4 protocol compliance, supporting
different burst types, sizes, and alignment requirements.
"""

import random
from typing import Dict, List, Any, Optional, Tuple, Union
from collections import deque

from ..field_config import FieldConfig
from ..flex_randomizer import FlexRandomizer
from ..gaxi.gaxi_sequence import GAXISequence
from .axi4_packet import AXI4Packet
from .axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG
)
from .axi4_seq_base import AXI4BaseSequence
from ..randomization_config import RandomizationConfig, RandomizationMode


class AXI4AddressSequence(AXI4BaseSequence):
    """
    AXI4 Address Sequence generator with protocol awareness.

    This class provides utilities for creating sequences of AXI4 address transactions
    that comply with the AXI4 protocol rules, including proper burst configuration,
    address alignment, and sizing.
    """

    def __init__(self, name: str = "axi4_addr",
                    channel: str = "AW",
                    id_width: int = 8,
                    addr_width: int = 32,
                    user_width: int = 1,
                    randomization_config: Optional[RandomizationConfig] = None):
        """
        Initialize the AXI4 Address Sequence.

        Args:
            name: Sequence name
            channel: AXI4 channel ('AW' or 'AR')
            id_width: Width of ID field in bits
            addr_width: Width of address field in bits
            user_width: Width of user field in bits
            randomization_config: Optional randomization configuration
        """
        super().__init__(name=name, randomization_config=randomization_config)

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
        self.stats.update({
            'alignment_fixes': 0,
            'protocol_violations': 0
        })

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
        elif adjusted_config.has_field('arid'):
            adjusted_config.update_field_width('arid', self.id_width)

        # Update address width
        if self.channel == 'AW':
            if adjusted_config.has_field('awaddr'):
                adjusted_config.update_field_width('awaddr', self.addr_width)
        elif adjusted_config.has_field('araddr'):
            adjusted_config.update_field_width('araddr', self.addr_width)

        # Update user width
        if self.channel == 'AW':
            if adjusted_config.has_field('awuser'):
                adjusted_config.update_field_width('awuser', self.user_width)
        elif adjusted_config.has_field('aruser'):
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
        adjusted_addr = self.align_address(addr, burst_size)
        aligned = (adjusted_addr == addr)

        if not aligned:
            self.stats['alignment_fixes'] += 1

        # Validate burst parameters using base class method
        valid, msg = self.validate_burst_parameters(adjusted_addr, burst_len, burst_size, burst_type)
        if not valid:
            self.stats['protocol_violations'] += 1
            self.log_warning(f"Protocol violation: {msg}")

            # Try to fix common issues
            if burst_type == self.BURST_WRAP:
                # For WRAP bursts, round burst_len to a power of 2
                orig_len = burst_len
                # Find the nearest power of 2 minus 1 (for burst_len)
                burst_len = self.next_power_of_two(burst_len + 1) - 1
                self.log_info(f"Adjusted burst length from {orig_len} to {burst_len} for WRAP burst")

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

    def _get_field_name_for_sequence(self, sequence: List[Any]) -> str:
        """
        Determine the field name based on the sequence.
        This is a helper for randomization.

        Args:
            sequence: Sequence list

        Returns:
            Field name for randomization
        """
        # Determine which sequence this is
        if sequence is self.addr_sequence:
            return "addr"
        elif sequence is self.id_sequence:
            return "id"
        elif sequence is self.len_sequence:
            return "len"
        elif sequence is self.size_sequence:
            return "size"
        elif sequence is self.burst_sequence:
            return "burst"
        elif sequence is self.lock_sequence:
            return "lock"
        elif sequence is self.cache_sequence:
            return "cache"
        elif sequence is self.prot_sequence:
            return "prot"
        elif sequence is self.qos_sequence:
            return "qos"
        elif sequence is self.region_sequence:
            return "region"
        elif sequence is self.user_sequence:
            return "user"
        # Default
        return "field"

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
            # Use randomization_config instead of direct random.choice
            field_name = f"{self.channel.lower()}_{self._get_field_name_for_sequence(sequence)}"
            return self.get_random_value(field_name)

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
            return AXI4Packet.create_aw_packet(
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
                awuser=user,
            )
        else:  # AR
            return AXI4Packet.create_ar_packet(
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
                aruser=user,
            )

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
        if count is None:
            if self.addr_sequence:
                count = len(self.addr_sequence)
            else:
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
            field_name = f"{self.channel.lower()}_packet_index"
            random_index = self.get_random_value(field_name, 0, len(self.packets) - 1)
            return self.packets[random_index]

        return self.packets[index % len(self.packets)]

    def cleanup(self) -> None:
        """
        Release resources to prevent memory leaks.
        """
        # Clear sequence lists
        self.addr_sequence.clear()
        self.id_sequence.clear()
        self.len_sequence.clear()
        self.size_sequence.clear()
        self.burst_sequence.clear()
        self.lock_sequence.clear()
        self.cache_sequence.clear()
        self.prot_sequence.clear()
        self.qos_sequence.clear()
        self.region_sequence.clear()
        self.user_sequence.clear()

        # Clear packet queue
        self.packets.clear()

        # Clear iterators
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

        # Call base class cleanup
        super().cleanup()

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
                                    channel: str = "AW",
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence of incrementing addresses.

        Args:
            start_addr: Starting address
            count: Number of transactions
            increment: Address increment between transactions
            id_value: Transaction ID to use
            burst_size: Burst size (log2 of number of bytes)
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="sequential", channel=channel, randomization_config=randomization_config)

        # Calculate proper alignment
        aligned_addr = sequence.align_address(start_addr, burst_size)

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
                                id_value: int = 0,
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence of transactions that test 4KB boundary cases.

        Args:
            channel: AXI4 channel ('AW' or 'AR')
            id_value: Transaction ID to use
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="4k_boundary_test", channel=channel, randomization_config=randomization_config)

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
                                    channel: str = "AW",
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence with various protection attribute combinations.

        Args:
            start_addr: Starting address
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="prot_variations", channel=channel, randomization_config=randomization_config)

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
                                channel: str = "AW",
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence with various cache attribute combinations.

        Args:
            start_addr: Starting address
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="cache_variations", channel=channel, randomization_config=randomization_config)

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
                            channel: str = "AW",
                            randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence with different QoS values.

        Args:
            start_addr: Starting address
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="qos_variations", channel=channel, randomization_config=randomization_config)

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
                                    channel: str = "AW",
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence of random but legal AXI4 transactions.

        Args:
            count: Number of transactions to generate
            addr_range: (min, max) address range
            id_range: (min, max) ID range
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        # If no randomization_config is provided, create a default one
        if randomization_config is None:
            from CocoTBFramework.components.randomization_config import (
                AXI4RandomizationConfig, RandomizationMode
            )
            randomization_config = AXI4RandomizationConfig()

            # Configure address range
            field_name = f"{channel.lower()}_addr"
            randomization_config.configure_field(
                field_name,
                mode=RandomizationMode.CONSTRAINED,
                constraints={
                    "bins": [addr_range],
                    "weights": [1.0]
                }
            )

            # Configure ID range
            field_name = f"{channel.lower()}_id"
            randomization_config.configure_field(
                field_name,
                mode=RandomizationMode.CONSTRAINED,
                constraints={
                    "bins": [id_range],
                    "weights": [1.0]
                }
            )

        sequence = cls(name="random_transactions", channel=channel,
                        randomization_config=randomization_config)

        for _ in range(count):
            # Generate random values
            ch_prefix = channel.lower()
            id_value = sequence.get_random_value(f"{ch_prefix}_id", id_range[0], id_range[1])
            burst_size = sequence.get_random_value(f"{ch_prefix}_size", 0, 3)  # 1, 2, 4, 8 bytes
            burst_type = sequence.get_random_value(f"{ch_prefix}_burst", 0, 2)

            # Generate random address within range and properly aligned
            addr = sequence.get_random_value(f"{ch_prefix}_addr", addr_range[0], addr_range[1])
            aligned_addr = sequence.align_address(addr, burst_size)

            # Determine burst length based on burst type
            if burst_type == cls.BURST_WRAP:
                # WRAP bursts need specific lengths
                wrap_len_options = [1, 3, 7, 15]  # 2, 4, 8, 16 transfers
                burst_len = sequence.get_random_value(f"{ch_prefix}_wrap_len", 0, len(wrap_len_options)-1)
                burst_len = wrap_len_options[burst_len]
            else:
                # For other types, any length up to 15 is fine for testing
                burst_len = sequence.get_random_value(f"{ch_prefix}_len", 0, 15)

            # Add the transaction
            sequence.add_transaction(
                addr=aligned_addr,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=burst_type,
                lock=sequence.get_random_value(f"{ch_prefix}_lock", 0, 1),
                cache=sequence.get_random_value(f"{ch_prefix}_cache", 0, 15),
                prot=sequence.get_random_value(f"{ch_prefix}_prot", 0, 7),
                qos=sequence.get_random_value(f"{ch_prefix}_qos", 0, 15)
            )

        return sequence

    @classmethod
    def create_comprehensive_test(cls, channel: str = "AW",
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a comprehensive test sequence combining various AXI4 address features.

        Args:
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence with a variety of transaction types
        """
        sequence = cls(name="comprehensive_test", channel=channel, randomization_config=randomization_config)

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

    @classmethod
    def create_incrementing_bursts(cls,
                                    start_addr: int = 0,
                                    count: int = 10,
                                    burst_len: int = 7,
                                    burst_size: int = 2,
                                    id_value: int = 0,
                                    channel: str = "AW",
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence of incrementing burst transactions.

        Args:
            start_addr: Starting address
            count: Number of transactions
            burst_len: Burst length (0 = 1 transfer, 7 = 8 transfers)
            burst_size: Burst size (log2 of number of bytes)
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="incr_bursts", channel=channel, randomization_config=randomization_config)

        # Calculate proper alignment
        aligned_addr = sequence.align_address(start_addr, burst_size)

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
                                channel: str = "AW",
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence of wrapping burst transactions.

        Args:
            start_addr: Starting address
            count: Number of transactions
            burst_lens: List of burst lengths to use (should be 2^n-1 for WRAP bursts)
            burst_size: Burst size (log2 of number of bytes)
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="wrap_bursts", channel=channel, randomization_config=randomization_config)

        # Calculate proper alignment
        aligned_addr = sequence.align_address(start_addr, burst_size)

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
                burst_len = sequence.next_power_of_two(burst_len + 1) - 1

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
                            channel: str = "AW",
                            randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence of fixed burst transactions.

        Args:
            addresses: List of addresses to use
            burst_len: Burst length (0 = 1 transfer, 7 = 8 transfers)
            burst_size: Burst size (log2 of number of bytes)
            id_value: Transaction ID to use
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="fixed_bursts", channel=channel, randomization_config=randomization_config)

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
    def create_varied_ids(cls, start_addr: int = 0, count: int = 10, id_values: List[int] = None, burst_size: int = 2, channel: str = "AW", randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence with varying transaction IDs.

        Args:
            start_addr: Starting address
            count: Number of transactions
            id_values: List of IDs to use
            burst_size: Burst size (log2 of number of bytes)
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        if id_values is None:
            id_values = [0, 1, 2, 3]
        sequence = cls(name="varied_ids", channel=channel, randomization_config=randomization_config)

        # Calculate proper alignment
        aligned_addr = sequence.align_address(start_addr, burst_size)

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
                                channel: str = "AR",
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4AddressSequence':
        """
        Create a sequence of exclusive access transactions.

        Args:
            addresses: List of addresses to use
            id_value: Transaction ID to use
            burst_size: Burst size (log2 of number of bytes)
            channel: AXI4 channel ('AW' or 'AR')
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4AddressSequence
        """
        sequence = cls(name="exclusive", channel=channel, randomization_config=randomization_config)

        # Add exclusive access for each address
        for addr in addresses:
            sequence.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_size=burst_size,
                burst_type=cls.BURST_INCR,  # INCR bursts
                lock=1  # Exclusive access
            )

        return sequence
