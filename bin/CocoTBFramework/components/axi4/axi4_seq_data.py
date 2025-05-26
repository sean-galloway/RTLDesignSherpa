"""
AXI4 Data Sequence

This module provides specialized sequence generators for AXI4 data channels (W/R).
It focuses on data pattern generation and strobe handling with proper AXI4 protocol compliance.
"""

from typing import List, Dict, Any, Optional, Tuple, Union
from collections import deque

from ..field_config import FieldConfig
from ..flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from .axi4_packet import AXI4Packet
from .axi4_fields_signals import (
    AXI4_W_FIELD_CONFIG,
    AXI4_R_FIELD_CONFIG
)
from .axi4_seq_base import AXI4BaseSequence
from ..randomization_config import RandomizationConfig, RandomizationMode


class AXI4DataSequence(AXI4BaseSequence):
    """
    AXI4 Data Sequence generator with protocol awareness.

    This class provides utilities for creating sequences of AXI4 data patterns
    that comply with the AXI4 protocol rules, including proper strobes and last signaling.
    """

    def __init__(self, name: str = "axi4_data",
                    channel: str = "W",
                    data_width: int = 32,
                    user_width: int = 1,
                    randomization_config: Optional[RandomizationConfig] = None):
        """
        Initialize the AXI4 Data Sequence.

        Args:
            name: Sequence name
            channel: AXI4 channel ('W' or 'R')
            data_width: Width of data field in bits
            user_width: Width of user field in bits
            randomization_config: Optional randomization configuration
        """
        super().__init__(name=name, randomization_config=randomization_config)

        self.channel = channel.upper()

        if self.channel not in ['W', 'R']:
            raise ValueError(f"Channel must be either 'W' or 'R', got '{channel}'")

        self.data_width = data_width
        self.user_width = user_width
        self.strb_width = data_width // 8  # Width of strobe field in bits

        # Select appropriate field config based on channel
        if self.channel == 'W':
            self.field_config = self._adjust_field_config(AXI4_W_FIELD_CONFIG)
        else:  # R
            self.field_config = self._adjust_field_config(AXI4_R_FIELD_CONFIG)

        # Initialize sequence data
        self.data_sequence = []
        self.strb_sequence = [] if self.channel == 'W' else None
        self.last_sequence = []
        self.user_sequence = []
        self.resp_sequence = [] if self.channel == 'R' else None
        self.id_sequence = [] if self.channel == 'R' else None

        # Calculated properties
        self.data_mask = (1 << data_width) - 1
        self.strb_mask = (1 << self.strb_width) - 1

        # Randomization options
        self.use_random_selection = False

        # Generated packets
        self.packets = deque()

        # Iterators for sequences
        self.data_iter = None
        self.strb_iter = None
        self.last_iter = None
        self.user_iter = None
        self.resp_iter = None
        self.id_iter = None

        # Statistics
        self.stats.update({
            'burst_count': 0,
            'max_burst_length': 0
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

        # Update data width
        if self.channel == 'W':
            if adjusted_config.has_field('wdata'):
                adjusted_config.update_field_width('wdata', self.data_width)
            if adjusted_config.has_field('wstrb'):
                adjusted_config.update_field_width('wstrb', self.strb_width)
            if adjusted_config.has_field('wuser'):
                adjusted_config.update_field_width('wuser', self.user_width)
        else:  # R
            if adjusted_config.has_field('rdata'):
                adjusted_config.update_field_width('rdata', self.data_width)
            if adjusted_config.has_field('rid'):
                # Default ID width is 8, we don't change it here
                pass
            if adjusted_config.has_field('ruser'):
                adjusted_config.update_field_width('ruser', self.user_width)

        return adjusted_config

    def add_transaction(self,
                        data: int,
                        strb: Optional[int] = None,
                        last: int = 0,
                        user: int = 0,
                        id_value: Optional[int] = None,
                        resp: Optional[int] = None) -> 'AXI4DataSequence':
        """
        Add a data transaction to the sequence.

        Args:
            data: Data value
            strb: Write strobe (for W channel)
            last: Last indicator (1 = last transfer in burst)
            user: User signal
            id_value: Transaction ID (for R channel)
            resp: Response code (for R channel)

        Returns:
            Self for method chaining
        """
        # Validate and mask data to fit the data width
        masked_data = data & self.data_mask

        # Add data
        self.data_sequence.append(masked_data)

        # Add strobe (W channel only)
        if self.channel == 'W':
            # Default to all bytes enabled if not specified
            if strb is None:
                strb = self.strb_mask
            else:
                strb = strb & self.strb_mask
            self.strb_sequence.append(strb)

        # Add last indicator
        self.last_sequence.append(1 if last else 0)

        # Add user signal
        self.user_sequence.append(user & ((1 << self.user_width) - 1))

        # Add R channel specific fields
        if self.channel == 'R':
            if id_value is not None:
                self.id_sequence.append(id_value)
            else:
                self.id_sequence.append(0)  # Default ID

            if resp is not None:
                self.resp_sequence.append(resp)
            else:
                self.resp_sequence.append(0)  # Default response (OKAY)

        # Update statistics
        self.stats['total_transactions'] += 1

        # Update burst statistics
        if last:
            self.stats['burst_count'] += 1
            current_burst_length = 1
            # Count backwards to find start of burst
            for i in range(len(self.last_sequence) - 2, -1, -1):
                if self.last_sequence[i] == 1:
                    break
                current_burst_length += 1

            if current_burst_length > self.stats['max_burst_length']:
                self.stats['max_burst_length'] = current_burst_length

        return self

    def add_burst(self,
                    data_values: List[int],
                    strb_values: Optional[List[int]] = None,
                    user_values: Optional[List[int]] = None,
                    id_value: Optional[int] = None,
                    resp_value: Optional[int] = None) -> 'AXI4DataSequence':
        """
        Add a complete burst of data transactions.

        Args:
            data_values: List of data values for the burst
            strb_values: List of strobe values (W channel only)
            user_values: List of user values
            id_value: Transaction ID (R channel only)
            resp_value: Response code (R channel only)

        Returns:
            Self for method chaining
        """
        if not data_values:
            return self

        # Handle default strobes (W channel only)
        if self.channel == 'W' and strb_values is None:
            # Default to all bytes enabled
            strb_values = [self.strb_mask] * len(data_values)
        elif self.channel == 'W' and len(strb_values) < len(data_values):
            # Pad with full strobes if list is too short
            strb_values = strb_values + [self.strb_mask] * (len(data_values) - len(strb_values))

        # Handle default user values
        if user_values is None:
            user_values = [0] * len(data_values)
        elif len(user_values) < len(data_values):
            # Pad with zeros if list is too short
            user_values = user_values + [0] * (len(data_values) - len(user_values))

        # Add each transaction in the burst
        for i, data in enumerate(data_values):
            # Last transaction gets last=1
            is_last = (i == len(data_values) - 1)

            # Add the transaction
            if self.channel == 'W':
                self.add_transaction(
                    data=data,
                    strb=strb_values[i] if strb_values else None,
                    last=is_last,
                    user=user_values[i] if user_values else 0
                )
            else:  # R
                self.add_transaction(
                    data=data,
                    last=is_last,
                    user=user_values[i] if user_values else 0,
                    id_value=id_value,
                    resp=resp_value
                )

        return self

    def set_random_selection(self, enable: bool = True) -> 'AXI4DataSequence':
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
        self.data_iter = iter(self.data_sequence)

        if self.channel == 'W' and self.strb_sequence:
            self.strb_iter = iter(self.strb_sequence)

        self.last_iter = iter(self.last_sequence)
        self.user_iter = iter(self.user_sequence)

        if self.channel == 'R':
            if self.resp_sequence:
                self.resp_iter = iter(self.resp_sequence)
            if self.id_sequence:
                self.id_iter = iter(self.id_sequence)

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
        if sequence is self.data_sequence:
            return "data"
        elif sequence is self.strb_sequence:
            return "strb"
        elif sequence is self.last_sequence:
            return "last"
        elif sequence is self.user_sequence:
            return "user"
        elif sequence is self.resp_sequence:
            return "resp"
        elif sequence is self.id_sequence:
            return "id"
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
        Generate the next data packet in the sequence.

        Returns:
            AXI4 data packet (W or R)
        """
        # Get field values from sequences
        data = self._next_value(self.data_sequence, self.data_iter)
        last = self._next_value(self.last_sequence, self.last_iter)
        user = self._next_value(self.user_sequence, self.user_iter)

        # Create appropriate packet type
        if self.channel == 'W':
            strb = self._next_value(self.strb_sequence, self.strb_iter) if self.strb_sequence else self.strb_mask

            return AXI4Packet.create_w_packet(
                wdata=data, wstrb=strb, wlast=last, wuser=user
            )
        else:  # R
            id_value = self._next_value(self.id_sequence, self.id_iter) if self.id_sequence else 0
            resp = self._next_value(self.resp_sequence, self.resp_iter) if self.resp_sequence else 0

            return AXI4Packet.create_r_packet(
                rid=id_value, rdata=data, rresp=resp, rlast=last, ruser=user
            )

    def generate_packets(self, count: Optional[int] = None) -> List[AXI4Packet]:
        """
        Generate multiple data packets.

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
            if self.data_sequence:
                count = len(self.data_sequence)
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
        self.data_sequence.clear()
        if self.strb_sequence:
            self.strb_sequence.clear()
        self.last_sequence.clear()
        self.user_sequence.clear()
        if self.resp_sequence:
            self.resp_sequence.clear()
        if self.id_sequence:
            self.id_sequence.clear()

        # Clear packet queue
        self.packets.clear()

        # Clear iterators
        self.data_iter = None
        self.strb_iter = None
        self.last_iter = None
        self.user_iter = None
        self.resp_iter = None
        self.id_iter = None

        # Call base class cleanup
        super().cleanup()

    # ========================================================================
    # Data Pattern Generation Methods
    # ========================================================================

    def add_incrementing_data(self,
                                count: int = 10,
                                start_value: int = 0,
                                increment: int = 1,
                                id_value: Optional[int] = None,
                                all_last: bool = False) -> 'AXI4DataSequence':
        """
        Add a sequence of incrementing data values.

        Args:
            count: Number of data values
            start_value: Initial value
            increment: Value to add for each step
            id_value: Transaction ID (R channel only)
            all_last: If False, only the final value has last=1;
                        if True, every value has last=1

        Returns:
            Self for method chaining
        """
        for i in range(count):
            value = start_value + (i * increment)
            is_last = all_last or (i == count - 1)

            if self.channel == 'W':
                self.add_transaction(
                    data=value,
                    last=is_last
                )
            else:  # R
                self.add_transaction(
                    data=value,
                    last=is_last,
                    id_value=id_value
                )

        return self

    def add_pattern_data(self,
                        patterns: List[int],
                        repeat: int = 1,
                        id_value: Optional[int] = None,
                        all_last: bool = False) -> 'AXI4DataSequence':
        """
        Add a sequence of specific data patterns.

        Args:
            patterns: List of data values to use
            repeat: Number of times to repeat the pattern list
            id_value: Transaction ID (R channel only)
            all_last: If False, only the final value has last=1;
                        if True, every value has last=1

        Returns:
            Self for method chaining
        """
        if not patterns:
            return self

        total_count = len(patterns) * repeat

        for i in range(total_count):
            pattern_index = i % len(patterns)
            value = patterns[pattern_index]
            is_last = all_last or (i == total_count - 1)

            if self.channel == 'W':
                self.add_transaction(
                    data=value,
                    last=is_last
                )
            else:  # R
                self.add_transaction(
                    data=value,
                    last=is_last,
                    id_value=id_value
                )

        return self

    def add_walking_ones(self,
                        count: Optional[int] = None,
                        id_value: Optional[int] = None) -> 'AXI4DataSequence':
        """
        Add a walking ones pattern (0x00000001, 0x00000002, 0x00000004, ...).

        Args:
            count: Number of bit positions to walk through, defaults to data width
            id_value: Transaction ID (R channel only)

        Returns:
            Self for method chaining
        """
        if count is None:
            count = self.data_width
        else:
            count = min(count, self.data_width)

        for i in range(count):
            value = 1 << i
            is_last = (i == count - 1)

            if self.channel == 'W':
                self.add_transaction(
                    data=value,
                    last=is_last
                )
            else:  # R
                self.add_transaction(
                    data=value,
                    last=is_last,
                    id_value=id_value
                )

        return self

    def add_walking_zeros(self,
                            count: Optional[int] = None,
                            id_value: Optional[int] = None) -> 'AXI4DataSequence':
        """
        Add a walking zeros pattern (all 1s except for a single 0 bit that moves).

        Args:
            count: Number of bit positions to walk through, defaults to data width
            id_value: Transaction ID (R channel only)

        Returns:
            Self for method chaining
        """
        if count is None:
            count = self.data_width
        else:
            count = min(count, self.data_width)

        all_ones = (1 << self.data_width) - 1

        for i in range(count):
            value = all_ones & ~(1 << i)
            is_last = (i == count - 1)

            if self.channel == 'W':
                self.add_transaction(
                    data=value,
                    last=is_last
                )
            else:  # R
                self.add_transaction(
                    data=value,
                    last=is_last,
                    id_value=id_value
                )

        return self

    def add_alternating_patterns(self, id_value: Optional[int] = None) -> 'AXI4DataSequence':
        """
        Add common bit pattern tests (checkerboard, stripes, etc.).

        Args:
            id_value: Transaction ID (R channel only)

        Returns:
            Self for method chaining
        """
        # Generate alternating patterns
        patterns = [
            0x55555555 & self.data_mask,  # 0101...
            0xAAAAAAAA & self.data_mask,  # 1010...
            0x33333333 & self.data_mask,  # 0011...
            0xCCCCCCCC & self.data_mask,  # 1100...
            0x0F0F0F0F & self.data_mask,  # 00001111...
            0xF0F0F0F0 & self.data_mask,  # 11110000...
            0x00FF00FF & self.data_mask,  # Alternating bytes
            0xFF00FF00 & self.data_mask,  # Alternating bytes
            0x0000FFFF & self.data_mask,  # Half and half
            0xFFFF0000 & self.data_mask   # Half and half
        ]

        # Add each pattern
        return self.add_pattern_data(patterns, id_value=id_value)

    def add_random_data(self,
                        count: int = 10,
                        id_value: Optional[int] = None,
                        all_last: bool = False) -> 'AXI4DataSequence':
        """
        Add random data values.

        Args:
            count: Number of random values to generate
            id_value: Transaction ID (R channel only)
            all_last: If False, only the final value has last=1;
                        if True, every value has last=1

        Returns:
            Self for method chaining
        """
        for i in range(count):
            ch_prefix = self.channel.lower()
            value = self.get_random_value(f"{ch_prefix}_data", 0, self.data_mask)
            is_last = all_last or (i == count - 1)

            if self.channel == 'W':
                self.add_transaction(
                    data=value,
                    last=is_last
                )
            else:  # R
                self.add_transaction(
                    data=value,
                    last=is_last,
                    id_value=id_value
                )

        return self

    def add_error_responses(self,
                            data_values: List[int],
                            error_indices: List[int],
                            id_value: Optional[int] = None) -> 'AXI4DataSequence':
        """
        Add R channel data with specific error responses.
        Only applicable for R channel.

        Args:
            data_values: List of data values
            error_indices: Indices where response should be an error
            id_value: Transaction ID

        Returns:
            Self for method chaining
        """
        if self.channel != 'R':
            raise ValueError("Error responses are only applicable for R channel")

        for i, data in enumerate(data_values):
            is_last = (i == len(data_values) - 1)

            # Determine response code
            # 0 = OKAY, 1 = EXOKAY, 2 = SLVERR, 3 = DECERR
            resp = 0  # Default to OKAY
            if i in error_indices:
                resp = 2  # SLVERR

            self.add_transaction(
                data=data,
                last=is_last,
                id_value=id_value,
                resp=resp
            )

        return self

    def add_varied_strobes(self,
                            data_values: List[int],
                            strobe_patterns: Optional[List[int]] = None) -> 'AXI4DataSequence':
        """
        Add W channel data with varied strobe patterns.
        Only applicable for W channel.

        Args:
            data_values: List of data values
            strobe_patterns: List of strobe patterns to use

        Returns:
            Self for method chaining
        """
        if self.channel != 'W':
            raise ValueError("Strobe patterns are only applicable for W channel")

        # Default strobe patterns if not provided
        if strobe_patterns is None:
            # Generate standard strobe patterns based on strobe width
            strobe_patterns = []

            # All bytes enabled
            strobe_patterns.append((1 << self.strb_width) - 1)

            # Single bytes enabled (1-hot)
            strobe_patterns.extend(1 << i for i in range(self.strb_width))
            strobe_patterns.extend((0x55 & self.strb_mask, 0xAA & self.strb_mask))
            # High half / low half
            if self.strb_width > 1:
                strobe_patterns.extend(
                    (
                        (1 << (self.strb_width // 2)) - 1,
                        ((1 << (self.strb_width // 2)) - 1)
                        << (self.strb_width // 2),
                    )
                )
        # Add data with varied strobes
        for i, data in enumerate(data_values):
            is_last = (i == len(data_values) - 1)
            strb = strobe_patterns[i % len(strobe_patterns)]

            self.add_transaction(
                data=data,
                strb=strb,
                last=is_last
            )

        return self

    # ========================================================================
    # Factory Methods for Common Patterns
    # ========================================================================

    @classmethod
    def create_write_data(cls,
                        data_values: List[int],
                        data_width: int = 32,
                        randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a simple write data sequence.

        Args:
            data_values: List of data values
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence
        """
        sequence = cls(name="write_data", channel='W', data_width=data_width,
                        randomization_config=randomization_config)

        # Last data value will have wlast=1
        for i, data in enumerate(data_values):
            is_last = (i == len(data_values) - 1)
            sequence.add_transaction(data=data, last=is_last)

        return sequence

    @classmethod
    def create_read_data(cls,
                        data_values: List[int],
                        id_value: int = 0,
                        data_width: int = 32,
                        randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a simple read data sequence.

        Args:
            data_values: List of data values
            id_value: Transaction ID
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence
        """
        sequence = cls(name="read_data", channel='R', data_width=data_width,
                        randomization_config=randomization_config)

        # Last data value will have rlast=1
        for i, data in enumerate(data_values):
            is_last = (i == len(data_values) - 1)
            sequence.add_transaction(data=data, last=is_last, id_value=id_value)

        return sequence

    @classmethod
    def create_incremental_data(cls,
                                start_value: int = 0,
                                count: int = 10,
                                increment: int = 1,
                                channel: str = 'W',
                                id_value: Optional[int] = None,
                                data_width: int = 32,
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a sequence with incrementing data values.

        Args:
            start_value: Initial value
            count: Number of data values
            increment: Value to add for each step
            channel: AXI4 channel ('W' or 'R')
            id_value: Transaction ID (R channel only)
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence
        """
        sequence = cls(name="incremental_data", channel=channel, data_width=data_width,
                        randomization_config=randomization_config)
        sequence.add_incrementing_data(count, start_value, increment, id_value)
        return sequence

    @classmethod
    def create_pattern_test(cls,
                            channel: str = 'W',
                            id_value: Optional[int] = None,
                            data_width: int = 32,
                            randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a sequence with various data patterns for testing.

        Args:
            channel: AXI4 channel ('W' or 'R')
            id_value: Transaction ID (R channel only)
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence with test patterns
        """
        sequence = cls(name="pattern_test", channel=channel, data_width=data_width,
                        randomization_config=randomization_config)

        # Add constant patterns
        sequence.add_pattern_data([0x00000000, 0xFFFFFFFF], repeat=2, id_value=id_value)

        # Add walking patterns
        sequence.add_walking_ones(id_value=id_value)
        sequence.add_walking_zeros(id_value=id_value)

        # Add alternating patterns
        sequence.add_alternating_patterns(id_value=id_value)

        # Add random data
        sequence.add_random_data(10, id_value=id_value)

        return sequence

    @classmethod
    def create_strobe_test(cls,
                            data_width: int = 32,
                            randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a write sequence with various strobe patterns.

        Args:
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence with strobe tests
        """
        sequence = cls(name="strobe_test", channel='W', data_width=data_width,
                        randomization_config=randomization_config)
        strb_width = data_width // 8

        # Create test data patterns
        data_patterns = [
            0xFFFFFFFF,  # All ones
            0x55555555,  # Alternating bits
            0xAAAAAAAA,  # Alternating bits (inverted)
            0x00FF00FF   # Alternating bytes
        ]

        # Create common strobe patterns
        strobe_patterns = [(1 << strb_width) - 1]

        # Single byte patterns (one-hot)
        strobe_patterns.extend(1 << i for i in range(strb_width))
        # Alternating bytes
        strobe_patterns.append(0x55 & ((1 << strb_width) - 1))
        strobe_patterns.append(0xAA & ((1 << strb_width) - 1))

        # High/low halves
        if strb_width >= 2:
            strobe_patterns.append((1 << (strb_width // 2)) - 1)
            strobe_patterns.append(((1 << (strb_width // 2)) - 1) << (strb_width // 2))

        # Add data with varied strobes
        sequence.add_varied_strobes(data_patterns * 2, strobe_patterns)

        return sequence

    @classmethod
    def create_error_response_test(cls,
                                    id_value: int = 0,
                                    data_width: int = 32,
                                    randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a read sequence with various error responses.

        Args:
            id_value: Transaction ID
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence with error responses
        """
        sequence = cls(name="error_response_test", channel='R', data_width=data_width,
                        randomization_config=randomization_config)

        # Create some test data
        data_values = [i * 0x100 + 0xFF for i in range(10)]

        # Set specific indices to return errors
        error_indices = [2, 5, 8]

        sequence.add_error_responses(data_values, error_indices, id_value)

        return sequence

    @classmethod
    def create_burst_test(cls,
                        burst_lengths: List[int],
                        channel: str = 'W',
                        id_value: Optional[int] = None,
                        data_width: int = 32,
                        randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a sequence with multiple bursts of different lengths.

        Args:
            burst_lengths: List of burst lengths to test
            channel: AXI4 channel ('W' or 'R')
            id_value: Transaction ID (R channel only)
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence with multiple bursts
        """
        sequence = cls(name="burst_test", channel=channel, data_width=data_width,
                        randomization_config=randomization_config)

        # Generate data for each burst
        start_value = 0

        for burst_len in burst_lengths:
            # Generate data values for this burst
            data_values = [start_value + i for i in range(burst_len)]

            # Increment start value for next burst
            start_value += burst_len + 0x100

            # Add the burst
            if channel == 'W':
                sequence.add_burst(data_values)
            else:  # R
                sequence.add_burst(data_values, id_value=id_value)

        return sequence

    @classmethod
    def create_comprehensive_test(cls,
                                channel: str = 'W',
                                data_width: int = 32,
                                randomization_config: Optional[RandomizationConfig] = None) -> 'AXI4DataSequence':
        """
        Create a comprehensive test sequence with multiple data patterns.

        Args:
            channel: AXI4 channel ('W' or 'R')
            data_width: Width of data in bits
            randomization_config: Optional randomization configuration

        Returns:
            Configured AXI4DataSequence with comprehensive tests
        """
        sequence = cls(name="comprehensive_test", channel=channel, data_width=data_width,
                        randomization_config=randomization_config)

        # For R channel, use multiple IDs
        id_values = [0, 1, 2, 3] if channel == 'R' else [None]

        for id_value in id_values:
            if channel == 'R':
                # Only use the ID for R channel
                current_id = id_value
            else:
                current_id = None

            # Add basic patterns
            sequence.add_pattern_data([0x00000000, 0xFFFFFFFF], id_value=current_id)

            # Add incrementing data
            start_val = id_value * 0x1000 if channel == 'R' else 0
            sequence.add_incrementing_data(5, start_val, 1, current_id)

            # Add walking patterns (partial to keep sequence manageable)
            sequence.add_walking_ones(8, current_id)
            sequence.add_walking_zeros(8, current_id)

            # Add alternating patterns
            sequence.add_pattern_data([
                0x55555555 & ((1 << data_width) - 1),
                0xAAAAAAAA & ((1 << data_width) - 1)
            ], id_value=current_id)

            # Add random data
            sequence.add_random_data(5, id_value=current_id)

        # For W channel, add strobe variations
        if channel == 'W':
            # Create some strobe patterns
            strb_width = data_width // 8
            strobe_patterns = [
                (1 << strb_width) - 1,  # All bytes enabled
                0x55 & ((1 << strb_width) - 1),  # Alternating bytes
                0xAA & ((1 << strb_width) - 1)   # Alternating bytes (inverted)
            ]

            sequence.add_varied_strobes([0xDEADBEEF, 0xCAFEBABE, 0x12345678], strobe_patterns)

        # For R channel, add error responses
        if channel == 'R':
            data_values = [0xA0000000 + i for i in range(5)]
            error_indices = [1, 3]
            sequence.add_error_responses(data_values, error_indices, id_value=3)

        return sequence
