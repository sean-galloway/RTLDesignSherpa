# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MNOCPacket
# Purpose: Network Packet Class
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Network Packet Class

Extends the base Packet class with Network-specific functionality including
v2.0 chunk_enables support, payload type handling, and enhanced validation.

Features:
- Network v2.0 packet structure support
- Multiple payload types (CONFIG, TS, RDA, RAW)
- Enhanced chunk_enables validation and manipulation
- Automatic parity calculation
- EOS (End of Stream) tracking
- Transaction-level packet creation utilities

Usage:
    # Create structured packet
    packet = MNOCPacket(field_config)
    packet.addr = 5
    packet.payload_type = 1  # TS_PKT
    packet.chunk_enables = 0x00FF  # Chunks 0-7 valid
    packet.eos = False

    # Create raw packet
    raw_packet = MNOCPacket.create_raw_packet(channel=3, data=0x123456789ABCDEF)
"""

from typing import Optional, List, Dict, Any, Union
from ..shared.packet import Packet
from ..shared.field_config import FieldConfig
from ..shared.flex_randomizer import FlexRandomizer


class MNOCPacket(Packet):
    """
    Packet class for Network protocol with v2.0 enhancements.

    Extends base Packet class with Network-specific features including
    chunk_enables support, payload type validation, and parity calculation.
    """

    # Network v2.0 Packet Types
    PKT_TYPES = {
        'CONFIG_PKT': 0,    # Configuration packet for FC/RISC-V configuration
        'TS_PKT': 1,        # TruStream data packet for core communication
        'RDA_PKT': 2,       # RISC-V Direct Access packet for memory access
        'RAW_PKT': 3        # Raw 512-bit data packet
    }

    # Network ACK Types
    ACK_TYPES = {
        'MSAP_STOP': 0,         # Packet received by MSAP, increment credit by 1
        'MSAP_START': 1,        # Starts a channel and sets credit to 8
        'MSAP_CREDIT_ON': 2,    # Packet received by RAPIDS, increment credit by 1
        'MSAP_STOP_AT_EOS': 3   # Stop at end of stream
    }

    def __init__(self, field_config: Optional[FieldConfig] = None,
                master_randomizer: Optional[FlexRandomizer] = None,
                slave_randomizer: Optional[FlexRandomizer] = None, **kwargs):
        """
        Initialize an Network packet.

        Args:
            field_config: Field configuration (or dict that will be converted)
            master_randomizer: Optional randomizer for master interface timing
            slave_randomizer: Optional randomizer for slave interface timing
            **kwargs: Initial field values passed to parent
        """
        # Call parent constructor
        super().__init__(field_config, **kwargs)

        # Network-specific properties
        self.master_randomizer = master_randomizer
        self.slave_randomizer = slave_randomizer
        self.master_delay = None
        self.slave_delay = None

        # Enhanced packet tracking
        self.packet_id = None
        self.transaction_id = None
        self.timestamp = None

    def set_master_randomizer(self, randomizer: FlexRandomizer):
        """Set the master randomizer for timing control."""
        self.master_randomizer = randomizer
        self.master_delay = None  # Reset cached delay

    def set_slave_randomizer(self, randomizer: FlexRandomizer):
        """Set the slave randomizer for timing control."""
        self.slave_randomizer = randomizer
        self.slave_delay = None  # Reset cached delay

    def get_master_delay(self) -> int:
        """
        Get the delay for the master interface (valid delay).

        Returns:
            Delay in cycles (0 if no randomizer)
        """
        if self.master_delay is None and self.master_randomizer:
            self.master_delay = self.master_randomizer.choose_valid_delay()
        return self.master_delay or 0

    def get_slave_delay(self) -> int:
        """
        Get the delay for the slave interface (ready delay).

        Returns:
            Delay in cycles (0 if no randomizer)
        """
        if self.slave_delay is None and self.slave_randomizer:
            self.slave_delay = self.slave_randomizer.choose_ready_delay()
        return self.slave_delay or 0

    def get_payload_type(self) -> int:
        """Get the payload type value."""
        return getattr(self, 'payload_type', 0)

    def get_payload_type_name(self) -> str:
        """Get the payload type name string."""
        pkt_type = self.get_payload_type()
        for name, value in self.PKT_TYPES.items():
            if value == pkt_type:
                return name
        return f"UNKNOWN_{pkt_type}"

    def is_structured_packet(self) -> bool:
        """Check if this is a structured packet (not RAW)."""
        return self.get_payload_type() != self.PKT_TYPES['RAW_PKT']

    def is_raw_packet(self) -> bool:
        """Check if this is a RAW packet."""
        return self.get_payload_type() == self.PKT_TYPES['RAW_PKT']

    def get_channel(self) -> int:
        """Get the channel/address value."""
        return getattr(self, 'addr', 0)

    def get_eos(self) -> bool:
        """Get the End of Stream flag."""
        return bool(getattr(self, 'eos', False))

    def get_chunk_enables(self) -> int:
        """Get the v2.0 chunk_enables value."""
        return getattr(self, 'chunk_enables', 0xFFFF)

    def set_chunk_enables(self, chunk_enables: int):
        """Set the v2.0 chunk_enables value with validation."""
        if not self.validate_chunk_enables(chunk_enables):
            raise ValueError(f"Invalid chunk_enables value: 0x{chunk_enables:04X}")
        setattr(self, 'chunk_enables', chunk_enables)

    def get_chunk_count(self) -> int:
        """Get the number of valid chunks."""
        return bin(self.get_chunk_enables()).count('1')

    def get_valid_chunks(self) -> List[int]:
        """Get list of valid chunk indices (0-15)."""
        chunk_enables = self.get_chunk_enables()
        return [i for i in range(16) if chunk_enables & (1 << i)]

    def set_chunks_valid(self, chunk_indices: List[int]):
        """Set specific chunks as valid."""
        chunk_enables = 0
        for idx in chunk_indices:
            if 0 <= idx <= 15:
                chunk_enables |= (1 << idx)
        self.set_chunk_enables(chunk_enables)

    def is_chunk_valid(self, chunk_index: int) -> bool:
        """Check if specific chunk is valid."""
        if not (0 <= chunk_index <= 15):
            return False
        return bool(self.get_chunk_enables() & (1 << chunk_index))

    def validate_chunk_enables(self, chunk_enables: int) -> bool:
        """
        Validate chunk_enables according to Network v2.0 rules.

        Args:
            chunk_enables: 16-bit chunk enables value

        Returns:
            True if valid
        """
        # Must have at least one valid chunk
        if chunk_enables == 0:
            return False

        # Must be 16-bit value
        if chunk_enables < 0 or chunk_enables > 0xFFFF:
            return False

        # For structured packets, chunk 15 typically not used
        if self.is_structured_packet() and (chunk_enables & 0x8000):
            # This might be valid in some cases, so allow but could warn
            pass

        return True

    def get_data_fields(self) -> List[int]:
        """Get all data fields for structured packets."""
        if self.is_raw_packet():
            return [getattr(self, 'raw_data', 0)]

        data_fields = []
        for i in range(15):
            field_name = f'data_{i}'
            data_fields.append(getattr(self, field_name, 0))
        return data_fields

    def set_data_fields(self, data_values: List[int]):
        """Set data fields for structured packets."""
        if self.is_raw_packet():
            if len(data_values) > 0:
                setattr(self, 'raw_data', data_values[0])
            return

        # Set up to 15 data fields
        for i in range(15):
            field_name = f'data_{i}'
            value = data_values[i] if i < len(data_values) else 0
            setattr(self, field_name, value)

    def get_ctrl_flags(self) -> int:
        """Get control flags for structured packets."""
        return getattr(self, 'ctrl', 0) if self.is_structured_packet() else 0

    def set_ctrl_flags(self, ctrl_value: int):
        """Set control flags for structured packets."""
        if self.is_structured_packet():
            setattr(self, 'ctrl', ctrl_value & 0x7FFF)  # 15-bit mask

    def calculate_header_parity(self) -> int:
        """Calculate odd parity for header (address field)."""
        addr = self.get_channel()
        return bin(addr).count('1') % 2

    def calculate_payload_parity(self) -> int:
        """Calculate odd parity for payload."""
        if self.is_raw_packet():
            data = getattr(self, 'raw_data', 0)
            return bin(data).count('1') % 2
        else:
            # Calculate parity of all payload fields
            parity_bits = 0

            # Data fields
            for i in range(15):
                field_value = getattr(self, f'data_{i}', 0)
                parity_bits ^= bin(field_value).count('1')

            # Control flags
            ctrl = self.get_ctrl_flags()
            parity_bits ^= bin(ctrl).count('1')

            # Chunk enables
            chunk_enables = self.get_chunk_enables()
            parity_bits ^= bin(chunk_enables).count('1')

            # Reserved bit
            reserved = getattr(self, 'reserved', 0)
            parity_bits ^= bin(reserved).count('1')

            return parity_bits % 2

    def update_parity_fields(self):
        """Update parity fields based on current packet content."""
        if hasattr(self, 'header_par'):
            setattr(self, 'header_par', self.calculate_header_parity())
        if hasattr(self, 'payload_par'):
            setattr(self, 'payload_par', self.calculate_payload_parity())

    def validate_packet(self) -> Dict[str, Any]:
        """
        Validate packet according to Network v2.0 specification.

        Returns:
            Dictionary with validation results
        """
        errors = []
        warnings = []

        # Check payload type
        pkt_type = self.get_payload_type()
        if pkt_type not in self.PKT_TYPES.values():
            errors.append(f"Invalid payload type: {pkt_type}")

        # Check chunk_enables
        chunk_enables = self.get_chunk_enables()
        if not self.validate_chunk_enables(chunk_enables):
            errors.append(f"Invalid chunk_enables: 0x{chunk_enables:04X}")

        # Check channel range (assuming 8-bit address)
        channel = self.get_channel()
        if channel < 0 or channel > 255:
            errors.append(f"Channel out of range: {channel}")

        # Check parity if fields exist
        if hasattr(self, 'header_par'):
            expected_header_par = self.calculate_header_parity()
            actual_header_par = getattr(self, 'header_par', 0)
            if expected_header_par != actual_header_par:
                errors.append(f"Header parity mismatch: expected {expected_header_par}, got {actual_header_par}")

        if hasattr(self, 'payload_par'):
            expected_payload_par = self.calculate_payload_parity()
            actual_payload_par = getattr(self, 'payload_par', 0)
            if expected_payload_par != actual_payload_par:
                errors.append(f"Payload parity mismatch: expected {expected_payload_par}, got {actual_payload_par}")

        # Check for structured packet constraints
        if self.is_structured_packet():
            if chunk_enables & 0x8000:
                warnings.append("Chunk 15 set for structured packet (unusual)")

        return {
            'valid': len(errors) == 0,
            'errors': errors,
            'warnings': warnings,
            'packet_type': self.get_payload_type_name(),
            'channel': channel,
            'chunk_count': self.get_chunk_count()
        }

    @classmethod
    def create_config_packet(cls, channel: int, config_data: List[int],
                        chunk_enables: int = 0xFFFF, eos: bool = False,
                        field_config: Optional[FieldConfig] = None) -> 'MNOCPacket':
        """Create a CONFIG packet."""
        packet = cls(field_config)
        packet.addr = channel
        packet.payload_type = cls.PKT_TYPES['CONFIG_PKT']
        packet.set_data_fields(config_data)
        packet.set_chunk_enables(chunk_enables)
        packet.eos = eos
        packet.update_parity_fields()
        return packet

    @classmethod
    def create_ts_packet(cls, channel: int, ts_data: List[int],
                        chunk_enables: int = 0xFFFF, eos: bool = False,
                        field_config: Optional[FieldConfig] = None) -> 'MNOCPacket':
        """Create a TruStream packet."""
        packet = cls(field_config)
        packet.addr = channel
        packet.payload_type = cls.PKT_TYPES['TS_PKT']
        packet.set_data_fields(ts_data)
        packet.set_chunk_enables(chunk_enables)
        packet.eos = eos
        packet.update_parity_fields()
        return packet

    @classmethod
    def create_rda_packet(cls, channel: int, rda_data: List[int],
                        chunk_enables: int = 0xFFFF, eos: bool = False,
                        field_config: Optional[FieldConfig] = None) -> 'MNOCPacket':
        """Create an RDA packet."""
        packet = cls(field_config)
        packet.addr = channel
        packet.payload_type = cls.PKT_TYPES['RDA_PKT']
        packet.set_data_fields(rda_data)
        packet.set_chunk_enables(chunk_enables)
        packet.eos = eos
        packet.update_parity_fields()
        return packet

    @classmethod
    def create_raw_packet(cls, channel: int, raw_data: int, eos: bool = False,
                        field_config: Optional[FieldConfig] = None) -> 'MNOCPacket':
        """Create a RAW packet."""
        packet = cls(field_config)
        packet.addr = channel
        packet.payload_type = cls.PKT_TYPES['RAW_PKT']
        packet.raw_data = raw_data
        packet.eos = eos
        packet.update_parity_fields()
        return packet

    @classmethod
    def create_ack_packet(cls, channel: int, ack_type: str,
                        field_config: Optional[FieldConfig] = None) -> 'MNOCPacket':
        """Create an ACK packet."""
        if ack_type not in cls.ACK_TYPES:
            raise ValueError(f"Invalid ACK type: {ack_type}")

        packet = cls(field_config)
        packet.addr = channel
        packet.ack = cls.ACK_TYPES[ack_type]

        # Calculate ACK parity (odd parity of ack field)
        if hasattr(packet, 'ack_par'):
            packet.ack_par = bin(packet.ack).count('1') % 2

        packet.update_parity_fields()
        return packet

    def to_dict(self) -> Dict[str, Any]:
        """Convert packet to dictionary representation."""
        result = super().to_dict()

        # Add Network-specific metadata
        result.update({
            'network_packet_type': self.get_payload_type_name(),
            'network_channel': self.get_channel(),
            'network_eos': self.get_eos(),
            'network_chunk_enables': f"0x{self.get_chunk_enables():04X}",
            'network_chunk_count': self.get_chunk_count(),
            'network_valid_chunks': self.get_valid_chunks(),
            'network_is_structured': self.is_structured_packet(),
            'network_validation': self.validate_packet()
        })

        return result

    def __str__(self) -> str:
        """String representation of Network packet."""
        pkt_type = self.get_payload_type_name()
        channel = self.get_channel()
        eos_str = " [EOS]" if self.get_eos() else ""
        chunk_str = f"chunks=0x{self.get_chunk_enables():04X}({self.get_chunk_count()})"

        return f"MNOCPacket({pkt_type}, ch={channel}, {chunk_str}{eos_str})"

    def __repr__(self) -> str:
        """Detailed representation of Network packet."""
        return f"MNOCPacket(type={self.get_payload_type_name()}, channel={self.get_channel()}, " \
            f"eos={self.get_eos()}, chunk_enables=0x{self.get_chunk_enables():04X})"