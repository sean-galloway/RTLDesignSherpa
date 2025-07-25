"""
MonBus Packet Class and Field Configuration

This module contains the MonbusPacket class and related field configuration
for handling monitor bus packets with complete type validation.
"""

import time
from typing import Optional, Any
from enum import IntEnum

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition

from .monbus_types import (
    ProtocolType, PktType, get_event_code_enum, get_event_code_name,
    is_valid_event_code
)


def create_monbus_field_config() -> FieldConfig:
    """Create field configuration for MonBus packets"""
    config = FieldConfig()

    # Monitor bus format: 64-bit total
    # [35:0]  data (36 bits)
    # [43:36] agent_id (8 bits)
    # [47:44] unit_id (4 bits)
    # [53:48] channel_id (6 bits)
    # [57:54] event_code (4 bits)
    # [59:58] protocol (2 bits)
    # [63:60] packet_type (4 bits)

    config.add_field(FieldDefinition(
        name="packet_type", bits=4, format="hex",
        description="Packet type (error, completion, etc.)",
        encoding={e.value: e.name for e in PktType}
    ))

    config.add_field(FieldDefinition(
        name="protocol", bits=2, format="hex",
        description="Protocol (AXI, NoC, APB, etc.)",
        encoding={e.value: e.name for e in ProtocolType}
    ))

    config.add_field(FieldDefinition(
        name="event_code", bits=4, format="hex",
        description="Event/error code"
    ))

    config.add_field(FieldDefinition(
        name="channel_id", bits=6, format="hex",
        description="Channel/transaction ID"
    ))

    config.add_field(FieldDefinition(
        name="unit_id", bits=4, format="hex",
        description="Unit identifier"
    ))

    config.add_field(FieldDefinition(
        name="agent_id", bits=8, format="hex",
        description="Agent identifier"
    ))

    config.add_field(FieldDefinition(
        name="data", bits=36, format="hex",
        description="Event data (address, metric, etc.)"
    ))

    # Verify total bits = 64
    total_bits = config.get_total_bits()
    if total_bits != 64:
        raise ValueError(f"MonBus field config must be exactly 64 bits, got {total_bits}")

    return config

class MonbusPacket:
    """
    Enhanced MonBus packet class with complete type validation
    """

    def __init__(self, gaxi_packet: GAXIPacket = None, **kwargs):
        """
        Create MonbusPacket from GAXIPacket using standard field access

        Args:
            gaxi_packet: Source GAXIPacket with fields already extracted by FieldConfig
            **kwargs: Direct field values (for manual creation)
        """
        self.timestamp = time.time()

        if gaxi_packet:
            # Use standard field access - FieldConfig already extracted these!
            self.data = getattr(gaxi_packet, 'data', 0)
            self.packet_type = getattr(gaxi_packet, 'packet_type', PktType.DEBUG.value)
            self.protocol = getattr(gaxi_packet, 'protocol', ProtocolType.APB.value)
            self.event_code = getattr(gaxi_packet, 'event_code', 0x1)
            self.channel_id = getattr(gaxi_packet, 'channel_id', 0)
            self.unit_id = getattr(gaxi_packet, 'unit_id', 0)
            self.agent_id = getattr(gaxi_packet, 'agent_id', 0)
        else:
            # Use provided kwargs
            self.data = kwargs.get('data', 0)
            self.packet_type = kwargs.get('packet_type', PktType.DEBUG.value)
            self.protocol = kwargs.get('protocol', ProtocolType.APB.value)
            self.event_code = kwargs.get('event_code', 0x1)
            self.channel_id = kwargs.get('channel_id', 0)
            self.unit_id = kwargs.get('unit_id', 0)
            self.agent_id = kwargs.get('agent_id', 0)

    # Packet type checks using enums
    def is_error_packet(self) -> bool:
        """Check if this is an error packet"""
        return self.packet_type == PktType.ERROR.value

    def is_completion_packet(self) -> bool:
        """Check if this is a completion packet"""
        return self.packet_type == PktType.COMPLETION.value

    def is_timeout_packet(self) -> bool:
        """Check if this is a timeout packet"""
        return self.packet_type == PktType.TIMEOUT.value

    def is_performance_packet(self) -> bool:
        """Check if this is a performance packet"""
        return self.packet_type == PktType.PERF.value

    def is_threshold_packet(self) -> bool:
        """Check if this is a threshold packet"""
        return self.packet_type == PktType.THRESHOLD.value

    def is_credit_packet(self) -> bool:
        """Check if this is a credit packet"""
        return self.packet_type == PktType.CREDIT.value

    def is_channel_packet(self) -> bool:
        """Check if this is a channel packet"""
        return self.packet_type == PktType.CHANNEL.value

    def is_stream_packet(self) -> bool:
        """Check if this is a stream packet"""
        return self.packet_type == PktType.STREAM.value

    def is_addr_match_packet(self) -> bool:
        """Check if this is an address match packet"""
        return self.packet_type == PktType.ADDR_MATCH.value

    def is_debug_packet(self) -> bool:
        """Check if this is a debug packet"""
        return self.packet_type == PktType.DEBUG.value

    # Protocol checks using enums
    def is_axi_protocol(self) -> bool:
        """Check if this is an AXI protocol packet"""
        return self.protocol == ProtocolType.AXI.value

    def is_noc_protocol(self) -> bool:
        """Check if this is a NOC protocol packet"""
        return self.protocol == ProtocolType.NOC.value

    def is_apb_protocol(self) -> bool:
        """Check if this is an APB protocol packet"""
        return self.protocol == ProtocolType.APB.value

    def is_custom_protocol(self) -> bool:
        """Check if this is a custom protocol packet"""
        return self.protocol == ProtocolType.CUSTOM.value

    # Enhanced name resolution using complete enum set
    def get_protocol_name(self) -> str:
        """Get human-readable protocol name"""
        try:
            return ProtocolType(self.protocol).name
        except ValueError:
            return f"UNKNOWN_PROTOCOL({self.protocol})"

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        try:
            return PktType(self.packet_type).name
        except ValueError:
            return f"UNKNOWN_PKT_TYPE({self.packet_type})"

    def get_event_code_name(self) -> str:
        """Get human-readable event code name using complete enum mapping"""
        return get_event_code_name(self.protocol, self.packet_type, self.event_code)

    def is_valid_event_code(self) -> bool:
        """Check if the event code is valid for this protocol/packet_type"""
        return is_valid_event_code(self.protocol, self.packet_type, self.event_code)

    def get_protocol_enum(self) -> Optional[ProtocolType]:
        """Get protocol as enum"""
        try:
            return ProtocolType(self.protocol)
        except ValueError:
            return None

    def get_packet_type_enum(self) -> Optional[PktType]:
        """Get packet type as enum"""
        try:
            return PktType(self.packet_type)
        except ValueError:
            return None

    def get_event_code_enum(self) -> Optional[IntEnum]:
        """Get event code as appropriate enum"""
        enum_class = get_event_code_enum(
            ProtocolType(self.protocol) if self.protocol in [e.value for e in ProtocolType] else None,
            PktType(self.packet_type) if self.packet_type in [e.value for e in PktType] else None
        )
        if enum_class:
            try:
                return enum_class(self.event_code)
            except ValueError:
                pass
        return None

    def to_dict(self) -> dict:
        """Convert packet to dictionary representation"""
        return {
            'data': self.data,
            'packet_type': self.packet_type,
            'protocol': self.protocol,
            'event_code': self.event_code,
            'channel_id': self.channel_id,
            'unit_id': self.unit_id,
            'agent_id': self.agent_id,
            'timestamp': self.timestamp,
            'protocol_name': self.get_protocol_name(),
            'packet_type_name': self.get_packet_type_name(),
            'event_code_name': self.get_event_code_name(),
            'valid_event_code': self.is_valid_event_code()
        }

    def matches(self, **criteria) -> bool:
        """
        Check if packet matches given criteria

        Args:
            **criteria: Field names and values to match

        Returns:
            True if all criteria match, False otherwise
        """
        for field, expected_value in criteria.items():
            if hasattr(self, field):
                actual_value = getattr(self, field)
                # Handle enum comparisons
                if hasattr(expected_value, 'value'):
                    expected_value = expected_value.value
                if actual_value != expected_value:
                    return False
            else:
                return False  # Field doesn't exist
        return True

    def __str__(self) -> str:
        """Enhanced string representation"""
        return (f"MonBus({self.get_protocol_name()}.{self.get_packet_type_name()}"
                f".{self.get_event_code_name()} ch={self.channel_id} "
                f"unit={self.unit_id} agent={self.agent_id} data=0x{self.data:X})")

    def __repr__(self) -> str:
        """Detailed representation for debugging"""
        return (f"MonbusPacket(protocol={self.get_protocol_name()}, "
                f"packet_type={self.get_packet_type_name()}, "
                f"event_code={self.get_event_code_name()}, "
                f"channel_id={self.channel_id}, unit_id={self.unit_id}, "
                f"agent_id={self.agent_id}, data=0x{self.data:X}, "
                f"valid_event={self.is_valid_event_code()})")

    def __eq__(self, other) -> bool:
        """Equality comparison"""
        if not isinstance(other, MonbusPacket):
            return False
        return (self.data == other.data and
                self.packet_type == other.packet_type and
                self.protocol == other.protocol and
                self.event_code == other.event_code and
                self.channel_id == other.channel_id and
                self.unit_id == other.unit_id and
                self.agent_id == other.agent_id)

    def __hash__(self) -> int:
        """Hash for use in sets/dicts"""
        return hash((self.data, self.packet_type, self.protocol,
                    self.event_code, self.channel_id, self.unit_id, self.agent_id))
