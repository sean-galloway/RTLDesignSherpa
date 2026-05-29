#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MonbusPacket
# Purpose: MonBus packet (128-bit) implementation for cocotb tests
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
MonBus Packet Implementation — 128-bit format

Defines MonbusPacket class and field configuration for monitor bus packets.
Supports all protocol types including ARB and CORE with comprehensive validation.

128-bit field layout (mirrors monitor_common_pkg.sv):
  [127:124] pkt_type    4 bits
  [123:109] reserved   15 bits
  [108:105] protocol    4 bits
  [104: 97] event_code  8 bits
  [ 96: 88] channel_id  9 bits
  [ 87: 72] agent_id   16 bits
  [ 71: 64] unit_id     8 bits
  [ 63:  0] data       64 bits
"""

from typing import Dict, Any, Optional
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from .monbus_types import ProtocolType, PktType


def create_monbus_field_config() -> FieldConfig:
    """Create field configuration for MonBus packets (128-bit format)."""
    config = FieldConfig()

    # 128-bit MonBus packet layout (mirrors monitor_common_pkg.sv):
    # [127:124] - pkt_type    4 bits
    # [123:109] - reserved   15 bits
    # [108:105] - protocol    4 bits
    # [104: 97] - event_code  8 bits
    # [ 96: 88] - channel_id  9 bits
    # [ 87: 72] - agent_id   16 bits
    # [ 71: 64] - unit_id     8 bits
    # [ 63:  0] - data       64 bits

    config.add_field(FieldDefinition(name="pkt_type",   bits=4,  format="hex"))
    config.add_field(FieldDefinition(name="reserved",   bits=15, format="hex"))
    config.add_field(FieldDefinition(name="protocol",   bits=4,  format="hex"))
    config.add_field(FieldDefinition(name="event_code", bits=8,  format="hex"))
    config.add_field(FieldDefinition(name="channel_id", bits=9,  format="hex"))
    config.add_field(FieldDefinition(name="agent_id",   bits=16, format="hex"))
    config.add_field(FieldDefinition(name="unit_id",    bits=8,  format="hex"))
    config.add_field(FieldDefinition(name="data",       bits=64, format="hex"))

    return config


class MonbusPacket:
    """MonBus packet with comprehensive validation and formatting - UPDATED"""

    def __init__(self, gaxi_packet: GAXIPacket):
        """Initialize from GAXIPacket"""
        self._gaxi_packet = gaxi_packet
        self._field_config = create_monbus_field_config()
        self._validate_required_fields()

    def _validate_required_fields(self):
        """Ensure all required fields are present"""
        required_fields = ['pkt_type', 'protocol', 'event_code', 'channel_id',
                        'unit_id', 'agent_id', 'data']

        for field_name in required_fields:
            if not hasattr(self._gaxi_packet, field_name):
                raise ValueError(f"Missing required field: {field_name}")

    @property
    def pkt_type(self) -> int:
        """Packet type (4 bits)"""
        return getattr(self._gaxi_packet, 'pkt_type', 0)

    @property
    def protocol(self) -> int:
        """Protocol type (4 bits)"""
        return getattr(self._gaxi_packet, 'protocol', 0)

    @property
    def event_code(self) -> int:
        """Event code (8 bits)"""
        return getattr(self._gaxi_packet, 'event_code', 0)

    @property
    def channel_id(self) -> int:
        """Channel ID (9 bits)"""
        return getattr(self._gaxi_packet, 'channel_id', 0)

    @property
    def unit_id(self) -> int:
        """Unit ID (8 bits)"""
        return getattr(self._gaxi_packet, 'unit_id', 0)

    @property
    def agent_id(self) -> int:
        """Agent ID (16 bits)"""
        return getattr(self._gaxi_packet, 'agent_id', 0)

    @property
    def data(self) -> int:
        """Event data (64 bits)"""
        return getattr(self._gaxi_packet, 'data', 0)

    @property
    def timestamp(self) -> float:
        """Packet timestamp if available"""
        return getattr(self._gaxi_packet, 'timestamp', 0.0)

    def validate_fields(self) -> bool:
        """Validate all field values are within expected ranges (128-bit layout)."""
        try:
            if not (0 <= self.pkt_type <= 0xF):                # 4 bits
                return False
            if not (0 <= self.protocol <= 0xF):                # 4 bits
                return False
            if not (0 <= self.event_code <= 0xFF):             # 8 bits
                return False
            if not (0 <= self.channel_id <= 0x1FF):            # 9 bits
                return False
            if not (0 <= self.unit_id <= 0xFF):                # 8 bits
                return False
            if not (0 <= self.agent_id <= 0xFFFF):             # 16 bits
                return False
            if not (0 <= self.data <= ((1 << 64) - 1)):        # 64 bits
                return False

            return True
        except Exception:
            return False

    def is_error_packet(self) -> bool:
        """Check if this is an error packet"""
        return self.pkt_type == PktType.ERROR.value

    def is_timeout_packet(self) -> bool:
        """Check if this is a timeout packet"""
        return self.pkt_type == PktType.TIMEOUT.value

    def is_completion_packet(self) -> bool:
        """Check if this is a completion packet"""
        return self.pkt_type == PktType.COMPLETION.value

    def is_threshold_packet(self) -> bool:
        """Check if this is a threshold packet"""
        return self.pkt_type == PktType.THRESHOLD.value

    def is_perf_packet(self) -> bool:
        """Check if this is a performance packet"""
        return self.pkt_type == PktType.PERF.value

    def is_debug_packet(self) -> bool:
        """Check if this is a debug packet"""
        return self.pkt_type == PktType.DEBUG.value

    def is_axi_protocol(self) -> bool:
        """Check if this is an AXI protocol packet"""
        return self.protocol == ProtocolType.PROTOCOL_AXI.value

    def is_apb_protocol(self) -> bool:
        """Check if this is an APB protocol packet"""
        return self.protocol == ProtocolType.PROTOCOL_APB.value

    def is_axis_protocol(self) -> bool:
        """Check if this is an AXIS protocol packet"""
        return self.protocol == ProtocolType.PROTOCOL_AXIS.value

    def is_arb_protocol(self) -> bool:
        """Check if this is an ARB protocol packet"""
        return self.protocol == ProtocolType.PROTOCOL_ARB.value

    def is_core_protocol(self) -> bool:
        """Check if this is a CORE protocol packet - NEW"""
        return self.protocol == ProtocolType.PROTOCOL_CORE.value

    def get_protocol_name(self) -> str:
        """Get human-readable protocol name"""
        try:
            return ProtocolType(self.protocol).name
        except ValueError:
            return f"UNKNOWN_PROTOCOL_{self.protocol}"

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        try:
            return PktType(self.pkt_type).name
        except ValueError:
            return f"UNKNOWN_TYPE_{self.pkt_type}"

    def matches(self, **criteria) -> bool:
        """Check if packet matches given criteria"""
        for key, expected_value in criteria.items():
            if not hasattr(self, key):
                return False
            actual_value = getattr(self, key)
            if actual_value != expected_value:
                return False
        return True

    def to_dict(self) -> Dict[str, Any]:
        """Convert packet to dictionary"""
        return {
            'pkt_type': self.pkt_type,
            'protocol': self.protocol,
            'event_code': self.event_code,
            'channel_id': self.channel_id,
            'unit_id': self.unit_id,
            'agent_id': self.agent_id,
            'data': self.data,
            'timestamp': self.timestamp
        }

    def format_for_display(self) -> str:
        """Format packet for human-readable display (128-bit layout)"""
        protocol_name = self.get_protocol_name()
        pkt_type_name = self.get_packet_type_name()

        return (f"{protocol_name}_{pkt_type_name}("
                f"event_code=0x{self.event_code:02X}, "
                f"channel_id=0x{self.channel_id:03X}, "
                f"unit_id=0x{self.unit_id:02X}, "
                f"agent_id=0x{self.agent_id:04X}, "
                f"data=0x{self.data:016X})")

    def format_detailed(self) -> str:
        """Format packet with full details (128-bit layout)"""
        return (f"MonbusPacket(\n"
                f"  pkt_type=0x{self.pkt_type:X} ({self.get_packet_type_name()}),\n"
                f"  protocol=0x{self.protocol:X} ({self.get_protocol_name()}),\n"
                f"  event_code=0x{self.event_code:02X},\n"
                f"  channel_id=0x{self.channel_id:03X},\n"
                f"  unit_id=0x{self.unit_id:02X},\n"
                f"  agent_id=0x{self.agent_id:04X},\n"
                f"  data=0x{self.data:016X},\n"
                f"  timestamp={self.timestamp:.1f}ns\n"
                f")")

    def format_bit_breakdown(self) -> str:
        """Format packet showing bit field breakdown (128-bit layout)."""
        # Reconstruct 128-bit value for bit analysis
        raw_128bit = (
            ((self.pkt_type   & 0xF)    << 124) |  # [127:124]
            # bits [123:109] reserved — zero
            ((self.protocol   & 0xF)    << 105) |  # [108:105]
            ((self.event_code & 0xFF)   <<  97) |  # [104: 97]
            ((self.channel_id & 0x1FF)  <<  88) |  # [ 96: 88]
            ((self.agent_id   & 0xFFFF) <<  72) |  # [ 87: 72]
            ((self.unit_id    & 0xFF)   <<  64) |  # [ 71: 64]
            (self.data & ((1 << 64) - 1))           # [ 63:  0]
        )

        return (
            f"Raw Packet: 0x{raw_128bit:032X}\n"
            f"  [127:124] pkt_type   = 0x{self.pkt_type:X} ({self.get_packet_type_name()})\n"
            f"  [108:105] protocol   = 0x{self.protocol:X} ({self.get_protocol_name()})\n"
            f"  [104: 97] event_code = 0x{self.event_code:02X}\n"
            f"  [ 96: 88] channel_id = 0x{self.channel_id:03X}\n"
            f"  [ 87: 72] agent_id   = 0x{self.agent_id:04X}\n"
            f"  [ 71: 64] unit_id    = 0x{self.unit_id:02X}\n"
            f"  [ 63:  0] data       = 0x{self.data:016X}"
        )

    def __str__(self) -> str:
        """String representation"""
        return self.format_for_display()

    def __repr__(self) -> str:
        """Detailed string representation"""
        return self.format_detailed()

    def __eq__(self, other) -> bool:
        """Equality comparison"""
        if not isinstance(other, MonbusPacket):
            return False
        return self.to_dict() == other.to_dict()

    def __hash__(self) -> int:
        """Hash for use in sets/dicts"""
        return hash((self.pkt_type, self.protocol, self.event_code,
                    self.channel_id, self.unit_id, self.agent_id, self.data))


# =============================================================================
# UTILITY FUNCTIONS FOR PACKET CREATION AND VALIDATION
# =============================================================================

def create_arb_error_packet(error_code, channel_id: int = 0, unit_id: int = 0, 
                           agent_id: int = 0x10, data: int = 0) -> Dict[str, Any]:
    """Create ARB error packet fields for testing"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': error_code.value if hasattr(error_code, 'value') else error_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data & ((1 << 64) - 1)  # Clamp to 64 bits
    }


def create_arb_completion_packet(completion_code, channel_id: int = 0, unit_id: int = 0,
                               agent_id: int = 0x10, data: int = 0) -> Dict[str, Any]:
    """Create ARB completion packet fields for testing"""
    return {
        'pkt_type': PktType.COMPLETION.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': completion_code.value if hasattr(completion_code, 'value') else completion_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data & ((1 << 64) - 1)  # Clamp to 64 bits
    }


def create_arb_performance_packet(perf_code, channel_id: int = 0, unit_id: int = 0,
                                agent_id: int = 0x10, data: int = 0) -> Dict[str, Any]:
    """Create ARB performance packet fields for testing"""
    return {
        'pkt_type': PktType.PERF.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': perf_code.value if hasattr(perf_code, 'value') else perf_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data & ((1 << 64) - 1)  # Clamp to 64 bits
    }


def create_core_error_packet(error_code, channel_id: int = 0, unit_id: int = 1,  # ✅ NEW
                           agent_id: int = 0x20, data: int = 0) -> Dict[str, Any]:
    """Create CORE error packet fields for testing"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': ProtocolType.PROTOCOL_CORE.value,
        'event_code': error_code.value if hasattr(error_code, 'value') else error_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data & ((1 << 64) - 1)  # Clamp to 64 bits
    }


def validate_packet_field_ranges(packet: MonbusPacket) -> list:
    """Validate all packet fields are within ranges (128-bit packet layout)."""
    errors = []

    if packet.pkt_type   > 0xF:                  # 4 bits
        errors.append(f"pkt_type {packet.pkt_type} exceeds 4-bit range")
    if packet.protocol   > 0xF:                  # 4 bits
        errors.append(f"protocol {packet.protocol} exceeds 4-bit range")
    if packet.event_code > 0xFF:                 # 8 bits
        errors.append(f"event_code {packet.event_code} exceeds 8-bit range")
    if packet.channel_id > 0x1FF:                # 9 bits
        errors.append(f"channel_id {packet.channel_id} exceeds 9-bit range")
    if packet.unit_id    > 0xFF:                 # 8 bits
        errors.append(f"unit_id {packet.unit_id} exceeds 8-bit range")
    if packet.agent_id   > 0xFFFF:               # 16 bits
        errors.append(f"agent_id {packet.agent_id} exceeds 16-bit range")
    if packet.data       > ((1 << 64) - 1):      # 64 bits
        errors.append(f"data 0x{packet.data:X} exceeds 64-bit range")

    return errors


def analyze_packet_bit_usage(packet: MonbusPacket) -> Dict[str, Any]:
    """Analyze how packet uses the 128-bit format."""
    analysis = {
        'total_bits': 128,
        'field_breakdown': {
            'pkt_type'  : {'bits':  4, 'position': '[127:124]', 'value': packet.pkt_type},
            'protocol'  : {'bits':  4, 'position': '[108:105]', 'value': packet.protocol},
            'event_code': {'bits':  8, 'position': '[104: 97]', 'value': packet.event_code},
            'channel_id': {'bits':  9, 'position': '[ 96: 88]', 'value': packet.channel_id},
            'agent_id'  : {'bits': 16, 'position': '[ 87: 72]', 'value': packet.agent_id},
            'unit_id'   : {'bits':  8, 'position': '[ 71: 64]', 'value': packet.unit_id},
            'data'      : {'bits': 64, 'position': '[ 63:  0]', 'value': packet.data},
        },
        'utilization': {
            'protocol_utilization': f"{packet.protocol}/15 ({packet.protocol/15*100:.1f}%)",
            'data_utilization': f"0x{packet.data:X} / 0xFFFFFFFFFFFFFFFF ({packet.data/((1<<64)-1)*100:.1f}%)"
        },
        'validation': {
            'all_fields_valid': packet.validate_fields(),
            'field_range_errors': validate_packet_field_ranges(packet)
        }
    }

    return analysis