#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MonbusPacket
# Purpose: MonBus Packet Implementation - UPDATED FOR 3-BIT PROTOCOL FIELD
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
MonBus Packet Implementation - UPDATED FOR 3-BIT PROTOCOL FIELD

Defines MonbusPacket class and field configuration for monitor bus packets.
Supports all protocol types including ARB and CORE with comprehensive validation.

UPDATED FOR NEW MONITOR PACKAGE:
- Protocol field INCREASED to 3 bits [59:57] (was 2 bits)
- Event code at [56:53] (4 bits) 
- Channel ID at [52:47] (6 bits)
- Unit ID at [46:43] (4 bits)
- Agent ID at [42:35] (8 bits)
- Event data REDUCED to 35 bits [34:0] (was 36 bits)
- Added CORE protocol support
"""

from typing import Dict, Any, Optional
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from .monbus_types import ProtocolType, PktType


def create_monbus_field_config() -> FieldConfig:
    """Create field configuration for MonBus packets - UPDATED FOR NEW FORMAT"""
    config = FieldConfig()

    # MonBus packet format (64-bit total) - UPDATED:
    # [63:60] - pkt_type: 4 bits (error, timeout, completion, etc.)
    # [59:57] - protocol: 3 bits (AXI/AXIS/APB/ARB/CORE) ✅ UPDATED: 3 bits
    # [56:53] - event_code: 4 bits (specific error or event code) ✅ UPDATED position
    # [52:47] - channel_id: 6 bits (channel ID and AXI ID)
    # [46:43] - unit_id: 4 bits (subsystem identifier)
    # [42:35] - agent_id: 8 bits (module identifier)
    # [34:0]  - data: 35 bits (event-specific data) ✅ UPDATED: 35 bits

    config.add_field(FieldDefinition(name="pkt_type",   bits=4,  format="hex")) # 63-60
    config.add_field(FieldDefinition(name="protocol",   bits=3,  format="hex")) # 59-57 ✅ UPDATED: 3 bits
    config.add_field(FieldDefinition(name="event_code", bits=4,  format="hex")) # 56-53 ✅ UPDATED position
    config.add_field(FieldDefinition(name="channel_id", bits=6,  format="hex")) # 52-47
    config.add_field(FieldDefinition(name="unit_id",    bits=4,  format="hex")) # 46-43
    config.add_field(FieldDefinition(name="agent_id",   bits=8,  format="hex")) # 42-35
    config.add_field(FieldDefinition(name="data",       bits=35, format="hex")) # 34-0 ✅ UPDATED: 35 bits

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
        """Protocol type (3 bits) - UPDATED"""
        return getattr(self._gaxi_packet, 'protocol', 0)

    @property
    def event_code(self) -> int:
        """Event code (4 bits)"""
        return getattr(self._gaxi_packet, 'event_code', 0)

    @property
    def channel_id(self) -> int:
        """Channel ID (6 bits)"""
        return getattr(self._gaxi_packet, 'channel_id', 0)

    @property
    def unit_id(self) -> int:
        """Unit ID (4 bits)"""
        return getattr(self._gaxi_packet, 'unit_id', 0)

    @property
    def agent_id(self) -> int:
        """Agent ID (8 bits)"""
        return getattr(self._gaxi_packet, 'agent_id', 0)

    @property
    def data(self) -> int:
        """Event data (35 bits) - UPDATED"""
        return getattr(self._gaxi_packet, 'data', 0)

    @property
    def timestamp(self) -> float:
        """Packet timestamp if available"""
        return getattr(self._gaxi_packet, 'timestamp', 0.0)

    def validate_fields(self) -> bool:
        """Validate all field values are within expected ranges - UPDATED"""
        try:
            # Check field ranges - UPDATED
            if not (0 <= self.pkt_type <= 15):  # 4 bits
                return False
            if not (0 <= self.protocol <= 7):   # 3 bits ✅ UPDATED: 0-7 range
                return False
            if not (0 <= self.event_code <= 15): # 4 bits
                return False
            if not (0 <= self.channel_id <= 63): # 6 bits
                return False
            if not (0 <= self.unit_id <= 15):   # 4 bits
                return False
            if not (0 <= self.agent_id <= 255): # 8 bits
                return False
            if not (0 <= self.data <= 0x7FFFFFFFF): # 35 bits ✅ UPDATED: 35-bit max
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
        """Format packet for human-readable display"""
        protocol_name = self.get_protocol_name()
        pkt_type_name = self.get_packet_type_name()

        return (f"{protocol_name}_{pkt_type_name}("
                f"event_code=0x{self.event_code:X}, "
                f"channel_id=0x{self.channel_id:02X}, "
                f"unit_id=0x{self.unit_id:X}, "
                f"agent_id=0x{self.agent_id:02X}, "
                f"data=0x{self.data:09X})")

    def format_detailed(self) -> str:
        """Format packet with full details"""
        return (f"MonbusPacket(\n"
                f"  pkt_type=0x{self.pkt_type:X} ({self.get_packet_type_name()}),\n"
                f"  protocol=0x{self.protocol:X} ({self.get_protocol_name()}),\n"
                f"  event_code=0x{self.event_code:X},\n"
                f"  channel_id=0x{self.channel_id:02X},\n"
                f"  unit_id=0x{self.unit_id:X},\n"
                f"  agent_id=0x{self.agent_id:02X},\n"
                f"  data=0x{self.data:09X},\n"
                f"  timestamp={self.timestamp:.1f}ns\n"
                f")")

    def format_bit_breakdown(self) -> str:
        """Format packet showing bit field breakdown - UPDATED"""
        # Reconstruct 64-bit value for bit analysis
        raw_64bit = (
            (self.pkt_type << 60) |      # [63:60] - 4 bits
            (self.protocol << 57) |      # [59:57] - 3 bits ✅ UPDATED
            (self.event_code << 53) |    # [56:53] - 4 bits ✅ UPDATED
            (self.channel_id << 47) |    # [52:47] - 6 bits
            (self.unit_id << 43) |       # [46:43] - 4 bits
            (self.agent_id << 35) |      # [42:35] - 8 bits
            (self.data & 0x7FFFFFFFF)    # [34:0] - 35 bits ✅ UPDATED
        )
        
        return (
            f"Raw Packet: 0x{raw_64bit:016X}\n"
            f"  [63:60] pkt_type   = 0x{self.pkt_type:X} ({self.get_packet_type_name()})\n"
            f"  [59:57] protocol   = 0x{self.protocol:X} ({self.get_protocol_name()}) ✅ 3-bit\n"
            f"  [56:53] event_code = 0x{self.event_code:X} ✅ moved\n"
            f"  [52:47] channel_id = 0x{self.channel_id:02X}\n"
            f"  [46:43] unit_id    = 0x{self.unit_id:X}\n"
            f"  [42:35] agent_id   = 0x{self.agent_id:02X}\n"
            f"  [34:0]  data       = 0x{self.data:09X} ✅ 35-bit"
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
        'data': data & 0x7FFFFFFFF  # ✅ UPDATED: Clamp to 35 bits
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
        'data': data & 0x7FFFFFFFF  # ✅ UPDATED: Clamp to 35 bits
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
        'data': data & 0x7FFFFFFFF  # ✅ UPDATED: Clamp to 35 bits
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
        'data': data & 0x7FFFFFFFF  # ✅ UPDATED: Clamp to 35 bits
    }


def validate_packet_field_ranges(packet: MonbusPacket) -> list:
    """Validate all packet fields are within proper ranges - UPDATED"""
    errors = []
    
    # Check all field ranges for updated format
    if packet.pkt_type > 15:  # 4 bits
        errors.append(f"pkt_type {packet.pkt_type} exceeds 4-bit range (0-15)")
        
    if packet.protocol > 7:  # 3 bits ✅ UPDATED
        errors.append(f"protocol {packet.protocol} exceeds 3-bit range (0-7)")
        
    if packet.event_code > 15:  # 4 bits
        errors.append(f"event_code {packet.event_code} exceeds 4-bit range (0-15)")
        
    if packet.channel_id > 63:  # 6 bits
        errors.append(f"channel_id {packet.channel_id} exceeds 6-bit range (0-63)")
        
    if packet.unit_id > 15:  # 4 bits
        errors.append(f"unit_id {packet.unit_id} exceeds 4-bit range (0-15)")
        
    if packet.agent_id > 255:  # 8 bits
        errors.append(f"agent_id {packet.agent_id} exceeds 8-bit range (0-255)")
        
    if packet.data > 0x7FFFFFFFF:  # 35 bits ✅ UPDATED
        errors.append(f"data 0x{packet.data:X} exceeds 35-bit range (0-0x7FFFFFFFF)")
    
    return errors


def analyze_packet_bit_usage(packet: MonbusPacket) -> Dict[str, Any]:
    """Analyze how packet uses the 64-bit format - UPDATED"""
    # Calculate bit positions and ranges
    analysis = {
        'total_bits': 64,
        'field_breakdown': {
            'pkt_type': {'bits': 4, 'position': '[63:60]', 'value': packet.pkt_type},
            'protocol': {'bits': 3, 'position': '[59:57]', 'value': packet.protocol},  # ✅ UPDATED
            'event_code': {'bits': 4, 'position': '[56:53]', 'value': packet.event_code},  # ✅ UPDATED
            'channel_id': {'bits': 6, 'position': '[52:47]', 'value': packet.channel_id},
            'unit_id': {'bits': 4, 'position': '[46:43]', 'value': packet.unit_id},
            'agent_id': {'bits': 8, 'position': '[42:35]', 'value': packet.agent_id},
            'data': {'bits': 35, 'position': '[34:0]', 'value': packet.data}  # ✅ UPDATED
        },
        'utilization': {
            'protocol_utilization': f"{packet.protocol}/7 ({packet.protocol/7*100:.1f}%)",  # ✅ UPDATED
            'data_utilization': f"0x{packet.data:X} / 0x7FFFFFFFF ({packet.data/0x7FFFFFFFF*100:.1f}%)"  # ✅ UPDATED
        },
        'validation': {
            'all_fields_valid': packet.validate_fields(),
            'field_range_errors': validate_packet_field_ranges(packet)
        }
    }
    
    return analysis