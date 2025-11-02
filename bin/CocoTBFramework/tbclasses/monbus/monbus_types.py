# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ProtocolType
# Purpose: Monitor Bus Type Definitions - Updated for 3-bit Protocol Field
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Monitor Bus Type Definitions - Updated for 3-bit Protocol Field

This module provides synchronized type definitions that match monitor_pkg.sv.
All packet parsing and field extraction functions have been updated for the new format.

UPDATED PACKET FORMAT (64 bits total):
- [63:60] - packet_type: 4 bits (error, timeout, completion, etc.)
- [59:57] - protocol:    3 bits (AXI/AXIS/APB/ARB/CORE) - ✅ INCREASED from 2 to 3 bits
- [56:53] - event_code:  4 bits (specific error or event code) - ✅ MOVED from [57:54]
- [52:47] - channel_id:  6 bits (channel ID and AXI ID) - ✅ UNCHANGED
- [46:43] - unit_id:     4 bits (subsystem identifier) - ✅ UNCHANGED
- [42:35] - agent_id:    8 bits (module identifier) - ✅ UNCHANGED
- [34:0]  - event_data:  35 bits (event-specific data) - ✅ REDUCED from 36 to 35 bits

Key Changes from Previous Version:
1. Protocol field expanded to 3 bits to support more protocols
2. Event data field reduced by 1 bit to accommodate protocol expansion
3. All field extraction functions updated for new bit positions
"""

from enum import IntEnum
from typing import List, Optional, Union, Dict, Any
from dataclasses import dataclass


# =============================================================================
# PROTOCOL DEFINITIONS - SYNCHRONIZED WITH monitor_pkg.sv
# =============================================================================

class ProtocolType(IntEnum):
    """Protocol types - synchronized with monitor_pkg.sv protocol_type_t"""
    PROTOCOL_AXI  = 0b000  # 0x0
    PROTOCOL_AXIS = 0b001  # 0x1
    PROTOCOL_APB  = 0b010  # 0x2
    PROTOCOL_ARB  = 0b011  # 0x3
    PROTOCOL_CORE = 0b100  # 0x4
    # 0b101-0b111 reserved for future use


# =============================================================================
# PACKET TYPE DEFINITIONS - SYNCHRONIZED WITH monitor_pkg.sv
# =============================================================================

class PktType(IntEnum):
    """Packet types - synchronized with monitor_pkg.sv"""
    PktTypeError      = 0x0  # Error event
    PktTypeCompletion = 0x1  # Transaction completion
    PktTypeThreshold  = 0x2  # Threshold crossed
    PktTypeTimeout    = 0x3  # Timeout event
    PktTypePerf       = 0x4  # Performance metric event
    PktTypeCredit     = 0x5  # Credit status (AXIS)
    PktTypeChannel    = 0x6  # Channel status (AXIS)
    PktTypeStream     = 0x7  # Stream event (AXIS)
    PktTypeAddrMatch  = 0x8  # Address match event (AXI)
    PktTypeAPB        = 0x9  # APB-specific event
    PktTypeReservedA  = 0xA  # Reserved
    PktTypeReservedB  = 0xB  # Reserved
    PktTypeReservedC  = 0xC  # Reserved
    PktTypeReservedD  = 0xD  # Reserved
    PktTypeReservedE  = 0xE  # Reserved
    PktTypeDebug      = 0xF  # Debug/trace event

    @classmethod
    def get_mask(cls, *packet_types) -> int:
        """Create a bitmask from multiple packet types"""
        mask = 0
        for pkt_type in packet_types:
            if isinstance(pkt_type, cls):
                mask |= (1 << pkt_type.value)
            elif isinstance(pkt_type, int):
                mask |= (1 << pkt_type)
        return mask


# =============================================================================
# ARB PROTOCOL EVENT CODES - SYNCHRONIZED WITH monitor_pkg.sv
# =============================================================================

class ARBErrorCode(IntEnum):
    """ARB Error Event Codes - synchronized with monitor_pkg.sv arb_error_code_t"""
    ARB_ERR_STARVATION         = 0x0  # Client request starvation
    ARB_ERR_ACK_TIMEOUT        = 0x1  # Grant ACK timeout  
    ARB_ERR_PROTOCOL_VIOLATION = 0x2  # ACK protocol violation
    ARB_ERR_CREDIT_VIOLATION   = 0x3  # Credit system violation
    ARB_ERR_FAIRNESS_VIOLATION = 0x4  # Weighted fairness violation
    ARB_ERR_WEIGHT_UNDERFLOW   = 0x5  # Weight credit underflow
    ARB_ERR_CONCURRENT_GRANTS  = 0x6  # Multiple simultaneous grants
    ARB_ERR_INVALID_GRANT_ID   = 0x7  # Invalid grant ID detected
    ARB_ERR_ORPHAN_ACK         = 0x8  # ACK without pending grant
    ARB_ERR_GRANT_OVERLAP      = 0x9  # Overlapping grant periods
    ARB_ERR_MASK_ERROR         = 0xA  # Round-robin mask error
    ARB_ERR_STATE_MACHINE      = 0xB  # FSM state error
    ARB_ERR_CONFIGURATION      = 0xC  # Invalid configuration
    ARB_ERR_RESERVED_D         = 0xD  # Reserved
    ARB_ERR_RESERVED_E         = 0xE  # Reserved
    ARB_ERR_USER_DEFINED       = 0xF  # User-defined error


class ARBTimeoutCode(IntEnum):
    """ARB Timeout Event Codes - synchronized with monitor_pkg.sv arb_timeout_code_t"""
    ARB_TIMEOUT_GRANT_ACK     = 0x0  # Grant ACK timeout
    ARB_TIMEOUT_REQUEST_HOLD  = 0x1  # Request held too long
    ARB_TIMEOUT_WEIGHT_UPDATE = 0x2  # Weight update timeout
    ARB_TIMEOUT_BLOCK_RELEASE = 0x3  # Block release timeout
    ARB_TIMEOUT_CREDIT_UPDATE = 0x4  # Credit update timeout
    ARB_TIMEOUT_STATE_CHANGE  = 0x5  # State machine timeout
    ARB_TIMEOUT_RESERVED_6    = 0x6  # Reserved
    ARB_TIMEOUT_RESERVED_7    = 0x7  # Reserved
    ARB_TIMEOUT_RESERVED_8    = 0x8  # Reserved
    ARB_TIMEOUT_RESERVED_9    = 0x9  # Reserved
    ARB_TIMEOUT_RESERVED_A    = 0xA  # Reserved
    ARB_TIMEOUT_RESERVED_B    = 0xB  # Reserved
    ARB_TIMEOUT_RESERVED_C    = 0xC  # Reserved
    ARB_TIMEOUT_RESERVED_D    = 0xD  # Reserved
    ARB_TIMEOUT_RESERVED_E    = 0xE  # Reserved
    ARB_TIMEOUT_USER_DEFINED  = 0xF  # User-defined timeout


class ARBCompletionCode(IntEnum):
    """ARB Completion Event Codes - synchronized with monitor_pkg.sv arb_completion_code_t"""
    ARB_COMPL_GRANT_ISSUED    = 0x0  # Grant successfully issued
    ARB_COMPL_ACK_RECEIVED    = 0x1  # ACK successfully received
    ARB_COMPL_TRANSACTION     = 0x2  # Complete transaction (grant+ack)
    ARB_COMPL_WEIGHT_UPDATE   = 0x3  # Weight update completed
    ARB_COMPL_CREDIT_CYCLE    = 0x4  # Credit cycle completed
    ARB_COMPL_FAIRNESS_PERIOD = 0x5  # Fairness analysis period
    ARB_COMPL_BLOCK_PERIOD    = 0x6  # Block period completed
    ARB_COMPL_RESERVED_7      = 0x7  # Reserved
    ARB_COMPL_RESERVED_8      = 0x8  # Reserved
    ARB_COMPL_RESERVED_9      = 0x9  # Reserved
    ARB_COMPL_RESERVED_A      = 0xA  # Reserved
    ARB_COMPL_RESERVED_B      = 0xB  # Reserved
    ARB_COMPL_RESERVED_C      = 0xC  # Reserved
    ARB_COMPL_RESERVED_D      = 0xD  # Reserved
    ARB_COMPL_RESERVED_E      = 0xE  # Reserved
    ARB_COMPL_USER_DEFINED    = 0xF  # User-defined completion


class ARBThresholdCode(IntEnum):
    """ARB Threshold Event Codes - synchronized with monitor_pkg.sv arb_threshold_code_t"""
    ARB_THRESH_REQUEST_LATENCY  = 0x0  # Request-to-grant latency threshold
    ARB_THRESH_ACK_LATENCY      = 0x1  # Grant-to-ACK latency threshold
    ARB_THRESH_FAIRNESS_DEV     = 0x2  # Fairness deviation threshold
    ARB_THRESH_ACTIVE_REQUESTS  = 0x3  # Active request count threshold
    ARB_THRESH_GRANT_RATE       = 0x4  # Grant rate threshold
    ARB_THRESH_EFFICIENCY       = 0x5  # Grant efficiency threshold
    ARB_THRESH_CREDIT_LOW       = 0x6  # Low credit threshold
    ARB_THRESH_WEIGHT_IMBALANCE = 0x7  # Weight imbalance threshold
    ARB_THRESH_STARVATION_TIME  = 0x8  # Starvation time threshold
    ARB_THRESH_RESERVED_9       = 0x9  # Reserved
    ARB_THRESH_RESERVED_A       = 0xA  # Reserved
    ARB_THRESH_RESERVED_B       = 0xB  # Reserved
    ARB_THRESH_RESERVED_C       = 0xC  # Reserved
    ARB_THRESH_RESERVED_D       = 0xD  # Reserved
    ARB_THRESH_RESERVED_E       = 0xE  # Reserved
    ARB_THRESH_USER_DEFINED     = 0xF  # User-defined threshold


class ARBPerformanceCode(IntEnum):
    """ARB Performance Event Codes - synchronized with monitor_pkg.sv arb_performance_code_t"""
    ARB_PERF_GRANT_ISSUED       = 0x0  # Grant issued event
    ARB_PERF_ACK_RECEIVED       = 0x1  # ACK received event
    ARB_PERF_GRANT_EFFICIENCY   = 0x2  # Grant completion efficiency
    ARB_PERF_FAIRNESS_METRIC    = 0x3  # Fairness compliance metric
    ARB_PERF_THROUGHPUT         = 0x4  # Arbitration throughput
    ARB_PERF_LATENCY_AVG        = 0x5  # Average latency measurement
    ARB_PERF_WEIGHT_COMPLIANCE  = 0x6  # Weight compliance metric
    ARB_PERF_CREDIT_UTILIZATION = 0x7  # Credit utilization efficiency
    ARB_PERF_CLIENT_ACTIVITY    = 0x8  # Per-client activity metric
    ARB_PERF_STARVATION_COUNT   = 0x9  # Starvation event count
    ARB_PERF_BLOCK_EFFICIENCY   = 0xA  # Block/unblock efficiency
    ARB_PERF_RESERVED_B         = 0xB  # Reserved
    ARB_PERF_RESERVED_C         = 0xC  # Reserved
    ARB_PERF_RESERVED_D         = 0xD  # Reserved
    ARB_PERF_RESERVED_E         = 0xE  # Reserved
    ARB_PERF_USER_DEFINED       = 0xF  # User-defined performance


class ARBDebugCode(IntEnum):
    """ARB Debug Event Codes - synchronized with monitor_pkg.sv arb_debug_code_t"""
    ARB_DEBUG_STATE_CHANGE     = 0x0  # Arbiter state machine change
    ARB_DEBUG_MASK_UPDATE      = 0x1  # Round-robin mask update
    ARB_DEBUG_WEIGHT_CHANGE    = 0x2  # Weight configuration change
    ARB_DEBUG_CREDIT_UPDATE    = 0x3  # Credit level update
    ARB_DEBUG_CLIENT_MASK      = 0x4  # Client enable/disable mask
    ARB_DEBUG_PRIORITY_CHANGE  = 0x5  # Priority level change
    ARB_DEBUG_BLOCK_EVENT      = 0x6  # Block/unblock event
    ARB_DEBUG_QUEUE_STATUS     = 0x7  # Request queue status
    ARB_DEBUG_COUNTER_SNAPSHOT = 0x8  # Counter values snapshot
    ARB_DEBUG_FIFO_STATUS      = 0x9  # FIFO status change
    ARB_DEBUG_FAIRNESS_STATE   = 0xA  # Fairness tracking state
    ARB_DEBUG_ACK_STATE        = 0xB  # ACK protocol state
    ARB_DEBUG_RESERVED_C       = 0xC  # Reserved
    ARB_DEBUG_RESERVED_D       = 0xD  # Reserved
    ARB_DEBUG_RESERVED_E       = 0xE  # Reserved
    ARB_DEBUG_USER_DEFINED     = 0xF  # User-defined debug


# =============================================================================
# AXI PROTOCOL EVENT CODES (Partial - for reference)
# =============================================================================

class AXIErrorCode(IntEnum):
    """AXI Error Event Codes - partial set for reference"""
    AXI_ERR_RESP_SLVERR        = 0x0  # Slave error response
    AXI_ERR_RESP_DECERR        = 0x1  # Decode error response
    AXI_ERR_DATA_ORPHAN        = 0x2  # Data without command
    AXI_ERR_RESP_ORPHAN        = 0x3  # Response without transaction
    AXI_ERR_PROTOCOL           = 0x4  # Protocol violation


class AXITimeoutCode(IntEnum):
    """AXI Timeout Event Codes"""
    AXI_TIMEOUT_CMD            = 0x0  # Command/Address timeout
    AXI_TIMEOUT_DATA           = 0x1  # Data timeout
    AXI_TIMEOUT_RESP           = 0x2  # Response timeout


# =============================================================================
# APB PROTOCOL EVENT CODES (Partial - for reference)
# =============================================================================

class APBErrorCode(IntEnum):
    """APB Error Event Codes"""
    APB_ERR_PSLVERR            = 0x0  # Peripheral slave error
    APB_ERR_SETUP_VIOLATION    = 0x1  # Setup phase protocol violation
    APB_ERR_ACCESS_VIOLATION   = 0x2  # Access phase protocol violation


# =============================================================================
# AXIS PROTOCOL EVENT CODES (Partial - for reference)
# =============================================================================

class AXISErrorCode(IntEnum):
    """AXIS Error Event Codes"""
    AXIS_ERR_PROTOCOL          = 0x0  # Protocol violation
    AXIS_ERR_READY_TIMING      = 0x1  # TREADY timing violation
    AXIS_ERR_VALID_TIMING      = 0x2  # TVALID timing violation


# =============================================================================
# PACKET FIELD EXTRACTION FUNCTIONS - UPDATED FOR NEW FORMAT
# =============================================================================

def get_packet_type(packet: int) -> int:
    """Extract packet type from 64-bit monitor packet"""
    return (packet >> 60) & 0xF


def get_protocol(packet: int) -> int:
    """Extract protocol from 64-bit monitor packet - ✅ UPDATED for 3-bit field"""
    return (packet >> 57) & 0x7  # ✅ CHANGED: Now 3 bits at [59:57]


def get_event_code(packet: int) -> int:
    """Extract event code from 64-bit monitor packet - ✅ UPDATED bit position"""
    return (packet >> 53) & 0xF  # ✅ CHANGED: Now at [56:53] (was [57:54])


def get_channel_id(packet: int) -> int:
    """Extract channel ID from 64-bit monitor packet"""
    return (packet >> 47) & 0x3F  # ✅ UNCHANGED: 6 bits at [52:47]


def get_unit_id(packet: int) -> int:
    """Extract unit ID from 64-bit monitor packet"""
    return (packet >> 43) & 0xF  # ✅ UNCHANGED: 4 bits at [46:43]


def get_agent_id(packet: int) -> int:
    """Extract agent ID from 64-bit monitor packet"""
    return (packet >> 35) & 0xFF  # ✅ UNCHANGED: 8 bits at [42:35]


def get_event_data(packet: int) -> int:
    """Extract event data from 64-bit monitor packet - ✅ UPDATED for 35-bit field"""
    return packet & 0x7FFFFFFFF  # ✅ CHANGED: Now 35 bits [34:0] (was 36 bits)


def create_monitor_packet(packet_type: int, protocol: int, event_code: int, 
                         channel_id: int, unit_id: int, agent_id: int, 
                         event_data: int) -> int:
    """Create a 64-bit monitor packet from individual fields - ✅ UPDATED"""
    return (
        ((packet_type & 0xF) << 60) |      # [63:60] - 4 bits
        ((protocol & 0x7) << 57) |         # [59:57] - 3 bits ✅ UPDATED
        ((event_code & 0xF) << 53) |       # [56:53] - 4 bits ✅ UPDATED
        ((channel_id & 0x3F) << 47) |      # [52:47] - 6 bits
        ((unit_id & 0xF) << 43) |          # [46:43] - 4 bits
        ((agent_id & 0xFF) << 35) |        # [42:35] - 8 bits
        (event_data & 0x7FFFFFFFF)         # [34:0] - 35 bits ✅ UPDATED
    )


# =============================================================================
# PACKET ANALYSIS AND VALIDATION FUNCTIONS
# =============================================================================

def is_valid_protocol_type(protocol: int) -> bool:
    """Check if protocol type is valid"""
    return protocol in [p.value for p in ProtocolType]


def is_valid_packet_type(packet_type: int) -> bool:
    """Check if packet type is valid"""
    return packet_type in [p.value for p in PktType]


def get_event_code_enum(protocol: int, packet_type: int, event_code: int):
    """Get the appropriate enum for an event code"""
    if protocol == ProtocolType.PROTOCOL_ARB:
        if packet_type == PktType.PktTypeError:
            return ARBErrorCode(event_code)
        elif packet_type == PktType.PktTypeTimeout:
            return ARBTimeoutCode(event_code)
        elif packet_type == PktType.PktTypeCompletion:
            return ARBCompletionCode(event_code)
        elif packet_type == PktType.PktTypeThreshold:
            return ARBThresholdCode(event_code)
        elif packet_type == PktType.PktTypePerf:
            return ARBPerformanceCode(event_code)
        elif packet_type == PktType.PktTypeDebug:
            return ARBDebugCode(event_code)
    # Add other protocols as needed
    return None


def is_valid_event_code(protocol: int, packet_type: int, event_code: int) -> bool:
    """Check if an event code is valid for the given protocol and packet type"""
    try:
        enum_obj = get_event_code_enum(protocol, packet_type, event_code)
        return enum_obj is not None
    except ValueError:
        return False


def get_event_code_name(protocol: int, packet_type: int, event_code: int) -> str:
    """Get human-readable name for an event code"""
    try:
        enum_obj = get_event_code_enum(protocol, packet_type, event_code)
        if enum_obj:
            return enum_obj.name
        return f"UNKNOWN_EVENT_{event_code:X}"
    except ValueError:
        return f"INVALID_EVENT_{event_code:X}"


def get_protocol_name(protocol: int) -> str:
    """Get human-readable protocol name"""
    try:
        return ProtocolType(protocol).name
    except ValueError:
        return f"UNKNOWN_PROTOCOL_{protocol}"


def get_packet_type_name(packet_type: int) -> str:
    """Get human-readable packet type name"""
    try:
        return PktType(packet_type).name
    except ValueError:
        return f"UNKNOWN_PACKET_TYPE_{packet_type}"


# =============================================================================
# PACKET DATA STRUCTURE
# =============================================================================

@dataclass
class MonitorPacket:
    """Parsed monitor packet structure"""
    packet_type: int
    protocol: int
    event_code: int
    channel_id: int
    unit_id: int
    agent_id: int
    event_data: int
    raw_packet: int

    @classmethod
    def from_raw(cls, raw_packet: int) -> 'MonitorPacket':
        """Create MonitorPacket from raw 64-bit value"""
        return cls(
            packet_type=get_packet_type(raw_packet),
            protocol=get_protocol(raw_packet),
            event_code=get_event_code(raw_packet),
            channel_id=get_channel_id(raw_packet),
            unit_id=get_unit_id(raw_packet),
            agent_id=get_agent_id(raw_packet),
            event_data=get_event_data(raw_packet),
            raw_packet=raw_packet
        )

    def to_raw(self) -> int:
        """Convert back to raw 64-bit value"""
        return create_monitor_packet(
            self.packet_type, self.protocol, self.event_code,
            self.channel_id, self.unit_id, self.agent_id, self.event_data
        )

    def get_protocol_name(self) -> str:
        """Get human-readable protocol name"""
        return get_protocol_name(self.protocol)

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        return get_packet_type_name(self.packet_type)

    def get_event_code_name(self) -> str:
        """Get human-readable event code name"""
        return get_event_code_name(self.protocol, self.packet_type, self.event_code)

    def is_valid(self) -> bool:
        """Check if packet has valid field values"""
        return (
            is_valid_protocol_type(self.protocol) and
            is_valid_packet_type(self.packet_type) and
            is_valid_event_code(self.protocol, self.packet_type, self.event_code)
        )

    def __str__(self) -> str:
        """Human-readable string representation"""
        return (
            f"[{self.get_protocol_name()}_{self.get_packet_type_name()}] "
            f"{self.get_event_code_name()} | "
            f"Agent:{self.agent_id:02X} Unit:{self.unit_id:X} Ch:{self.channel_id:02X} | "
            f"Data:{self.event_data:09X}"
        )


# =============================================================================
# HELPER FUNCTIONS FOR TESTING AND DEBUGGING
# =============================================================================

def validate_monitor_packet(packet: int) -> bool:
    """Validate that a monitor packet has valid field values"""
    try:
        parsed = MonitorPacket.from_raw(packet)
        return parsed.is_valid()
    except (ValueError, TypeError):
        return False


def debug_packet_bits(packet: int) -> str:
    """Return detailed bit-level breakdown of a monitor packet for debugging"""
    lines = []
    lines.append(f"Raw packet: 0x{packet:016X} (64-bit)")
    lines.append("Bit-level breakdown:")
    lines.append(f"  [63:60] packet_type = 0b{(packet >> 60) & 0xF:04b} (0x{(packet >> 60) & 0xF:X})")
    lines.append(f"  [59:57] protocol    = 0b{(packet >> 57) & 0x7:03b} (0x{(packet >> 57) & 0x7:X})")
    lines.append(f"  [56:53] event_code  = 0b{(packet >> 53) & 0xF:04b} (0x{(packet >> 53) & 0xF:X})")
    lines.append(f"  [52:47] channel_id  = 0b{(packet >> 47) & 0x3F:06b} (0x{(packet >> 47) & 0x3F:02X})")
    lines.append(f"  [46:43] unit_id     = 0b{(packet >> 43) & 0xF:04b} (0x{(packet >> 43) & 0xF:X})")
    lines.append(f"  [42:35] agent_id    = 0b{(packet >> 35) & 0xFF:08b} (0x{(packet >> 35) & 0xFF:02X})")
    lines.append(f"  [34:0]  event_data  = 0x{packet & 0x7FFFFFFFF:09X} ({packet & 0x7FFFFFFFF})")

    # Try to parse and show human-readable names
    try:
        parsed = MonitorPacket.from_raw(packet)
        lines.append("\nParsed fields:")
        lines.append(f"  Protocol: {parsed.get_protocol_name()}")
        lines.append(f"  Packet Type: {parsed.get_packet_type_name()}")
        lines.append(f"  Event Code: {parsed.get_event_code_name()}")
        lines.append(f"  Valid: {parsed.is_valid()}")
    except (ValueError, TypeError) as e:
        lines.append(f"\nParsing error: {e}")

    return "\n".join(lines)


def format_packet_fields(packet: int) -> Dict[str, Any]:
    """Format packet as dictionary with all field values"""
    return {
        'packet_type': get_packet_type(packet),
        'packet_type_name': get_packet_type_name(get_packet_type(packet)),
        'protocol': get_protocol(packet),
        'protocol_name': get_protocol_name(get_protocol(packet)),
        'event_code': get_event_code(packet),
        'event_code_name': get_event_code_name(get_protocol(packet), get_packet_type(packet), get_event_code(packet)),
        'channel_id': get_channel_id(packet),
        'unit_id': get_unit_id(packet),
        'agent_id': get_agent_id(packet),
        'event_data': get_event_data(packet),
        'raw_packet': packet
    }
