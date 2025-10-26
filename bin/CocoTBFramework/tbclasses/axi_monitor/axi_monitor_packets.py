# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXITransactionState
# Purpose: AXI4/AXIL Monitor Packet Definitions - FIXED FORWARD REFERENCES
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4/AXIL Monitor Packet Definitions - FIXED FORWARD REFERENCES

Updated to align with the enhanced monitor_pkg.sv changes:
1. Updated packet format with protocol field (2 bits at [59:58])
2. Event data reduced from 38 bits to 36 bits
3. Support for unified event codes and multi-protocol support
4. Enhanced packet types and threshold events
5. FIXED: Reorganized class definitions to resolve forward reference issues
"""

from typing import Optional, Dict, Any, List, Union
from dataclasses import dataclass
from enum import Enum
import time

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class AXITransactionState(Enum):
    """AXI Transaction state tracking (unchanged)"""
    EMPTY = "empty"
    ADDR_PHASE = "addr_phase"
    DATA_PHASE = "data_phase"
    RESP_PHASE = "resp_phase"
    COMPLETE = "complete"
    ERROR = "error"
    ORPHANED = "orphaned"


class MonitorEventCode(Enum):
    """Monitor event codes matching RTL definitions (AXI-specific)"""
    NONE = 0x0
    CMD_TIMEOUT = 0x1
    DATA_TIMEOUT = 0x2
    RESP_TIMEOUT = 0x3
    RESP_ERROR = 0x4
    RESP_SLVERR = 0x5
    RESP_DECERR = 0x6
    DATA_ORPHAN = 0x7
    RESP_ORPHAN = 0x8
    PROTOCOL = 0x9
    TRANS_COMPLETE = 0xA
    ADDR_MISS_T0 = 0xB
    ADDR_MISS_T1 = 0xC
    USER_DEFINED = 0xF


class InterruptPacketType(Enum):
    """Interrupt bus packet types (updated with new types)"""
    ERROR = 0x0
    COMPLETION = 0x1
    THRESHOLD = 0x2
    TIMEOUT = 0x3
    PERF = 0x4
    CREDIT = 0x5      # New: Credit status (packet protocols)
    CHANNEL = 0x6     # New: Channel status (packet protocols)
    STREAM = 0x7      # New: Stream event (packet protocols)
    DEBUG = 0xF


class ProtocolType(Enum):
    """Protocol types from monitor_pkg.sv"""
    AXI = 0x0
    PKT = 0x1  # Packet-based protocol
    APB = 0x2
    CUSTOM = 0x3


class PerformanceMetric(Enum):
    """Performance metric types (updated with new metrics)"""
    ADDR_LATENCY = 0x0
    DATA_LATENCY = 0x1
    RESP_LATENCY = 0x2
    TOTAL_LATENCY = 0x3
    THROUGHPUT = 0x4
    ERROR_RATE = 0x5
    ACTIVE_COUNT = 0x6
    COMPLETED_COUNT = 0x7
    ERROR_COUNT = 0x8
    CREDIT_EFFICIENCY = 0x9  # New: Credit utilization (packet protocols)
    CHANNEL_UTIL = 0xA       # New: Channel utilization (packet protocols)
    PACKET_RATE = 0xB        # New: Packet rate (packet protocols)
    CUSTOM = 0xF


class ThresholdEvent(Enum):
    """Threshold event types (updated with new events)"""
    ACTIVE_COUNT = 0x0
    LATENCY = 0x1
    ERROR_RATE = 0x2
    BUFFER_LEVEL = 0x3
    CREDIT_LOW = 0x4         # New: Credit low threshold (packet protocols)
    PACKET_RATE = 0x5        # New: Packet rate threshold (packet protocols)
    CHANNEL_STALL = 0x6      # New: Channel stall threshold (packet protocols)
    CUSTOM = 0xF


# =============================================================================
# Field Configuration Functions (updated for new packet format)
# =============================================================================

def create_interrupt_packet_field_config() -> FieldConfig:
    """Create interrupt bus packet field configuration (64-bit) - Updated format"""
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="packet_type", bits=4, format="hex",
        description="Packet type (error, completion, etc.)"
    ))
    
    config.add_field(FieldDefinition(
        name="protocol", bits=2, format="hex",
        description="Protocol type (AXI/PKT/APB/Custom)"
    ))
    
    config.add_field(FieldDefinition(
        name="event_code", bits=4, format="hex",
        description="Event/error code"
    ))
    
    config.add_field(FieldDefinition(
        name="channel_id", bits=6, format="hex",
        description="Channel/ID information"
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
        name="data", bits=36, format="hex",  # Updated from 38 to 36 bits
        description="Event data (address, metric, etc.)"
    ))

    return config


def create_axi_command_field_config(id_width: int = 8, addr_width: int = 32, user_width: int = 1) -> FieldConfig:
    """Create AXI address channel field configuration (AR/AW) - Unchanged"""
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="id", bits=id_width, format="hex",
        description="Transaction ID"
    ))
    config.add_field(FieldDefinition(
        name="addr", bits=addr_width, format="hex",
        description="Address"
    ))
    config.add_field(FieldDefinition(
        name="len", bits=8, format="dec",
        description="Burst length (transfers - 1)"
    ))
    config.add_field(FieldDefinition(
        name="size", bits=3, format="dec",
        description="Burst size (bytes per transfer)"
    ))
    config.add_field(FieldDefinition(
        name="burst", bits=2, format="dec",
        description="Burst type",
        encoding={0: "FIXED", 1: "INCR", 2: "WRAP"}
    ))
    config.add_field(FieldDefinition(
        name="lock", bits=1, format="dec",
        description="Lock type"
    ))
    config.add_field(FieldDefinition(
        name="cache", bits=4, format="hex",
        description="Cache control"
    ))
    config.add_field(FieldDefinition(
        name="prot", bits=3, format="hex",
        description="Protection attributes"
    ))
    config.add_field(FieldDefinition(
        name="qos", bits=4, format="dec",
        description="Quality of Service"
    ))
    config.add_field(FieldDefinition(
        name="region", bits=4, format="dec",
        description="Region identifier"
    ))

    if user_width > 0:
        config.add_field(FieldDefinition(
            name="user", bits=user_width, format="hex",
            description="User-defined signals"
        ))

    return config


def create_axi_read_data_field_config(id_width: int = 8, data_width: int = 32, user_width: int = 1) -> FieldConfig:
    """Create AXI read data channel field configuration (R) - Unchanged"""
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="id", bits=id_width, format="hex",
        description="Transaction ID"
    ))
    config.add_field(FieldDefinition(
        name="data", bits=data_width, format="hex",
        description="Read data"
    ))
    config.add_field(FieldDefinition(
        name="resp", bits=2, format="dec",
        description="Response status",
        encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
    ))
    config.add_field(FieldDefinition(
        name="last", bits=1, format="dec",
        description="Last transfer in burst"
    ))

    if user_width > 0:
        config.add_field(FieldDefinition(
            name="user", bits=user_width, format="hex",
            description="User-defined signals"
        ))

    return config


def create_axi_write_data_field_config(data_width: int = 32, user_width: int = 1) -> FieldConfig:
    """Create AXI write data channel field configuration (W) - Unchanged"""
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="data", bits=data_width, format="hex",
        description="Write data"
    ))
    config.add_field(FieldDefinition(
        name="strb", bits=data_width//8, format="hex",
        description="Write strobes"
    ))
    config.add_field(FieldDefinition(
        name="last", bits=1, format="dec",
        description="Last transfer in burst"
    ))

    if user_width > 0:
        config.add_field(FieldDefinition(
            name="user", bits=user_width, format="hex",
            description="User-defined signals"
        ))

    return config


def create_axi_write_response_field_config(id_width: int = 8, user_width: int = 1) -> FieldConfig:
    """Create AXI write response channel field configuration (B) - Unchanged"""
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="id", bits=id_width, format="hex",
        description="Transaction ID"
    ))
    config.add_field(FieldDefinition(
        name="resp", bits=2, format="dec",
        description="Response status",
        encoding={0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
    ))

    if user_width > 0:
        config.add_field(FieldDefinition(
            name="user", bits=user_width, format="hex",
            description="User-defined signals"
        ))

    return config


def create_monitor_config_field_config() -> FieldConfig:
    """Create monitor configuration field configuration - Unchanged"""
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="freq_sel", bits=4, format="dec",
        description="Timer frequency selection"
    ))
    config.add_field(FieldDefinition(
        name="addr_cnt", bits=4, format="dec",
        description="Address timeout count"
    ))
    config.add_field(FieldDefinition(
        name="data_cnt", bits=4, format="dec",
        description="Data timeout count"
    ))
    config.add_field(FieldDefinition(
        name="resp_cnt", bits=4, format="dec",
        description="Response timeout count"
    ))
    config.add_field(FieldDefinition(
        name="error_enable", bits=1, format="dec",
        description="Enable error packets"
    ))
    config.add_field(FieldDefinition(
        name="compl_enable", bits=1, format="dec",
        description="Enable completion packets"
    ))
    config.add_field(FieldDefinition(
        name="threshold_enable", bits=1, format="dec",
        description="Enable threshold packets"
    ))
    config.add_field(FieldDefinition(
        name="timeout_enable", bits=1, format="dec",
        description="Enable timeout packets"
    ))
    config.add_field(FieldDefinition(
        name="perf_enable", bits=1, format="dec",
        description="Enable performance packets"
    ))
    config.add_field(FieldDefinition(
        name="debug_enable", bits=1, format="dec",
        description="Enable debug packets"
    ))
    config.add_field(FieldDefinition(
        name="active_trans_threshold", bits=16, format="dec",
        description="Active transaction threshold"
    ))
    config.add_field(FieldDefinition(
        name="latency_threshold", bits=32, format="dec",
        description="Latency threshold (cycles)"
    ))

    return config


# =============================================================================
# AXI Packet Classes - MOVED BEFORE MonitoredTransaction to fix forward references
# =============================================================================

class AXICommandPacket(GAXIPacket):
    """AXI Address Channel packet (AR/AW)"""

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        if field_config is None:
            field_config = create_axi_command_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None):
        """Create packet from dictionary"""
        return cls(field_config=field_config, **data)


class AXIReadDataPacket(GAXIPacket):
    """AXI Read Data Channel packet (R)"""

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        if field_config is None:
            field_config = create_axi_read_data_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None):
        """Create packet from dictionary"""
        return cls(field_config=field_config, **data)

    def get_response_name(self) -> str:
        """Get human-readable response name"""
        resp_map = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        return resp_map.get(self.resp, f"UNKNOWN({self.resp})")

    def is_error_response(self) -> bool:
        """Check if this is an error response"""
        return self.resp in [2, 3]  # SLVERR or DECERR


class AXIWriteDataPacket(GAXIPacket):
    """AXI Write Data Channel packet (W)"""

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        if field_config is None:
            field_config = create_axi_write_data_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None):
        """Create packet from dictionary"""
        return cls(field_config=field_config, **data)

    def get_strobe_pattern(self) -> str:
        """Get formatted strobe pattern"""
        return f"0x{self.strb:X}"

    def get_active_bytes(self) -> int:
        """Count number of active byte lanes"""
        return bin(self.strb).count('1')


class AXIWriteResponsePacket(GAXIPacket):
    """AXI Write Response Channel packet (B)"""

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        if field_config is None:
            field_config = create_axi_write_response_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None):
        """Create packet from dictionary"""
        return cls(field_config=field_config, **data)

    def get_response_name(self) -> str:
        """Get human-readable response name"""
        resp_map = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        return resp_map.get(self.resp, f"UNKNOWN({self.resp})")

    def is_error_response(self) -> bool:
        """Check if this is an error response"""
        return self.resp in [2, 3]  # SLVERR or DECERR


# =============================================================================
# Interrupt Packet Class
# =============================================================================

class InterruptPacket(GAXIPacket):
    """Monitor Interrupt Bus packet (64-bit consolidated format) - Updated"""

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        if field_config is None:
            field_config = create_interrupt_packet_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None):
        """Create packet from dictionary"""
        return cls(field_config=field_config, **data)

    @classmethod
    def from_64bit_value(cls, value: int) -> 'InterruptPacket':
        """Create packet from 64-bit interrupt bus value (updated format)"""
        return cls(
            packet_type=(value >> 60) & 0xF,
            protocol=(value >> 58) & 0x3,        # NEW: Protocol field
            event_code=(value >> 54) & 0xF,       # Shifted
            channel_id=(value >> 48) & 0x3F,      # Shifted
            unit_id=(value >> 44) & 0xF,          # Shifted
            agent_id=(value >> 36) & 0xFF,        # Shifted
            data=value & 0xFFFFFFFFF              # 36 bits instead of 38
        )

    def to_64bit_value(self) -> int:
        """Convert packet to 64-bit interrupt bus value (updated format)"""
        return (
            (self.packet_type << 60) |
            (self.protocol << 58) |        # NEW: Protocol field
            (self.event_code << 54) |      # Shifted
            (self.channel_id << 48) |      # Shifted
            (self.unit_id << 44) |         # Shifted
            (self.agent_id << 36) |        # Shifted
            (self.data & 0xFFFFFFFFF)      # 36 bits instead of 38
        )

    def get_protocol_name(self) -> str:
        """Get human-readable protocol name"""
        try:
            return ProtocolType(self.protocol).name
        except ValueError:
            return f"UNKNOWN_PROTOCOL({self.protocol:X})"

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        type_map = {
            0x0: "ERROR",
            0x1: "COMPLETION", 
            0x2: "THRESHOLD",
            0x3: "TIMEOUT",
            0x4: "PERF",
            0x5: "CREDIT",     # New
            0x6: "CHANNEL",    # New
            0x7: "STREAM",     # New
            0xF: "DEBUG"
        }
        return type_map.get(self.packet_type, f"UNKNOWN({self.packet_type:X})")

    def get_event_code_name(self) -> str:
        """Get human-readable event code name (protocol-aware)"""
        if self.protocol == ProtocolType.AXI.value:
            try:
                event = MonitorEventCode(self.event_code)
                return event.name
            except ValueError:
                return f"UNKNOWN_AXI_EVENT({self.event_code:X})"
        else:
            # For other protocols, use generic naming
            return f"EVENT_{self.event_code:X}"

    def is_axi_protocol(self) -> bool:
        """Check if this is an AXI protocol packet"""
        return self.protocol == ProtocolType.AXI.value

    def is_error_packet(self) -> bool:
        """Check if this is an error packet"""
        return self.packet_type == InterruptPacketType.ERROR.value

    def is_timeout_packet(self) -> bool:
        """Check if this is a timeout packet"""
        return self.packet_type == InterruptPacketType.TIMEOUT.value

    def is_completion_packet(self) -> bool:
        """Check if this is a completion packet"""
        return self.packet_type == InterruptPacketType.COMPLETION.value

    def is_performance_packet(self) -> bool:
        """Check if this is a performance packet"""
        return self.packet_type == InterruptPacketType.PERF.value

    def is_credit_packet(self) -> bool:
        """Check if this is a credit packet (new)"""
        return self.packet_type == InterruptPacketType.CREDIT.value

    def is_channel_packet(self) -> bool:
        """Check if this is a channel packet (new)"""
        return self.packet_type == InterruptPacketType.CHANNEL.value

    def is_stream_packet(self) -> bool:
        """Check if this is a stream packet (new)"""
        return self.packet_type == InterruptPacketType.STREAM.value

    def get_address_value(self, addr_width: int = 32) -> int:
        """Extract address value from data field (max 36 bits now)"""
        max_addr_bits = min(addr_width, 36)  # Updated from 38 to 36
        return self.data & ((1 << max_addr_bits) - 1)

    def get_metric_value(self) -> int:
        """Extract metric value from data field"""
        return self.data


class MonitorConfigPacket(GAXIPacket):
    """Monitor Configuration packet - Unchanged"""

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        if field_config is None:
            field_config = create_monitor_config_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], field_config: Optional[FieldConfig] = None):
        """Create packet from dictionary"""
        return cls(field_config=field_config, **data)

    def get_enabled_features(self) -> List[str]:
        """Get list of enabled monitoring features"""
        features = []
        if getattr(self, 'error_enable', 0):
            features.append('ERROR')
        if getattr(self, 'compl_enable', 0):
            features.append('COMPLETION')
        if getattr(self, 'threshold_enable', 0):
            features.append('THRESHOLD')
        if getattr(self, 'timeout_enable', 0):
            features.append('TIMEOUT')
        if getattr(self, 'perf_enable', 0):
            features.append('PERFORMANCE')
        if getattr(self, 'debug_enable', 0):
            features.append('DEBUG')
        return features


# =============================================================================
# Transaction Tracking (MOVED AFTER all packet class definitions)
# =============================================================================

@dataclass
class MonitoredTransaction:
    """Complete monitored AXI transaction with all phases (updated)"""

    # Transaction identification
    transaction_id: int
    is_read: bool
    is_axi4: bool  # True for AXI4, False for AXI-Lite
    protocol: ProtocolType = ProtocolType.AXI  # NEW: Protocol type

    # Address phase
    address_packet: Optional[AXICommandPacket] = None
    address_timestamp: Optional[float] = None

    # Data phase
    data_packets: Optional[List[Union[AXIReadDataPacket, AXIWriteDataPacket]]] = None
    data_timestamps: Optional[List[float]] = None

    # Response phase (write only)
    response_packet: Optional[AXIWriteResponsePacket] = None
    response_timestamp: Optional[float] = None

    # Transaction state
    state: AXITransactionState = AXITransactionState.EMPTY
    start_time: float = 0.0
    completion_time: Optional[float] = None

    # Error tracking
    errors: Optional[List[str]] = None
    events: Optional[List[InterruptPacket]] = None

    # Performance metrics
    address_latency: Optional[float] = None
    data_latency: Optional[float] = None
    response_latency: Optional[float] = None
    total_latency: Optional[float] = None

    def __post_init__(self):
        """Initialize mutable default values"""
        if self.data_packets is None:
            self.data_packets = []
        if self.data_timestamps is None:
            self.data_timestamps = []
        if self.errors is None:
            self.errors = []
        if self.events is None:
            self.events = []
        if self.start_time == 0.0:
            self.start_time = time.time()

    def add_data_packet(self, packet: Union[AXIReadDataPacket, AXIWriteDataPacket], timestamp: float):
        """Add a data packet with timestamp"""
        self.data_packets.append(packet)
        self.data_timestamps.append(timestamp)

    def add_error(self, error: str):
        """Add an error to this transaction"""
        self.errors.append(error)
        if self.state not in [AXITransactionState.ERROR, AXITransactionState.COMPLETE]:
            self.state = AXITransactionState.ERROR

    def add_event(self, event: InterruptPacket):
        """Add an interrupt event to this transaction"""
        self.events.append(event)

    def mark_complete(self, timestamp: float):
        """Mark transaction as complete"""
        self.completion_time = timestamp
        if self.state != AXITransactionState.ERROR:
            self.state = AXITransactionState.COMPLETE

        # Calculate latencies
        if self.address_timestamp and self.start_time:
            self.address_latency = self.address_timestamp - self.start_time

        if self.is_read and self.data_timestamps:
            if self.address_timestamp and self.data_timestamps[-1]:
                self.data_latency = self.data_timestamps[-1] - self.address_timestamp
        elif not self.is_read and self.response_timestamp:
            if self.address_timestamp:
                self.response_latency = self.response_timestamp - self.address_timestamp

        if self.completion_time and self.start_time:
            self.total_latency = self.completion_time - self.start_time

    def is_complete(self) -> bool:
        """Check if transaction is complete"""
        return self.state in [AXITransactionState.COMPLETE, AXITransactionState.ERROR]

    def has_errors(self) -> bool:
        """Check if transaction has errors"""
        return len(self.errors) > 0 or self.state == AXITransactionState.ERROR

    def get_expected_data_beats(self) -> int:
        """Get expected number of data beats"""
        if self.address_packet:
            return self.address_packet.len + 1
        return 0

    def get_actual_data_beats(self) -> int:
        """Get actual number of data beats received"""
        return len(self.data_packets)

    def is_burst_transaction(self) -> bool:
        """Check if this is a burst transaction"""
        return self.get_expected_data_beats() > 1

    def get_transaction_summary(self) -> str:
        """Get a summary string for this transaction"""
        txn_type = "READ" if self.is_read else "WRITE"
        protocol_name = self.protocol.name if hasattr(self.protocol, 'name') else str(self.protocol)
        beats = f"{self.get_actual_data_beats()}/{self.get_expected_data_beats()}"
        
        summary = f"{protocol_name} {txn_type} ID={self.transaction_id:02X} "
        summary += f"state={self.state.value} beats={beats}"
        
        if self.has_errors():
            summary += f" errors={len(self.errors)}"
        
        if self.total_latency:
            summary += f" latency={self.total_latency:.1f}ns"
            
        return summary


# =============================================================================
# Conversion Functions (updated)
# =============================================================================

def convert_gaxi_to_axi_address(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXICommandPacket:
    """Convert GAXI packet to AXI address packet - Unchanged"""
    packet_data = {}
    for field_name in ['id', 'addr', 'len', 'size', 'burst', 'lock', 'cache', 'prot', 'qos', 'region', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)
    return AXICommandPacket.from_dict(packet_data, field_config)


def convert_gaxi_to_axi_read_data(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIReadDataPacket:
    """Convert GAXI packet to AXI read data packet - Unchanged"""
    packet_data = {}
    for field_name in ['id', 'data', 'resp', 'last', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)
    return AXIReadDataPacket.from_dict(packet_data, field_config)


def convert_gaxi_to_axi_write_data(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIWriteDataPacket:
    """Convert GAXI packet to AXI write data packet - Unchanged"""
    packet_data = {}
    for field_name in ['data', 'strb', 'last', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)
    return AXIWriteDataPacket.from_dict(packet_data, field_config)


def convert_gaxi_to_axi_write_response(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIWriteResponsePacket:
    """Convert GAXI packet to AXI write response packet - Unchanged"""
    packet_data = {}
    
    # Handle standard fields
    for field_name in ['id', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)
    
    # Handle response field - could be named 'resp' or 'code'
    if hasattr(gaxi_packet, 'resp'):
        packet_data['resp'] = gaxi_packet.resp
    elif hasattr(gaxi_packet, 'code'):
        packet_data['resp'] = gaxi_packet.code
    else:
        packet_data['resp'] = 0  # Default to OKAY
    
    return AXIWriteResponsePacket.from_dict(packet_data, field_config)


def convert_raw_to_interrupt_packet(raw_value: int) -> InterruptPacket:
    """Convert raw 64-bit value to interrupt packet (updated format)"""
    return InterruptPacket.from_64bit_value(raw_value)


# =============================================================================
# Utility Functions (updated)
# =============================================================================

def create_default_config_packet(**overrides) -> MonitorConfigPacket:
    """Create a monitor configuration packet with default values - Unchanged"""
    defaults = {
        'freq_sel': 3,
        'addr_cnt': 8,
        'data_cnt': 8,
        'resp_cnt': 8,
        'error_enable': 1,
        'compl_enable': 1,
        'threshold_enable': 1,
        'timeout_enable': 1,
        'perf_enable': 0,
        'debug_enable': 0,
        'active_trans_threshold': 8,
        'latency_threshold': 1000
    }
    defaults.update(overrides)
    return MonitorConfigPacket.from_dict(defaults)


def validate_packet_consistency(packet) -> List[str]:
    """Validate packet field consistency and return list of issues (updated)"""
    issues = []
    
    if isinstance(packet, AXICommandPacket):
        # Validate command packet
        if packet.len > 255:
            issues.append(f"Invalid burst length: {packet.len}")
        if packet.size > 7:
            issues.append(f"Invalid burst size: {packet.size}")
        if packet.burst > 2:
            issues.append(f"Invalid burst type: {packet.burst}")
            
    elif isinstance(packet, (AXIReadDataPacket, AXIWriteResponsePacket)):
        # Validate response codes
        if packet.resp > 3:
            issues.append(f"Invalid response code: {packet.resp}")
            
    elif isinstance(packet, InterruptPacket):
        # Validate interrupt packet (updated for new format)
        if packet.packet_type > 0xF:
            issues.append(f"Invalid packet type: {packet.packet_type:X}")
        if packet.protocol > 0x3:  # NEW: Validate protocol field
            issues.append(f"Invalid protocol: {packet.protocol:X}")
        if packet.event_code > 0xF:
            issues.append(f"Invalid event code: {packet.event_code:X}")
        if packet.channel_id > 0x3F:
            issues.append(f"Invalid channel ID: {packet.channel_id:X}")
        if packet.data > 0xFFFFFFFFF:  # Updated: 36 bits instead of 38
            issues.append(f"Invalid data field (too large): {packet.data:X}")
    
    return issues


def format_packet_summary(packet) -> str:
    """Generate a concise summary string for any packet type (updated)"""
    if isinstance(packet, AXICommandPacket):
        return f"CMD(ID={packet.id:02X}, ADDR=0x{packet.addr:X}, LEN={packet.len})"
    elif isinstance(packet, AXIReadDataPacket):
        return f"RDATA(ID={packet.id:02X}, RESP={packet.get_response_name()}, LAST={packet.last})"
    elif isinstance(packet, AXIWriteDataPacket):
        return f"WDATA(STRB={packet.get_strobe_pattern()}, LAST={packet.last})"
    elif isinstance(packet, AXIWriteResponsePacket):
        return f"WRESP(ID={packet.id:02X}, RESP={packet.get_response_name()})"
    elif isinstance(packet, InterruptPacket):
        # Updated to include protocol
        return f"INTR({packet.get_protocol_name()}.{packet.get_packet_type_name()}.{packet.get_event_code_name()}, CH={packet.channel_id:02X})"
    elif isinstance(packet, MonitorConfigPacket):
        features = ','.join(packet.get_enabled_features())
        return f"CONFIG({features})"
    else:
        return f"UNKNOWN({type(packet).__name__})"


def create_axi_interrupt_packet(packet_type: InterruptPacketType, event_code: MonitorEventCode,
                               channel_id: int = 0, unit_id: int = 9, agent_id: int = 99,
                               address_or_data: int = 0) -> InterruptPacket:
    """Helper function to create AXI-specific interrupt packets (new)"""
    packet = InterruptPacket()
    packet.packet_type = packet_type.value
    packet.protocol = ProtocolType.AXI.value
    packet.event_code = event_code.value
    packet.channel_id = channel_id & 0x3F
    packet.unit_id = unit_id & 0xF
    packet.agent_id = agent_id & 0xFF
    packet.data = address_or_data & 0xFFFFFFFFF  # 36 bits max
    packet.timestamp = time.time()
    return packet
