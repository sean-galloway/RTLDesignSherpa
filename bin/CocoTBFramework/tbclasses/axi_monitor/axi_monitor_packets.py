"""
AXI4/AXIL Monitor Packet Definitions - Clean Implementation

Comprehensive packet classes for AXI monitor verification, supporting:
- AXI4 and AXI-Lite transactions (AR, AW, R, W, B channels)
- Monitor interrupt bus packets
- Configuration and status packets
- Error and event reporting
- Performance metrics

These packets extend GAXIPacket and use field configurations for consistency
with the testbench framework.
"""

from typing import Optional, Dict, Any, List
from dataclasses import dataclass
from enum import Enum
import time

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class AXITransactionState(Enum):
    """AXI Transaction state tracking"""
    EMPTY = "empty"
    ADDR_PHASE = "addr_phase"
    DATA_PHASE = "data_phase"
    RESP_PHASE = "resp_phase"
    COMPLETE = "complete"
    ERROR = "error"
    ORPHANED = "orphaned"


class MonitorEventCode(Enum):
    """Monitor event codes matching RTL definitions"""
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
    """Interrupt bus packet types"""
    ERROR = 0x0
    COMPLETION = 0x1
    THRESHOLD = 0x2
    TIMEOUT = 0x3
    PERF = 0x4
    DEBUG = 0xF


class PerformanceMetric(Enum):
    """Performance metric types"""
    ADDR_LATENCY = 0x0
    DATA_LATENCY = 0x1
    RESP_LATENCY = 0x2
    TOTAL_LATENCY = 0x3
    THROUGHPUT = 0x4
    ERROR_RATE = 0x5
    ACTIVE_COUNT = 0x6
    COMPLETED_COUNT = 0x7
    ERROR_COUNT = 0x8


# =============================================================================
# Field Configuration Functions
# =============================================================================

def create_axi_command_field_config(id_width: int = 8, addr_width: int = 32, user_width: int = 1) -> FieldConfig:
    """Create AXI address channel field configuration (AR/AW)"""
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
    """Create AXI read data channel field configuration (R)"""
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
    """Create AXI write data channel field configuration (W)"""
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
    """Create AXI write response channel field configuration (B)"""
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


def create_interrupt_packet_field_config() -> FieldConfig:
    """Create interrupt bus packet field configuration (64-bit)"""
    config = FieldConfig()

    config.add_field(FieldDefinition(
        name="packet_type", bits=4, format="hex",
        description="Packet type (error, completion, etc.)"
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
        name="data", bits=38, format="hex",
        description="Event data (address, metric, etc.)"
    ))

    return config


def create_monitor_config_field_config() -> FieldConfig:
    """Create monitor configuration field configuration"""
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
# AXI Packet Classes
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

    def get_burst_type_name(self) -> str:
        """Get human-readable burst type name"""
        burst_map = {0: "FIXED", 1: "INCR", 2: "WRAP"}
        return burst_map.get(self.burst, f"UNKNOWN({self.burst})")

    def calculate_total_bytes(self) -> int:
        """Calculate total bytes in this transaction"""
        bytes_per_beat = 1 << self.size
        num_beats = self.len + 1
        return bytes_per_beat * num_beats

    def calculate_end_address(self) -> int:
        """Calculate end address of this transaction"""
        return self.addr + self.calculate_total_bytes() - 1

    def will_cross_boundary(self, boundary_size: int) -> bool:
        """Check if transaction crosses a boundary"""
        start_boundary = self.addr // boundary_size
        end_boundary = self.calculate_end_address() // boundary_size
        return start_boundary != end_boundary


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


class InterruptPacket(GAXIPacket):
    """Monitor Interrupt Bus packet (64-bit consolidated format)"""

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
        """Create packet from 64-bit interrupt bus value"""
        return cls(
            packet_type=(value >> 60) & 0xF,
            event_code=(value >> 56) & 0xF,
            channel_id=(value >> 50) & 0x3F,
            unit_id=(value >> 46) & 0xF,
            agent_id=(value >> 38) & 0xFF,
            data=value & 0x3FFFFFFFFF  # 38 bits
        )

    def to_64bit_value(self) -> int:
        """Convert packet to 64-bit interrupt bus value"""
        return (
            (self.packet_type << 60) |
            (self.event_code << 56) |
            (self.channel_id << 50) |
            (self.unit_id << 46) |
            (self.agent_id << 38) |
            (self.data & 0x3FFFFFFFFF)
        )

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        type_map = {
            0x0: "ERROR",
            0x1: "COMPLETION", 
            0x2: "THRESHOLD",
            0x3: "TIMEOUT",
            0x4: "PERF",
            0xF: "DEBUG"
        }
        return type_map.get(self.packet_type, f"UNKNOWN({self.packet_type:X})")

    def get_event_code_name(self) -> str:
        """Get human-readable event code name"""
        try:
            event = MonitorEventCode(self.event_code)
            return event.name
        except ValueError:
            return f"UNKNOWN({self.event_code:X})"

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

    def get_address_value(self, addr_width: int = 32) -> int:
        """Extract address value from data field"""
        return self.data & ((1 << addr_width) - 1)

    def get_metric_value(self) -> int:
        """Extract metric value from data field"""
        return self.data


class MonitorConfigPacket(GAXIPacket):
    """Monitor Configuration packet"""

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
# Transaction Tracking
# =============================================================================

@dataclass
class MonitoredTransaction:
    """Complete monitored AXI transaction with all phases"""

    # Transaction identification
    transaction_id: int
    is_read: bool
    is_axi4: bool  # True for AXI4, False for AXI-Lite

    # Address phase
    address_packet: Optional[AXICommandPacket] = None
    address_timestamp: Optional[float] = None

    # Data phase
    data_packets: List = None  # List[AXIReadDataPacket] or List[AXIWriteDataPacket]
    data_timestamps: List[float] = None

    # Response phase (write only)
    response_packet: Optional[AXIWriteResponsePacket] = None
    response_timestamp: Optional[float] = None

    # Transaction state
    state: AXITransactionState = AXITransactionState.EMPTY
    start_time: float = 0.0
    completion_time: Optional[float] = None

    # Error tracking
    errors: List[str] = None
    events: List[InterruptPacket] = None

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

    def add_data_packet(self, packet, timestamp: float):
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
        protocol = "AXI4" if self.is_axi4 else "AXI-Lite"
        beats = f"{self.get_actual_data_beats()}/{self.get_expected_data_beats()}"
        
        summary = f"{protocol} {txn_type} ID={self.transaction_id:02X} "
        summary += f"state={self.state.value} beats={beats}"
        
        if self.has_errors():
            summary += f" errors={len(self.errors)}"
        
        if self.total_latency:
            summary += f" latency={self.total_latency:.1f}ns"
            
        return summary


# =============================================================================
# Conversion Functions
# =============================================================================

def convert_gaxi_to_axi_address(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXICommandPacket:
    """Convert GAXI packet to AXI address packet"""
    packet_data = {}
    for field_name in ['id', 'addr', 'len', 'size', 'burst', 'lock', 'cache', 'prot', 'qos', 'region', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)
    return AXICommandPacket.from_dict(packet_data, field_config)


def convert_gaxi_to_axi_read_data(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIReadDataPacket:
    """Convert GAXI packet to AXI read data packet"""
    packet_data = {}
    for field_name in ['id', 'data', 'resp', 'last', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)
    return AXIReadDataPacket.from_dict(packet_data, field_config)


def convert_gaxi_to_axi_write_data(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIWriteDataPacket:
    """Convert GAXI packet to AXI write data packet"""
    packet_data = {}
    for field_name in ['data', 'strb', 'last', 'user']:
        if hasattr(gaxi_packet, field_name):
            packet_data[field_name] = getattr(gaxi_packet, field_name)
    return AXIWriteDataPacket.from_dict(packet_data, field_config)


def convert_gaxi_to_axi_write_response(gaxi_packet, field_config: Optional[FieldConfig] = None) -> AXIWriteResponsePacket:
    """Convert GAXI packet to AXI write response packet"""
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
    """Convert raw 64-bit value to interrupt packet"""
    return InterruptPacket.from_64bit_value(raw_value)


# =============================================================================
# Utility Functions
# =============================================================================

def create_default_config_packet(**overrides) -> MonitorConfigPacket:
    """Create a monitor configuration packet with default values"""
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
    """Validate packet field consistency and return list of issues"""
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
        # Validate interrupt packet
        if packet.packet_type > 0xF:
            issues.append(f"Invalid packet type: {packet.packet_type:X}")
        if packet.event_code > 0xF:
            issues.append(f"Invalid event code: {packet.event_code:X}")
        if packet.channel_id > 0x3F:
            issues.append(f"Invalid channel ID: {packet.channel_id:X}")
    
    return issues


def format_packet_summary(packet) -> str:
    """Generate a concise summary string for any packet type"""
    if isinstance(packet, AXICommandPacket):
        return f"CMD(ID={packet.id:02X}, ADDR=0x{packet.addr:X}, LEN={packet.len})"
    elif isinstance(packet, AXIReadDataPacket):
        return f"RDATA(ID={packet.id:02X}, RESP={packet.get_response_name()}, LAST={packet.last})"
    elif isinstance(packet, AXIWriteDataPacket):
        return f"WDATA(STRB={packet.get_strobe_pattern()}, LAST={packet.last})"
    elif isinstance(packet, AXIWriteResponsePacket):
        return f"WRESP(ID={packet.id:02X}, RESP={packet.get_response_name()})"
    elif isinstance(packet, InterruptPacket):
        return f"INTR({packet.get_packet_type_name()}.{packet.get_event_code_name()}, CH={packet.channel_id:02X})"
    elif isinstance(packet, MonitorConfigPacket):
        features = ','.join(packet.get_enabled_features())
        return f"CONFIG({features})"
    else:
        return f"UNKNOWN({type(packet).__name__})"
