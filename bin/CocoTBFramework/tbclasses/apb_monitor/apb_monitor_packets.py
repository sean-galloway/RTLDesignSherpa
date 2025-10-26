# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBTransactionState
# Purpose: APB Monitor Packet Definitions - FIXED VERSION
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Monitor Packet Definitions - FIXED VERSION

Defines packet classes for APB monitor validation including CMD, RSP interfaces
and monitor bus packets. Uses consistent definitions from monbus_components framework.

CHANGES:
- Removed redundant APBMonitorEventType enum (use MonbusPktType instead)
- Updated APBMonitorEvent to use integer packet types from monbus_components
- Consistent use of factory functions from monbus_components
- All packet type comparisons now use integer values
"""

import time
from typing import Optional, Dict, Any, List
from dataclasses import dataclass
from enum import Enum

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition

# Import monitor bus components - SINGLE SOURCE OF TRUTH
from CocoTBFramework.tbclasses.misc.monbus_components import (
    MonbusPacket, MonbusProtocol, MonbusPktType,
    APBErrorCode, APBTimeoutCode, APBCompletionCode,
    APBPerformanceCode, APBThresholdCode, APBDebugCode,
    create_apb_error_event, create_apb_completion_event, 
    create_apb_timeout_event, create_apb_performance_event,
    create_apb_debug_event
)

# Import the APB-GAXI field configurations
from CocoTBFramework.tbclasses.apb.apbgaxiconfig import APBGAXIConfig


class APBTransactionState(Enum):
    """APB Transaction state tracking"""
    IDLE = "idle"
    CMD_SENT = "cmd_sent"
    RSP_PENDING = "rsp_pending"
    COMPLETE = "complete"
    ERROR = "error"
    TIMEOUT = "timeout"


# REMOVED: APBMonitorEventType enum - use MonbusPktType from monbus_components instead


class APBCommandPacket(GAXIPacket):
    """APB Command interface packet using APBGAXIConfig"""

    def __init__(self, field_config: Optional[FieldConfig] = None,
                 addr_width: int = 32, data_width: int = 32, **kwargs):
        if field_config is None:
            # Use APBGAXIConfig to create proper field configuration
            apb_config = APBGAXIConfig(addr_width=addr_width, data_width=data_width)
            field_config = apb_config.create_cmd_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def create_with_config(cls, addr_width: int = 32, data_width: int = 32, **kwargs):
        """Create packet with specific address and data widths"""
        return cls(addr_width=addr_width, data_width=data_width, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], addr_width: int = 32, data_width: int = 32):
        """Create packet from dictionary with configurable widths"""
        return cls.create_with_config(addr_width=addr_width, data_width=data_width, **data)

    def is_write(self) -> bool:
        """Check if this is a write command"""
        return bool(getattr(self, 'pwrite', 0))

    def is_read(self) -> bool:
        """Check if this is a read command"""
        return not self.is_write()

    def get_address(self) -> int:
        """Get the address value"""
        return getattr(self, 'paddr', 0)

    def get_write_data(self) -> int:
        """Get the write data value"""
        return getattr(self, 'pwdata', 0) if hasattr(self, 'pwdata') else 0

    def get_strobe_mask(self) -> int:
        """Get the byte strobe mask"""
        return getattr(self, 'pstrb', 0) if hasattr(self, 'pstrb') else 0

    def get_strobe_pattern(self) -> str:
        """Get formatted strobe pattern"""
        strb = self.get_strobe_mask()
        return f"0x{strb:X}"

    def get_protection_type(self) -> str:
        """Get human-readable protection type"""
        pprot = getattr(self, 'pprot', 0)

        # Use the encoding from APBGAXIConfig
        prot_map = {
            0b000: "NORMAL",
            0b001: "PRIVILEGED",
            0b010: "NONSECURE",
            0b011: "PRIV_NONSECURE",
            0b100: "INSTR",
            0b101: "PRIV_INSTR",
            0b110: "NONSECURE_INSTR",
            0b111: "PRIV_NONSECURE_INSTR"
        }
        return prot_map.get(pprot, f"UNKNOWN({pprot:03b})")

    def get_protection_flags(self) -> Dict[str, bool]:
        """Get individual protection flags"""
        pprot = getattr(self, 'pprot', 0)
        return {
            'privileged': bool(pprot & 0x1),
            'nonsecure': bool(pprot & 0x2),
            'instruction': bool(pprot & 0x4)
        }

    def is_secure_access(self) -> bool:
        """Check if this is a secure access (PPROT[1] == 0)"""
        pprot = getattr(self, 'pprot', 0)
        return not bool(pprot & 0x2)

    def is_privileged_access(self) -> bool:
        """Check if this is a privileged access (PPROT[0] == 1)"""
        pprot = getattr(self, 'pprot', 0)
        return bool(pprot & 0x1)

    def get_active_byte_lanes(self) -> List[int]:
        """Get list of active byte lane indices based on strobe"""
        strb = self.get_strobe_mask()
        active_lanes = []
        for i in range(8):  # Support up to 64-bit data
            if strb & (1 << i):
                active_lanes.append(i)
        return active_lanes

    def validate_strobe_alignment(self, data_width: int = 32) -> List[str]:
        """Validate strobe alignment with address and data width"""
        errors = []
        addr = self.get_address()
        strb = self.get_strobe_mask()

        # Check strobe doesn't exceed data width
        max_strb = (1 << (data_width // 8)) - 1
        if strb > max_strb:
            errors.append(f"Strobe 0x{strb:X} exceeds data width {data_width} bits")

        # Check alignment for narrow transfers
        byte_addr = addr & ((data_width // 8) - 1)
        if self.is_write() and strb != 0:
            # For writes, check that strobes align with address
            active_lanes = self.get_active_byte_lanes()
            if active_lanes and min(active_lanes) < byte_addr:
                errors.append(f"Strobe pattern 0x{strb:X} misaligned with address 0x{addr:X}")

        return errors

    def __str__(self) -> str:
        """String representation"""
        op_type = "WRITE" if self.is_write() else "READ"
        addr_str = f"0x{self.get_address():08X}"

        if self.is_write():
            data_str = f" DATA=0x{self.get_write_data():08X}"
            strb_str = f" STRB={self.get_strobe_pattern()}"
        else:
            data_str = ""
            strb_str = ""

        prot_str = f" PROT={self.get_protection_type()}"

        return f"APB_CMD({op_type} ADDR={addr_str}{data_str}{strb_str}{prot_str})"


class APBResponsePacket(GAXIPacket):
    """APB Response interface packet using APBGAXIConfig"""

    def __init__(self, field_config: Optional[FieldConfig] = None,
                 data_width: int = 32, **kwargs):
        if field_config is None:
            # Use APBGAXIConfig to create proper field configuration
            apb_config = APBGAXIConfig(data_width=data_width)
            field_config = apb_config.create_rsp_field_config()

        self.timestamp = kwargs.pop('timestamp', time.time())
        super().__init__(field_config, **kwargs)

    @classmethod
    def create_with_config(cls, data_width: int = 32, **kwargs):
        """Create packet with specific data width"""
        return cls(data_width=data_width, **kwargs)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], data_width: int = 32):
        """Create packet from dictionary with configurable width"""
        return cls.create_with_config(data_width=data_width, **data)

    def is_error(self) -> bool:
        """Check if this response indicates an error"""
        return bool(getattr(self, 'pslverr', 0))

    def is_ok(self) -> bool:
        """Check if this response is OK"""
        return not self.is_error()

    def get_read_data(self) -> int:
        """Get the read data value"""
        return getattr(self, 'prdata', 0) if hasattr(self, 'prdata') else 0

    def get_error_status(self) -> str:
        """Get human-readable error status"""
        return "ERROR" if self.is_error() else "OK"

    def get_response_code(self) -> APBErrorCode:
        """Get corresponding APB error code for this response"""
        if self.is_error():
            return APBErrorCode.PSLVERR
        else:
            return None

    def __str__(self) -> str:
        """String representation"""
        data_str = f"DATA=0x{self.get_read_data():08X}"
        status_str = f"STATUS={self.get_error_status()}"
        return f"APB_RSP({data_str} {status_str})"


@dataclass
class APBTransaction:
    """Complete APB transaction combining command and response"""

    # Transaction identification
    transaction_id: int
    timestamp_start: float

    # Command phase
    cmd_packet: Optional[APBCommandPacket] = None
    cmd_timestamp: Optional[float] = None

    # Response phase
    rsp_packet: Optional[APBResponsePacket] = None
    rsp_timestamp: Optional[float] = None

    # Transaction state
    state: APBTransactionState = APBTransactionState.IDLE
    completion_time: Optional[float] = None

    # Error tracking
    errors: Optional[List[str]] = None
    monitor_events: Optional[List[MonbusPacket]] = None

    # Performance metrics
    cmd_to_rsp_latency: Optional[float] = None
    total_latency: Optional[float] = None

    # APB-specific tracking
    setup_time: Optional[float] = None
    access_time: Optional[float] = None
    enable_time: Optional[float] = None

    def __post_init__(self):
        """Initialize mutable default values"""
        if self.errors is None:
            self.errors = []
        if self.monitor_events is None:
            self.monitor_events = []

    def add_command(self, cmd_packet: APBCommandPacket, timestamp: float):
        """Add command packet to transaction"""
        self.cmd_packet = cmd_packet
        self.cmd_timestamp = timestamp
        self.state = APBTransactionState.CMD_SENT

    def add_response(self, rsp_packet: APBResponsePacket, timestamp: float):
        """Add response packet to transaction"""
        self.rsp_packet = rsp_packet
        self.rsp_timestamp = timestamp

        if rsp_packet.is_error():
            self.state = APBTransactionState.ERROR
        else:
            self.state = APBTransactionState.COMPLETE

        self.completion_time = timestamp

        # Calculate latencies
        if self.cmd_timestamp and self.rsp_timestamp:
            self.cmd_to_rsp_latency = self.rsp_timestamp - self.cmd_timestamp

        if self.completion_time:
            self.total_latency = self.completion_time - self.timestamp_start

    def add_error(self, error: str):
        """Add an error to this transaction"""
        self.errors.append(error)
        if self.state not in [APBTransactionState.ERROR, APBTransactionState.COMPLETE]:
            self.state = APBTransactionState.ERROR

    def add_monitor_event(self, event: MonbusPacket):
        """Add a monitor bus event to this transaction"""
        self.monitor_events.append(event)

    def mark_timeout(self):
        """Mark transaction as timed out"""
        self.state = APBTransactionState.TIMEOUT
        self.add_error("Transaction timeout")

    def is_complete(self) -> bool:
        """Check if transaction is complete"""
        return self.state in [APBTransactionState.COMPLETE, APBTransactionState.ERROR, APBTransactionState.TIMEOUT]

    def has_errors(self) -> bool:
        """Check if transaction has errors"""
        return len(self.errors) > 0 or self.state in [APBTransactionState.ERROR, APBTransactionState.TIMEOUT]

    def is_write_transaction(self) -> bool:
        """Check if this is a write transaction"""
        return self.cmd_packet is not None and self.cmd_packet.is_write()

    def is_read_transaction(self) -> bool:
        """Check if this is a read transaction"""
        return self.cmd_packet is not None and self.cmd_packet.is_read()

    def get_address(self) -> Optional[int]:
        """Get transaction address"""
        return self.cmd_packet.get_address() if self.cmd_packet else None

    def get_data_value(self) -> Optional[int]:
        """Get transaction data (write data or read data)"""
        if self.is_write_transaction():
            return self.cmd_packet.get_write_data()
        elif self.rsp_packet:
            return self.rsp_packet.get_read_data()
        return None

    def get_apb_phases(self) -> Dict[str, Optional[float]]:
        """Get APB phase timing information"""
        return {
            'setup': self.setup_time,
            'access': self.access_time,
            'enable': self.enable_time
        }

    def validate_transaction(self) -> List[str]:
        """Validate the complete transaction"""
        errors = []

        # Basic transaction completeness
        if not self.cmd_packet:
            errors.append("Missing command packet")
        if not self.rsp_packet and self.state != APBTransactionState.TIMEOUT:
            errors.append("Missing response packet")

        # Validate command packet if present
        if self.cmd_packet:
            cmd_errors = self.cmd_packet.validate_strobe_alignment()
            errors.extend(cmd_errors)

        # Validate response matches command expectation
        if self.cmd_packet and self.rsp_packet:
            if self.is_read_transaction() and self.rsp_packet.get_read_data() == 0:
                # This might be OK, but worth noting
                pass

        # Check timing constraints
        if self.total_latency and self.total_latency < 0:
            errors.append("Negative latency detected")

        return errors

    def get_transaction_summary(self) -> str:
        """Get a summary string for this transaction"""
        if not self.cmd_packet:
            return f"APB_TXN(ID={self.transaction_id:02X} INCOMPLETE)"

        op_type = "WRITE" if self.is_write_transaction() else "READ"
        addr_str = f"0x{self.get_address():08X}" if self.get_address() is not None else "N/A"

        summary = f"APB_TXN(ID={self.transaction_id:02X} {op_type} ADDR={addr_str} STATE={self.state.value}"

        if self.has_errors():
            summary += f" ERRORS={len(self.errors)}"

        if self.total_latency is not None:
            summary += f" LATENCY={self.total_latency:.1f}ns"

        if self.get_data_value() is not None:
            summary += f" DATA=0x{self.get_data_value():08X}"

        summary += ")"
        return summary


class APBMonitorEvent:
    """Expected monitor event for validation - FIXED to use MonbusPktType"""

    def __init__(self, packet_type: int, event_code: int,
                 expected_data: Optional[int] = None, tolerance_ns: float = 10.0):
        # Use integer packet types from MonbusPktType (not string-based types)
        self.packet_type = packet_type  # e.g., MonbusPktType.ERROR.value
        self.event_code = event_code
        self.expected_data = expected_data
        self.tolerance_ns = tolerance_ns
        self.timestamp_expected = None
        self.found_event = None

    @classmethod
    def create_error_event(cls, error_code: APBErrorCode, expected_addr: int = None, **kwargs):
        """Create error event expectation using proper enum"""
        return cls(MonbusPktType.ERROR.value, error_code.value, expected_addr, **kwargs)

    @classmethod
    def create_timeout_event(cls, timeout_code: APBTimeoutCode, expected_addr: int = None, **kwargs):
        """Create timeout event expectation using proper enum"""
        return cls(MonbusPktType.TIMEOUT.value, timeout_code.value, expected_addr, **kwargs)

    @classmethod
    def create_completion_event(cls, completion_code: APBCompletionCode, expected_addr: int = None, **kwargs):
        """Create completion event expectation using proper enum"""
        return cls(MonbusPktType.COMPLETION.value, completion_code.value, expected_addr, **kwargs)

    @classmethod
    def create_performance_event(cls, perf_code: APBPerformanceCode, expected_data: int = None, **kwargs):
        """Create performance event expectation using proper enum"""
        return cls(MonbusPktType.PERF.value, perf_code.value, expected_data, **kwargs)

    @classmethod
    def create_debug_event(cls, debug_code: APBDebugCode, expected_data: int = None, **kwargs):
        """Create debug event expectation using proper enum"""
        return cls(MonbusPktType.DEBUG.value, debug_code.value, expected_data, **kwargs)

    def matches_packet(self, packet: MonbusPacket) -> bool:
        """Check if a monitor packet matches this expected event"""
        # Check protocol
        if packet.protocol != MonbusProtocol.APB.value:
            return False

        # Check packet type (now using integer comparison)
        if packet.packet_type != self.packet_type:
            return False

        # Check event code
        if packet.event_code != self.event_code:
            return False

        # Check data if specified
        if self.expected_data is not None:
            # For address-based events, compare lower 32 bits
            packet_addr = packet.data & 0xFFFFFFFF
            if packet_addr != (self.expected_data & 0xFFFFFFFF):
                return False

        return True

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        try:
            return MonbusPktType(self.packet_type).name
        except ValueError:
            return f"UNKNOWN_{self.packet_type}"

    def get_event_code_name(self) -> str:
        """Get human-readable event code name"""
        # Use the helper function from monbus_components
        from CocoTBFramework.tbclasses.misc.monbus_components import get_event_code_name
        return get_event_code_name(MonbusProtocol.APB.value, self.packet_type, self.event_code)

    def __str__(self) -> str:
        """String representation"""
        data_str = f" DATA=0x{self.expected_data:08X}" if self.expected_data is not None else ""
        return f"APB_MONITOR_EVENT({self.get_packet_type_name()}.{self.get_event_code_name()}{data_str})"


# Utility functions leveraging APBGAXIConfig
def create_apb_write_cmd(addr: int, data: int, strb: int = None, prot: int = 0,
                        addr_width: int = 32, data_width: int = 32) -> APBCommandPacket:
    """Create an APB write command packet using APBGAXIConfig"""
    if strb is None:
        strb = (1 << (data_width // 8)) - 1  # All strobes enabled

    return APBCommandPacket.create_with_config(
        addr_width=addr_width,
        data_width=data_width,
        pwrite=1,
        paddr=addr,
        pwdata=data,
        pstrb=strb,
        pprot=prot
    )


def create_apb_read_cmd(addr: int, prot: int = 0,
                       addr_width: int = 32, data_width: int = 32) -> APBCommandPacket:
    """Create an APB read command packet using APBGAXIConfig"""
    return APBCommandPacket.create_with_config(
        addr_width=addr_width,
        data_width=data_width,
        pwrite=0,
        paddr=addr,
        pwdata=0,
        pstrb=0,
        pprot=prot
    )


def create_apb_ok_rsp(data: int = 0, data_width: int = 32) -> APBResponsePacket:
    """Create an APB OK response packet using APBGAXIConfig"""
    return APBResponsePacket.create_with_config(
        data_width=data_width,
        prdata=data,
        pslverr=0
    )


def create_apb_error_rsp(data: int = 0, data_width: int = 32) -> APBResponsePacket:
    """Create an APB error response packet using APBGAXIConfig"""
    return APBResponsePacket.create_with_config(
        data_width=data_width,
        prdata=data,
        pslverr=1
    )


def create_configurable_apb_cmd(addr_width: int = 32, data_width: int = 32, **kwargs) -> APBCommandPacket:
    """Create APB command with configurable field widths"""
    return APBCommandPacket.create_with_config(addr_width=addr_width, data_width=data_width, **kwargs)


def create_configurable_apb_rsp(data_width: int = 32, **kwargs) -> APBResponsePacket:
    """Create APB response with configurable field widths"""
    return APBResponsePacket.create_with_config(data_width=data_width, **kwargs)


def validate_packet_consistency(packet) -> List[str]:
    """Validate packet field consistency and return list of issues"""
    issues = []

    if isinstance(packet, APBCommandPacket):
        # Validate command packet
        if hasattr(packet, 'paddr') and packet.paddr < 0:
            issues.append(f"Invalid address: {packet.paddr}")

        if hasattr(packet, 'pwrite') and packet.pwrite not in [0, 1]:
            issues.append(f"Invalid pwrite value: {packet.pwrite}")

        if hasattr(packet, 'pprot') and packet.pprot > 7:
            issues.append(f"Invalid pprot value: {packet.pprot}")

        # Check strobe alignment for writes
        if packet.is_write():
            strb_errors = packet.validate_strobe_alignment()
            issues.extend(strb_errors)

    elif isinstance(packet, APBResponsePacket):
        # Validate response packet
        if hasattr(packet, 'pslverr') and packet.pslverr not in [0, 1]:
            issues.append(f"Invalid pslverr value: {packet.pslverr}")

    return issues


def format_packet_summary(packet) -> str:
    """Generate a concise summary string for any packet type"""
    if isinstance(packet, APBCommandPacket):
        return str(packet)
    elif isinstance(packet, APBResponsePacket):
        return str(packet)
    elif isinstance(packet, MonbusPacket):
        return f"MONBUS({packet.get_protocol_name()}.{packet.get_packet_type_name()}.{packet.get_event_code_name()})"
    else:
        return f"UNKNOWN({type(packet).__name__})"


def create_apb_transaction_from_packets(cmd: APBCommandPacket, rsp: APBResponsePacket = None,
                                       transaction_id: int = 0) -> APBTransaction:
    """Create an APB transaction from command and optional response packets"""
    txn = APBTransaction(
        transaction_id=transaction_id,
        timestamp_start=cmd.timestamp if hasattr(cmd, 'timestamp') else time.time()
    )

    txn.add_command(cmd, cmd.timestamp if hasattr(cmd, 'timestamp') else time.time())

    if rsp:
        txn.add_response(rsp, rsp.timestamp if hasattr(rsp, 'timestamp') else time.time())

    return txn
