"""
Monitor Bus Components - Fixed Version

Fix for the stats attribute error in MonbusSlave.
The issue was that GAXISlave expects stats to be an object with attributes,
but we were using a dictionary.
"""

import asyncio
import random
from typing import Dict, List, Optional, Callable, Any
from enum import Enum

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class MonbusPktType(Enum):
    """Monitor bus packet types"""
    ERROR = 0x0
    COMPLETION = 0x1
    THRESHOLD = 0x2
    TIMEOUT = 0x3
    PERF = 0x4
    DEBUG = 0xF


class MonbusEventCode(Enum):
    """Monitor bus event codes"""
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


class MonbusStats:
    """Stats object compatible with GAXISlave expectations"""
    
    def __init__(self):
        # Standard GAXISlave stats
        self.received_transactions = 0
        self.transactions_observed = 0
        self.packets_sent = 0
        self.packets_received = 0
        self.bytes_sent = 0
        self.bytes_received = 0
        self.errors = 0
        self.timeouts = 0
        
        # MonbusSlave specific stats
        self.total_packets = 0
        self.error_packets = 0
        self.completion_packets = 0
        self.timeout_packets = 0
        self.performance_packets = 0
        self.debug_packets = 0
        self.unknown_packets = 0
        self.verification_errors = 0


class MonbusPacket(GAXIPacket):
    """Structured representation of a 64-bit monitor bus packet using GAXIPacket framework"""

    def __init__(self, field_config: Optional[FieldConfig] = None, **kwargs):
        """Initialize MonbusPacket with proper field configuration"""
        if field_config is None:
            field_config = create_monbus_structured_field_config()

        # Initialize timestamp
        self.timestamp = kwargs.pop('timestamp', 0.0)

        # Call parent constructor
        super().__init__(field_config, **kwargs)

    @classmethod
    def from_64bit(cls, value: int, timestamp: float = 0.0) -> 'MonbusPacket':
        """Create packet from 64-bit value"""
        packet = cls(timestamp=timestamp)
        packet.unpack_from_64bit(value)
        return packet

    def unpack_from_64bit(self, value: int):
        """Unpack 64-bit value into packet fields"""
        self.packet_type = (value >> 60) & 0xF
        self.event_code = (value >> 56) & 0xF
        self.channel_id = (value >> 50) & 0x3F
        self.unit_id = (value >> 46) & 0xF
        self.agent_id = (value >> 38) & 0xFF
        self.data = value & 0x3FFFFFFFFF  # 38 bits
        self.raw_value = value

    def to_64bit(self) -> int:
        """Convert packet to 64-bit value"""
        return (
            (self.packet_type << 60) |
            (self.event_code << 56) |
            (self.channel_id << 50) |
            (self.unit_id << 46) |
            (self.agent_id << 38) |
            (self.data & 0x3FFFFFFFFF)
        )

    @property
    def raw_value(self) -> int:
        """Get the raw 64-bit value"""
        return self.to_64bit()

    @raw_value.setter
    def raw_value(self, value: int):
        """Set from raw 64-bit value"""
        self.unpack_from_64bit(value)

    def get_packet_type_name(self) -> str:
        """Get human-readable packet type name"""
        try:
            return MonbusPktType(self.packet_type).name
        except ValueError:
            return f"UNKNOWN_TYPE_{self.packet_type:X}"

    def get_event_code_name(self) -> str:
        """Get human-readable event code name"""
        try:
            return MonbusEventCode(self.event_code).name
        except ValueError:
            return f"UNKNOWN_EVENT_{self.event_code:X}"

    def is_error_packet(self) -> bool:
        """Check if this is an error packet"""
        return self.packet_type == MonbusPktType.ERROR.value

    def is_timeout_packet(self) -> bool:
        """Check if this is a timeout packet"""
        return self.packet_type == MonbusPktType.TIMEOUT.value

    def is_completion_packet(self) -> bool:
        """Check if this is a completion packet"""
        return self.packet_type == MonbusPktType.COMPLETION.value

    def is_performance_packet(self) -> bool:
        """Check if this is a performance packet"""
        return self.packet_type == MonbusPktType.PERF.value

    def get_address_value(self, addr_width: int = 32) -> int:
        """Extract address value from data field"""
        return self.data & ((1 << addr_width) - 1)

    def get_metric_value(self) -> int:
        """Extract metric value from data field"""
        return self.data

    def __str__(self) -> str:
        """String representation with monitor-specific formatting"""
        base_str = super().__str__()

        # Add monitor-specific summary
        summary = (f"MonbusPacket: {self.get_packet_type_name()}.{self.get_event_code_name()} "
                  f"ch={self.channel_id:02X} unit={self.unit_id:X} agent={self.agent_id:02X} "
                  f"data=0x{self.data:010X}")

        if hasattr(self, 'timestamp') and self.timestamp > 0:
            summary += f" @{self.timestamp:.1f}ns"

        return f"{summary}\n{base_str}"


def create_monbus_field_config() -> FieldConfig:
    """Create field configuration for monitor bus packets (single 64-bit field)"""
    config = FieldConfig()

    # Single 64-bit field for the consolidated packet
    config.add_field(FieldDefinition(
        name="packet", bits=64, format="hex",
        description="Consolidated 64-bit monitor packet"
    ))

    return config


def create_monbus_structured_field_config() -> FieldConfig:
    """Create structured field configuration for monitor bus packets"""
    config = FieldConfig()

    # Add individual fields that make up the 64-bit packet
    config.add_field(FieldDefinition(
        name="packet_type", bits=4, format="hex",
        description="Packet type (error, completion, etc.)",
        encoding={
            0x0: "ERROR",
            0x1: "COMPLETION",
            0x2: "THRESHOLD",
            0x3: "TIMEOUT",
            0x4: "PERF",
            0xF: "DEBUG"
        }
    ))

    config.add_field(FieldDefinition(
        name="event_code", bits=4, format="hex",
        description="Event/error code",
        encoding={
            0x0: "NONE",
            0x1: "CMD_TIMEOUT",
            0x2: "DATA_TIMEOUT",
            0x3: "RESP_TIMEOUT",
            0x4: "RESP_ERROR",
            0x5: "RESP_SLVERR",
            0x6: "RESP_DECERR",
            0x7: "DATA_ORPHAN",
            0x8: "RESP_ORPHAN",
            0x9: "PROTOCOL",
            0xA: "TRANS_COMPLETE",
            0xB: "ADDR_MISS_T0",
            0xC: "ADDR_MISS_T1",
            0xF: "USER_DEFINED"
        }
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
        name="data", bits=38, format="hex",
        description="Event data (address, metric, etc.)"
    ))

    # Add timestamp as a separate tracking field (not part of 64-bit packet)
    config.add_field(FieldDefinition(
        name="timestamp", bits=64, format="dec",
        description="Capture timestamp (ns)"
    ))

    # Add raw_value as a computed field
    config.add_field(FieldDefinition(
        name="raw_value", bits=64, format="hex",
        description="Complete 64-bit packet value"
    ))

    return config


class MonbusMaster(GAXIMaster):
    """
    Monitor Bus Master - Sends monitor packets TO DUT

    This would be used in scenarios where you want to inject monitor
    packets into a DUT that processes them (rare, but included for completeness).
    """

    def __init__(self, dut, title: str = "MonbusMaster", prefix: str = "",
                 unit_id: int = 9, agent_id: int = 99, **kwargs):

        # Create field configuration
        field_config = create_monbus_field_config()

        # Set default parameters for monitor bus
        kwargs.setdefault('bus_name', 'monbus')
        kwargs.setdefault('pkt_prefix', '')
        kwargs.setdefault('mode', 'skid')
        kwargs.setdefault('multi_sig', False)
        kwargs.setdefault('timeout_cycles', 1000)

        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            field_config=field_config,
            **kwargs
        )

        self.unit_id = unit_id & 0xF  # 4 bits
        self.agent_id = agent_id & 0xFF  # 8 bits
        self.packet_count = 0
        self.packets_sent = []

        self.log.info(f"{title} initialized - UNIT_ID={self.unit_id:X}, AGENT_ID={self.agent_id:02X}")

    async def send_error_packet(self, event_code: int, channel_id: int = 0,
                               address: int = 0) -> MonbusPacket:
        """Send an error packet"""
        packet = MonbusPacket(timestamp=get_sim_time('ns'))
        packet.packet_type = MonbusPktType.ERROR.value
        packet.event_code = event_code
        packet.channel_id = channel_id & 0x3F
        packet.unit_id = self.unit_id
        packet.agent_id = self.agent_id
        packet.data = address & 0x3FFFFFFFFF

        await self._send_packet(packet)
        return packet

    async def send_completion_packet(self, channel_id: int, address: int = 0) -> MonbusPacket:
        """Send a transaction completion packet"""
        packet = MonbusPacket(timestamp=get_sim_time('ns'))
        packet.packet_type = MonbusPktType.COMPLETION.value
        packet.event_code = MonbusEventCode.TRANS_COMPLETE.value
        packet.channel_id = channel_id & 0x3F
        packet.unit_id = self.unit_id
        packet.agent_id = self.agent_id
        packet.data = address & 0x3FFFFFFFFF

        await self._send_packet(packet)
        return packet

    async def send_timeout_packet(self, timeout_type: int, channel_id: int = 0,
                                    address: int = 0) -> MonbusPacket:
        """Send a timeout packet"""
        packet = MonbusPacket(timestamp=get_sim_time('ns'))
        packet.packet_type = MonbusPktType.TIMEOUT.value
        packet.event_code = timeout_type
        packet.channel_id = channel_id & 0x3F
        packet.unit_id = self.unit_id
        packet.agent_id = self.agent_id
        packet.data = address & 0x3FFFFFFFFF

        await self._send_packet(packet)
        return packet

    async def send_performance_packet(self, metric_type: int, metric_value: int,
                                        channel_id: int = 0) -> MonbusPacket:
        """Send a performance metric packet"""
        packet = MonbusPacket(timestamp=get_sim_time('ns'))
        packet.packet_type = MonbusPktType.PERF.value
        packet.event_code = metric_type
        packet.channel_id = channel_id & 0x3F
        packet.unit_id = self.unit_id
        packet.agent_id = self.agent_id
        packet.data = metric_value & 0x3FFFFFFFFF

        await self._send_packet(packet)
        return packet

    async def send_debug_packet(self, debug_type: int, debug_data: int,
                                channel_id: int = 0) -> MonbusPacket:
        """Send a debug packet"""
        packet = MonbusPacket(timestamp=get_sim_time('ns'))
        packet.packet_type = MonbusPktType.DEBUG.value
        packet.event_code = debug_type
        packet.channel_id = channel_id & 0x3F
        packet.unit_id = self.unit_id
        packet.agent_id = self.agent_id
        packet.data = debug_data & 0x3FFFFFFFFF

        await self._send_packet(packet)
        return packet

    async def _send_packet(self, monbus_packet: MonbusPacket):
        """Internal method to send a monitor bus packet"""
        # Create GAXI packet with single 64-bit field
        gaxi_packet = GAXIPacket(create_monbus_field_config())
        gaxi_packet.packet = monbus_packet.to_64bit()

        # Send packet
        await self.send(gaxi_packet)

        # Track sent packets
        self.packets_sent.append(monbus_packet)
        self.packet_count += 1

        if self.log:
            self.log.info(f"📤 SENT: {monbus_packet}")

    def get_statistics(self) -> Dict[str, Any]:
        """Get master statistics"""
        stats = {
            'packets_sent': self.packet_count,
            'last_packet_time': self.packets_sent[-1].timestamp if self.packets_sent else 0,
        }

        # Count by packet type
        type_counts = {}
        for packet in self.packets_sent:
            pkt_type = packet.get_packet_type_name()
            type_counts[pkt_type] = type_counts.get(pkt_type, 0) + 1

        stats['packet_type_counts'] = type_counts
        return stats


class MonbusSlave(GAXISlave):
    """
    Monitor Bus Slave - Receives monitor packets FROM DUT

    This is the primary component used in testbenches to receive and
    verify monitor packets generated by the AXI monitor.
    """

    def __init__(self, dut, title: str = "MonbusSlave",
                    prefix: str = "", pkt_prefix: str = "monbus",
                    expected_unit_id: Optional[int] = None,
                    expected_agent_id: Optional[int] = None, **kwargs):

        # Create field configuration
        field_config = create_monbus_field_config()

        # Set default parameters for monitor bus
        kwargs.setdefault('bus_name', 'monbus')
        kwargs.setdefault('pkt_prefix', '')
        kwargs.setdefault('mode', 'skid')
        kwargs.setdefault('multi_sig', False)
        kwargs.setdefault('timeout_cycles', 1000)

        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            in_prefix='',
            out_prefix='',
            field_config=field_config,
            **kwargs
        )

        # CRITICAL FIX: Replace the dictionary stats with MonbusStats object
        self.stats = MonbusStats()

        self.expected_unit_id = expected_unit_id
        self.expected_agent_id = expected_agent_id
        self.packet_count = 0
        self.packets_received = []
        self.packet_callbacks = []
        self.verification_errors = []

        self.log.info(f"{title} initialized for monitoring packets")
        if expected_unit_id is not None:
            self.log.info(f"  Expected UNIT_ID: {expected_unit_id:X}")
        if expected_agent_id is not None:
            self.log.info(f"  Expected AGENT_ID: {expected_agent_id:02X}")

    def add_packet_callback(self, callback: Callable[[MonbusPacket], None]):
        """Add callback function for received packets"""
        self.packet_callbacks.append(callback)

    async def start_monitoring(self):
        """Start monitoring for packets (non-blocking)"""
        self.log.info(f"{self.title} starting packet monitoring...")

        # Start the monitoring task
        cocotb.start_soon(self._monitor_packets())

    async def _monitor_packets(self):
        """Internal monitoring loop"""
        while True:
            try:
                # Wait for packet
                gaxi_packet = await self.receive()

                # Convert to monitor packet
                timestamp = get_sim_time('ns')
                monbus_packet = MonbusPacket.from_64bit(gaxi_packet.packet, timestamp)

                # Process packet
                await self._process_packet(monbus_packet)

            except Exception as e:
                if self.log:
                    self.log.error(f"Error in packet monitoring: {e}")
                await Timer(100, 'ns')  # Brief delay before retrying

    async def _process_packet(self, packet: MonbusPacket):
        """Process a received monitor packet"""
        self.packets_received.append(packet)
        self.packet_count += 1
        self.stats.total_packets += 1

        # Update type statistics
        if packet.is_error_packet():
            self.stats.error_packets += 1
        elif packet.is_completion_packet():
            self.stats.completion_packets += 1
        elif packet.is_timeout_packet():
            self.stats.timeout_packets += 1
        elif packet.is_performance_packet():
            self.stats.performance_packets += 1
        elif packet.packet_type == MonbusPktType.DEBUG.value:
            self.stats.debug_packets += 1
        else:
            self.stats.unknown_packets += 1

        # Verify packet format
        await self._verify_packet(packet)

        # Log packet using the GAXIPacket's built-in formatting
        if self.log:
            self.log.info(f"📥 RECEIVED: {packet}")

        # Call user callbacks
        for callback in self.packet_callbacks:
            try:
                callback(packet)
            except Exception as e:
                if self.log:
                    self.log.error(f"Error in packet callback: {e}")

    async def _verify_packet(self, packet: MonbusPacket):
        """Verify packet format and content"""
        errors = []

        # Check field ranges
        if packet.packet_type > 0xF:
            errors.append(f"Invalid packet_type: {packet.packet_type:X}")

        if packet.event_code > 0xF:
            errors.append(f"Invalid event_code: {packet.event_code:X}")

        if packet.channel_id > 0x3F:
            errors.append(f"Invalid channel_id: {packet.channel_id:X}")

        if packet.unit_id > 0xF:
            errors.append(f"Invalid unit_id: {packet.unit_id:X}")

        if packet.agent_id > 0xFF:
            errors.append(f"Invalid agent_id: {packet.agent_id:X}")

        if packet.data > 0x3FFFFFFFFF:  # 38 bits
            errors.append(f"Invalid data field: {packet.data:X}")

        # Check expected IDs
        if self.expected_unit_id is not None and packet.unit_id != self.expected_unit_id:
            errors.append(f"Unit ID mismatch: expected {self.expected_unit_id:X}, got {packet.unit_id:X}")

        if self.expected_agent_id is not None and packet.agent_id != self.expected_agent_id:
            errors.append(f"Agent ID mismatch: expected {self.expected_agent_id:02X}, got {packet.agent_id:02X}")

        # Check packet type specific constraints
        if packet.is_error_packet():
            valid_error_codes = [e.value for e in MonbusEventCode if e.value in [0x4, 0x5, 0x6, 0x7, 0x8, 0x9]]
            if packet.event_code not in valid_error_codes:
                errors.append(f"Invalid error event code: {packet.event_code:X}")

        elif packet.is_timeout_packet():
            valid_timeout_codes = [0x1, 0x2, 0x3]  # CMD, DATA, RESP timeouts
            if packet.event_code not in valid_timeout_codes:
                errors.append(f"Invalid timeout event code: {packet.event_code:X}")

        elif packet.is_completion_packet():
            if packet.event_code != MonbusEventCode.TRANS_COMPLETE.value:
                errors.append(f"Invalid completion event code: {packet.event_code:X}")

        # Record verification errors
        if errors:
            self.verification_errors.extend(errors)
            self.stats.verification_errors += len(errors)

            if self.log:
                for error in errors:
                    self.log.error(f"❌ PACKET_VERIFICATION_ERROR: {error}")

    def get_packets_by_type(self, packet_type: MonbusPktType) -> List[MonbusPacket]:
        """Get all packets of a specific type"""
        return [p for p in self.packets_received if p.packet_type == packet_type.value]

    def get_error_packets(self) -> List[MonbusPacket]:
        """Get all error packets"""
        return self.get_packets_by_type(MonbusPktType.ERROR)

    def get_completion_packets(self) -> List[MonbusPacket]:
        """Get all completion packets"""
        return self.get_packets_by_type(MonbusPktType.COMPLETION)

    def get_timeout_packets(self) -> List[MonbusPacket]:
        """Get all timeout packets"""
        return self.get_packets_by_type(MonbusPktType.TIMEOUT)

    def get_performance_packets(self) -> List[MonbusPacket]:
        """Get all performance packets"""
        return self.get_packets_by_type(MonbusPktType.PERF)

    def get_debug_packets(self) -> List[MonbusPacket]:
        """Get all debug packets"""
        return self.get_packets_by_type(MonbusPktType.DEBUG)

    def get_packets_for_channel(self, channel_id: int) -> List[MonbusPacket]:
        """Get all packets for a specific channel"""
        return [p for p in self.packets_received if p.channel_id == channel_id]

    def get_latest_packet(self) -> Optional[MonbusPacket]:
        """Get the most recently received packet"""
        return self.packets_received[-1] if self.packets_received else None

    def wait_for_packet_type(self, packet_type: MonbusPktType, timeout_cycles: int = 1000) -> Optional[MonbusPacket]:
        """Wait for a specific packet type (coroutine)"""
        async def _wait():
            start_count = len(self.get_packets_by_type(packet_type))
            for _ in range(timeout_cycles):
                if len(self.get_packets_by_type(packet_type)) > start_count:
                    return self.get_packets_by_type(packet_type)[-1]
                await RisingEdge(self.clock)
            return None

        return _wait()

    def has_verification_errors(self) -> bool:
        """Check if any verification errors were detected"""
        return len(self.verification_errors) > 0

    def get_statistics(self) -> Dict[str, Any]:
        """Get comprehensive statistics"""
        stats = {
            'packets_received': self.packet_count,
            'total_packets': self.stats.total_packets,
            'error_packets': self.stats.error_packets,
            'completion_packets': self.stats.completion_packets,
            'timeout_packets': self.stats.timeout_packets,
            'performance_packets': self.stats.performance_packets,
            'debug_packets': self.stats.debug_packets,
            'unknown_packets': self.stats.unknown_packets,
            'verification_errors': self.stats.verification_errors,
            'verification_error_list': self.verification_errors,
            'last_packet_time': self.packets_received[-1].timestamp if self.packets_received else 0,
            'monitoring_duration': (self.packets_received[-1].timestamp - self.packets_received[0].timestamp)
                                  if len(self.packets_received) > 1 else 0
        }
        return stats

    def generate_report(self) -> str:
        """Generate a comprehensive monitoring report"""
        stats = self.get_statistics()

        report = f"\n{self.title} Monitor Report\n"
        report += "=" * 50 + "\n"
        report += f"Total Packets Received: {stats['packets_received']}\n"
        report += f"Monitoring Duration: {stats['monitoring_duration']:.1f} ns\n\n"

        report += "Packet Type Breakdown:\n"
        report += f"  Error Packets: {stats['error_packets']}\n"
        report += f"  Completion Packets: {stats['completion_packets']}\n"
        report += f"  Timeout Packets: {stats['timeout_packets']}\n"
        report += f"  Performance Packets: {stats['performance_packets']}\n"
        report += f"  Debug Packets: {stats['debug_packets']}\n"
        report += f"  Unknown Packets: {stats['unknown_packets']}\n\n"

        if stats['verification_errors'] > 0:
            report += f"Verification Errors: {stats['verification_errors']}\n"
            for error in stats['verification_error_list'][-5:]:  # Show last 5
                report += f"  - {error}\n"
        else:
            report += "✅ No verification errors detected\n"

        return report

    def reset_statistics(self):
        """Reset all statistics and packet history"""
        self.packet_count = 0
        self.packets_received.clear()
        self.verification_errors.clear()

        # Reset the stats object
        self.stats = MonbusStats()

        if self.log:
            self.log.info(f"{self.title} statistics reset")


# Utility functions for easy integration
def create_monbus_master(dut, unit_id: int = 9, agent_id: int = 99, **kwargs) -> MonbusMaster:
    """Utility function to create a monitor bus master"""
    return MonbusMaster(
        dut=dut,
        unit_id=unit_id,
        agent_id=agent_id,
        **kwargs
    )


def create_monbus_slave(dut, expected_unit_id: Optional[int] = None,
                       expected_agent_id: Optional[int] = None, **kwargs) -> MonbusSlave:
    """Utility function to create a monitor bus slave"""
    return MonbusSlave(
        dut=dut,
        expected_unit_id=expected_unit_id,
        expected_agent_id=expected_agent_id,
        **kwargs
    )
