"""
MonBus Slave Implementation

This module contains the enhanced MonbusSlave class with complete type validation
and comprehensive packet monitoring capabilities.
"""

import time
import asyncio
from typing import List, Dict, Any, Callable, Union, Optional

from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket

from .monbus_types import ProtocolType, PktType
from .monbus_packet import MonbusPacket, create_monbus_field_config


class MonbusSlave(GAXISlave):
    """Enhanced MonBus Slave with complete type validation support"""

    def __init__(self, dut, title, prefix, clock,
                    bus_name='monbus',
                    pkt_prefix='',
                    expected_unit_id=None,
                    expected_agent_id=None,
                    expected_protocol=None,
                    timeout_cycles=1000,
                    log=None, super_debug=False, **kwargs):
        """Initialize enhanced MonBus Slave with complete type support"""

        # Create proper field config for monitor bus packets
        field_config = create_monbus_field_config()

        # Initialize GAXISlave with monitor bus field config
        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            timeout_cycles=timeout_cycles,
            mode='skid',
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            multi_sig=False,
            log=log,
            super_debug=super_debug,
            **kwargs
        )

        # MonBus-specific attributes with enhanced type support
        self.expected_unit_id = expected_unit_id
        self.expected_agent_id = expected_agent_id
        self.expected_protocol = expected_protocol

        # Packet callbacks and storage
        self.packet_callbacks: List[Callable] = []
        self.received_packets: List[MonbusPacket] = []

        # Enhanced statistics with complete packet type breakdown
        self.monbus_stats = self._initialize_enhanced_stats()

        # Override the packet processing callback
        self.add_callback(self._process_monbus_packet)

        self.log.info(f"Enhanced MonbusSlave '{title}' initialized with complete type support")

    def _initialize_enhanced_stats(self) -> Dict[str, Any]:
        """Initialize enhanced statistics with all packet types"""
        stats = {
            'packets_received': 0,
            'total_packets': 0,
            'verification_errors': 0,
            'verification_error_list': [],
            'last_packet_time': 0,
            'monitoring_duration': 0,
            'field_access_errors': 0,
            'raw_gaxi_packets': 0,
            'invalid_event_codes': 0,
        }

        # Protocol-specific counters
        for protocol in ProtocolType:
            stats[f'{protocol.name.lower()}_packets'] = 0

        # Packet type counters
        for pkt_type in PktType:
            stats[f'{pkt_type.name.lower()}_packets'] = 0

        return stats

    def _process_monbus_packet(self, gaxi_packet: GAXIPacket):
        """Enhanced packet processing with complete type validation"""
        try:
            self.monbus_stats['raw_gaxi_packets'] += 1

            # Create MonbusPacket with enhanced validation
            monbus_packet = MonbusPacket(gaxi_packet)

            if self.super_debug:
                self.log.debug(f"🔧 Enhanced MonbusPacket: {monbus_packet}")

            # Enhanced validation
            valid = self._validate_enhanced_packet(monbus_packet)
            if not valid:
                return

            # Enhanced statistics update
            self._update_enhanced_packet_stats(monbus_packet)

            # Store packet
            self.received_packets.append(monbus_packet)

            if self.super_debug:
                self.log.debug(f"✅ Enhanced MonBus packet processed: {monbus_packet}")

            # Call all registered callbacks
            for callback in self.packet_callbacks:
                try:
                    callback(monbus_packet)
                except Exception as e:
                    self.log.error(f"Error in packet callback: {e}")

        except Exception as e:
            self.log.error(f"Error in enhanced packet processing: {e}")
            self.monbus_stats['field_access_errors'] += 1
            self.monbus_stats['verification_errors'] += 1
            self.monbus_stats['verification_error_list'].append(f"Processing error: {e}")

    def _validate_enhanced_packet(self, packet: MonbusPacket) -> bool:
        """Enhanced packet validation with complete type checking"""
        # Basic field validation
        if self.expected_unit_id is not None and packet.unit_id != self.expected_unit_id:
            error_msg = f"Unit ID mismatch: expected {self.expected_unit_id}, got {packet.unit_id}"
            self.monbus_stats['verification_errors'] += 1
            self.monbus_stats['verification_error_list'].append(error_msg)
            if self.super_debug:
                self.log.warning(f"⚠️ {error_msg}")
            return False

        if self.expected_agent_id is not None and packet.agent_id != self.expected_agent_id:
            error_msg = f"Agent ID mismatch: expected {self.expected_agent_id}, got {packet.agent_id}"
            self.monbus_stats['verification_errors'] += 1
            self.monbus_stats['verification_error_list'].append(error_msg)
            if self.super_debug:
                self.log.warning(f"⚠️ {error_msg}")
            return False

        if self.expected_protocol is not None:
            expected_val = self.expected_protocol.value if hasattr(self.expected_protocol, 'value') else self.expected_protocol
            if packet.protocol != expected_val:
                error_msg = f"Protocol mismatch: expected {expected_val}, got {packet.protocol}"
                self.monbus_stats['verification_errors'] += 1
                self.monbus_stats['verification_error_list'].append(error_msg)
                if self.super_debug:
                    self.log.warning(f"⚠️ {error_msg}")
                return False

        # Enhanced validation: Check if event code is valid for protocol/packet_type
        if not packet.is_valid_event_code():
            error_msg = (f"Invalid event code {packet.event_code:X} for "
                        f"{packet.get_protocol_name()}.{packet.get_packet_type_name()}")
            self.monbus_stats['invalid_event_codes'] += 1
            self.monbus_stats['verification_error_list'].append(error_msg)
            if self.super_debug:
                self.log.warning(f"⚠️ {error_msg}")
            # Don't fail validation for invalid event codes, just log them

        return True

    def _update_enhanced_packet_stats(self, packet: MonbusPacket):
        """Enhanced statistics update with complete type breakdown"""
        self.monbus_stats['packets_received'] += 1
        self.monbus_stats['total_packets'] += 1
        self.monbus_stats['last_packet_time'] = time.time()

        # Protocol-specific stats using enums
        protocol_enum = packet.get_protocol_enum()
        if protocol_enum:
            protocol_key = f'{protocol_enum.name.lower()}_packets'
            self.monbus_stats[protocol_key] = self.monbus_stats.get(protocol_key, 0) + 1

        # Packet type stats using enums
        pkt_type_enum = packet.get_packet_type_enum()
        if pkt_type_enum:
            pkt_type_key = f'{pkt_type_enum.name.lower()}_packets'
            self.monbus_stats[pkt_type_key] = self.monbus_stats.get(pkt_type_key, 0) + 1

    # Enhanced packet retrieval methods with enum support
    def get_received_packets(self, packet_type: Union[PktType, int] = None,
                            protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
        """Get received packets with enhanced filtering"""
        packets = self.received_packets.copy()

        if packet_type is not None:
            pkt_type_val = packet_type.value if hasattr(packet_type, 'value') else packet_type
            packets = [p for p in packets if p.packet_type == pkt_type_val]

        if protocol is not None:
            protocol_val = protocol.value if hasattr(protocol, 'value') else protocol
            packets = [p for p in packets if p.protocol == protocol_val]

        return packets

    # Enhanced convenience methods using enums
    def get_error_packets(self, protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
        """Get error packets, optionally filtered by protocol"""
        return self.get_received_packets(PktType.ERROR, protocol)

    def get_completion_packets(self, protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
        """Get completion packets, optionally filtered by protocol"""
        return self.get_received_packets(PktType.COMPLETION, protocol)

    def get_timeout_packets(self, protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
        """Get timeout packets, optionally filtered by protocol"""
        return self.get_received_packets(PktType.TIMEOUT, protocol)

    def get_performance_packets(self, protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
        """Get performance packets, optionally filtered by protocol"""
        return self.get_received_packets(PktType.PERF, protocol)

    def get_threshold_packets(self, protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
        """Get threshold packets, optionally filtered by protocol"""
        return self.get_received_packets(PktType.THRESHOLD, protocol)

    def get_debug_packets(self, protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
        """Get debug packets, optionally filtered by protocol"""
        return self.get_received_packets(PktType.DEBUG, protocol)

    # Protocol-specific packet retrieval
    def get_axi_packets(self, packet_type: Union[PktType, int] = None) -> List[MonbusPacket]:
        """Get AXI protocol packets"""
        return self.get_received_packets(packet_type, ProtocolType.AXI)

    def get_apb_packets(self, packet_type: Union[PktType, int] = None) -> List[MonbusPacket]:
        """Get APB protocol packets"""
        return self.get_received_packets(packet_type, ProtocolType.APB)

    def get_noc_packets(self, packet_type: Union[PktType, int] = None) -> List[MonbusPacket]:
        """Get NOC protocol packets"""
        return self.get_received_packets(packet_type, ProtocolType.NOC)

    def get_custom_packets(self, packet_type: Union[PktType, int] = None) -> List[MonbusPacket]:
        """Get custom protocol packets"""
        return self.get_received_packets(packet_type, ProtocolType.CUSTOM)

    async def expect_packet(self, expected_packet: Dict[str, Any],
                            timeout_cycles: int = None) -> bool:
        """
        Wait for and validate a specific packet

        Args:
            expected_packet: Dict with packet fields to match
            timeout_cycles: Optional timeout override

        Returns:
            True if matching packet received, False on timeout
        """
        timeout_cycles = timeout_cycles or self.timeout_cycles
        start_count = len(self.received_packets)

        for _ in range(timeout_cycles):
            await self.wait_clock()

            # Check if any new packets match
            for packet in self.received_packets[start_count:]:
                if packet.matches(**expected_packet):
                    if self.super_debug:
                        self.log.debug(f"✅ Expected packet found: {packet}")
                    return True

        if self.super_debug:
            self.log.warning(f"⚠️ Expected packet not found after {timeout_cycles} cycles: {expected_packet}")
        return False

    async def expect_packet_sequence(self, expected_sequence: List[Dict[str, Any]],
                                    timeout_cycles: int = None) -> bool:
        """
        Wait for and validate a sequence of packets in order

        Args:
            expected_sequence: List of expected packet dicts
            timeout_cycles: Optional timeout override

        Returns:
            True if sequence matches, False on timeout
        """
        timeout_cycles = timeout_cycles or self.timeout_cycles
        start_count = len(self.received_packets)
        sequence_index = 0

        for _ in range(timeout_cycles):
            await self.wait_clock()

            # Check for next packet in sequence
            while (start_count + sequence_index < len(self.received_packets) and
                    sequence_index < len(expected_sequence)):
                packet = self.received_packets[start_count + sequence_index]
                expected = expected_sequence[sequence_index]

                if packet.matches(**expected):
                    sequence_index += 1
                    if sequence_index == len(expected_sequence):
                        if self.super_debug:
                            self.log.debug(f"✅ Packet sequence completed")
                        return True
                else:
                    # Sequence broken
                    if self.super_debug:
                        self.log.warning(f"⚠️ Packet sequence broken at index {sequence_index}")
                        self.log.warning(f"   Expected: {expected}")
                        self.log.warning(f"   Got: {packet.to_dict()}")
                    return False

        if self.super_debug:
            self.log.warning(f"⚠️ Packet sequence incomplete: {sequence_index}/{len(expected_sequence)} after {timeout_cycles} cycles")
        return False

    def validate_packet_sequence(self, expected_sequence: List[Dict[str, Any]],
                                start_index: int = 0) -> bool:
        """
        Validate a sequence of packets was received in order (synchronous)

        Args:
            expected_sequence: List of expected packet dicts
            start_index: Index to start checking from

        Returns:
            True if sequence matches, False otherwise
        """
        if len(self.received_packets) - start_index < len(expected_sequence):
            return False

        for i, expected in enumerate(expected_sequence):
            packet_index = start_index + i
            if packet_index >= len(self.received_packets):
                return False

            packet = self.received_packets[packet_index]
            if not packet.matches(**expected):
                if self.super_debug:
                    self.log.warning(f"⚠️ Sequence mismatch at index {i}")
                    self.log.warning(f"   Expected: {expected}")
                    self.log.warning(f"   Got: {packet.to_dict()}")
                return False

        return True

    def find_packets(self, **criteria) -> List[MonbusPacket]:
        """
        Find packets matching given criteria

        Args:
            **criteria: Field names and values to match

        Returns:
            List of matching packets
        """
        return [p for p in self.received_packets if p.matches(**criteria)]

    def count_packets(self, **criteria) -> int:
        """Count packets matching given criteria"""
        return len(self.find_packets(**criteria))

    def get_enhanced_statistics(self) -> Dict[str, Any]:
        """Return enhanced statistics with complete type breakdown"""
        stats = self.monbus_stats.copy()

        # Add enhanced type breakdown
        stats['protocol_breakdown'] = {}
        for protocol in ProtocolType:
            protocol_key = f'{protocol.name.lower()}_packets'
            stats['protocol_breakdown'][protocol.name] = stats.get(protocol_key, 0)

        stats['packet_type_breakdown'] = {}
        for pkt_type in PktType:
            pkt_type_key = f'{pkt_type.name.lower()}_packets'
            stats['packet_type_breakdown'][pkt_type.name] = stats.get(pkt_type_key, 0)

        # Add field config info
        stats['field_config_total_bits'] = self.field_config.get_total_bits()
        stats['field_names'] = self.field_config.field_names()

        return stats

    def add_packet_callback(self, callback: Callable[[MonbusPacket], None]):
        """Add callback for received packets"""
        self.packet_callbacks.append(callback)

    def clear_received_packets(self):
        """Clear the received packets list (useful for test phases)"""
        self.received_packets.clear()

    def get_stats_summary(self) -> str:
        """Get a human-readable summary of statistics"""
        stats = self.get_enhanced_statistics()
        lines = [
            f"Enhanced MonbusSlave '{self.title}' Statistics:",
            f"  Total packets: {stats['total_packets']}",
            f"  Verification errors: {stats['verification_errors']}",
            f"  Invalid event codes: {stats['invalid_event_codes']}",
            "",
            "Protocol breakdown:"
        ]

        for protocol, count in stats['protocol_breakdown'].items():
            if count > 0:
                lines.append(f"  {protocol}: {count}")

        lines.append("")
        lines.append("Packet type breakdown:")

        for pkt_type, count in stats['packet_type_breakdown'].items():
            if count > 0:
                lines.append(f"  {pkt_type}: {count}")

        if stats['verification_error_list']:
            lines.append("")
            lines.append("Recent errors:")
            for error in stats['verification_error_list'][-5:]:  # Show last 5 errors
                lines.append(f"  {error}")

        return "\n".join(lines)

    def __str__(self) -> str:
        """Enhanced string representation"""
        return (f"Enhanced MonbusSlave '{self.title}': {self.monbus_stats['packets_received']} packets, "
                f"{self.monbus_stats['verification_errors']} errors, "
                f"{self.monbus_stats['invalid_event_codes']} invalid event codes")
