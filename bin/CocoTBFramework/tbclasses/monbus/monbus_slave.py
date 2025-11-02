# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MonbusSlave
# Purpose: MonBus Slave Implementation - Fixed and Functional
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
MonBus Slave Implementation - Fixed and Functional

This module contains a properly implemented MonbusSlave class based on GAXISlave
with complete packet monitoring capabilities and ARB protocol support.

Key Features:
- Proper GAXISlave inheritance and initialization
- Complete packet processing pipeline
- ARB protocol support with all event types
- Comprehensive statistics tracking
- Ready probability control for backpressure testing
- Robust error handling and validation
"""

import time
import asyncio
from collections import defaultdict, deque
from typing import List, Dict, Any, Callable, Union, Optional

from cocotb.utils import get_sim_time

from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

from .monbus_types import ProtocolType, PktType
from .monbus_packet import MonbusPacket, create_monbus_field_config


class MonbusSlave(GAXISlave):
    """MonBus Slave with complete functionality and ARB protocol support"""

    def __init__(self, dut, title, prefix, clock,
                bus_name='monbus',
                pkt_prefix='',
                expected_unit_id=None,
                expected_agent_id=None,
                expected_protocol=None,
                timeout_cycles=1000,
                ready_probability=0.8,  # Backward compatibility only
                log=None, super_debug=False, **kwargs):
        """Initialize MonBus Slave with complete functionality"""

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
            mode='skid',  # Use skid mode for immediate capture
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            multi_sig=False,
            log=log,
            super_debug=super_debug,
            **kwargs  # Pass through all kwargs including randomizer
        )

        # MonBus-specific attributes
        self.expected_unit_id = expected_unit_id
        self.expected_agent_id = expected_agent_id
        self.expected_protocol = expected_protocol

        # Packet storage and callbacks
        self.packet_callbacks: List[Callable] = []
        self.received_packets: List[MonbusPacket] = []
        self.packet_history: deque = deque(maxlen=1000)  # Ring buffer for history

        # Ready delay randomizer for GAXI slave compatibility
        self._ready_randomizer = None
        if 'randomizer' in kwargs and kwargs['randomizer'] is not None:
            self._ready_randomizer = kwargs['randomizer']

        # Backward compatibility for ready_probability (convert to fast profile if needed)
        if ready_probability != 0.8 and self._ready_randomizer is None:
            # Create a fast profile with ready_probability converted to delays
            if ready_probability >= 0.8:
                profile = {'ready_delay': ([(0, 0), (1, 2)], [8, 1])}  # Mostly no delay
            elif ready_probability >= 0.5:
                profile = {'ready_delay': ([(0, 1), (2, 5)], [6, 3])}  # Medium delays
            else:
                profile = {'ready_delay': ([(1, 5), (6, 15)], [5, 4])}  # Higher delays
            self._ready_randomizer = FlexRandomizer(profile)

        # Statistics tracking
        self.monbus_stats = self._initialize_complete_stats()
        self.event_counters = defaultdict(int)
        self.protocol_counters = defaultdict(int)

        # Timing tracking
        self.last_packet_time = 0
        self.start_time = get_sim_time('ns')

        # Add our packet processing callback
        self.add_callback(self._process_monbus_packet)

        if self.log:
            self.log.info(f"MonbusSlave '{title}' initialized successfully with ARB protocol support")

    def _initialize_complete_stats(self) -> Dict[str, Any]:
        """Initialize comprehensive statistics tracking"""
        stats = {
            # Basic counters
            'packets_received': 0,
            'total_packets': 0,
            'verification_errors': 0,
            'verification_error_list': [],
            'last_packet_time': 0,
            'monitoring_duration': 0,
            'field_access_errors': 0,
            'raw_gaxi_packets': 0,
            'invalid_event_codes': 0,

            # Ready signal statistics
            'ready_assertions': 0,
            'ready_deasssertions': 0,
            'backpressure_cycles': 0,
            'ready_randomizer_profile': str(self._ready_randomizer.constraints if self._ready_randomizer else 'None'),

            # Protocol breakdown - FIXED KEYS
            'axi_packets': 0,
            'apb_packets': 0,
            'axis_packets': 0,
            'arb_packets': 0,
            'unknown_packets': 0,  # ✅ ADD: For unexpected protocols

            # Packet type breakdown - FIXED KEYS  
            'error_packets': 0,
            'timeout_packets': 0,
            'completion_packets': 0,
            'threshold_packets': 0,
            'perf_packets': 0,
            'debug_packets': 0,
            'unknown_type_packets': 0,  # ✅ ADD: For unexpected packet types

            # ARB-specific statistics - EXISTING KEYS
            'arb_error_events': 0,
            'arb_timeout_events': 0,
            'arb_completion_events': 0,
            'arb_threshold_events': 0,
            'arb_performance_events': 0,
            'arb_debug_events': 0,

            # Timing statistics
            'first_packet_time': None,
            'last_packet_time': None,
            'packet_rate': 0.0,
            'avg_inter_packet_time': 0.0,
        }

        return stats

    def _process_monbus_packet(self, gaxi_packet: GAXIPacket):
        """Process incoming GAXI packets and convert to MonBus packets"""
        try:
            current_time = get_sim_time('ns')
            self.monbus_stats['raw_gaxi_packets'] += 1

            # Create MonbusPacket from GAXIPacket
            try:
                monbus_packet = MonbusPacket(gaxi_packet)
            except Exception as e:
                self.monbus_stats['field_access_errors'] += 1
                if self.log:
                    self.log.error(f"Failed to create MonbusPacket: {e}")
                return

            # Validate packet
            if not self._validate_monbus_packet(monbus_packet):
                return

            # Store packet
            self.received_packets.append(monbus_packet)
            self.packet_history.append({
                'packet': monbus_packet,
                'timestamp': current_time,
                'raw_data': gaxi_packet.to_dict() if hasattr(gaxi_packet, 'to_dict') else str(gaxi_packet)
            })

            # Update comprehensive statistics
            self._update_packet_statistics(monbus_packet, current_time)

            # Execute user callbacks
            for callback in self.packet_callbacks:
                try:
                    callback(monbus_packet)
                except Exception as e:
                    if self.log:
                        self.log.error(f"Packet callback error: {e}")

            # Debug logging
            if self.super_debug and self.log:
                self.log.info(f"📦 MonBus packet received: {monbus_packet.format_for_display()}")

        except Exception as e:
            self.monbus_stats['field_access_errors'] += 1
            if self.log:
                self.log.error(f"Critical error processing MonBus packet {gaxi_packet=}: {e}")

    def _validate_monbus_packet(self, packet: MonbusPacket) -> bool:
        """Validate MonBus packet with comprehensive checks"""
        try:
            # Basic field validation
            if not packet.validate_fields():
                error_msg = f"Invalid field values in packet: {packet.to_dict()}"
                self._record_validation_error(error_msg)
                return False

            # Expected value validation
            if (self.expected_unit_id is not None and
                packet.unit_id != self.expected_unit_id):
                error_msg = f"Unexpected unit_id: expected {self.expected_unit_id:X}, got {packet.unit_id:X}"
                self._record_validation_error(error_msg)
                return False

            if (self.expected_agent_id is not None and
                packet.agent_id != self.expected_agent_id):
                error_msg = f"Unexpected agent_id: expected {self.expected_agent_id:X}, got {packet.agent_id:X}"
                self._record_validation_error(error_msg)
                return False

            if (self.expected_protocol is not None and
                packet.protocol != self.expected_protocol):
                error_msg = f"Unexpected protocol: expected {self.expected_protocol}, got {packet.protocol}"
                self._record_validation_error(error_msg)
                return False

            return True

        except Exception as e:
            self._record_validation_error(f"Validation exception: {e}")
            return False

    def _record_validation_error(self, error_msg: str):
        """Record validation error in statistics"""
        self.monbus_stats['verification_errors'] += 1
        self.monbus_stats['verification_error_list'].append(error_msg)
        if self.super_debug and self.log:
            self.log.warning(f"⚠️ {error_msg}")

    def _update_packet_statistics(self, packet: MonbusPacket, current_time: float):
        """Update comprehensive packet statistics"""
        self.monbus_stats['packets_received'] += 1
        self.monbus_stats['total_packets'] += 1
        self.monbus_stats['last_packet_time'] = current_time

        # Update timing statistics
        if self.monbus_stats['first_packet_time'] is None:
            self.monbus_stats['first_packet_time'] = current_time

        # Protocol statistics - FIX THE KEY MAPPING
        try:
            protocol = ProtocolType(packet.protocol)
            
            # ✅ FIX: Map protocol enum names to correct stats keys
            protocol_mapping = {
                'PROTOCOL_AXI': 'axi_packets',
                'PROTOCOL_APB': 'apb_packets', 
                'PROTOCOL_AXIS': 'axis_packets',
                'PROTOCOL_ARB': 'arb_packets'
            }
            
            protocol_key = protocol_mapping.get(protocol.name, 'unknown_packets')
            
            # Create the key if it doesn't exist (for unknown protocols)
            if protocol_key not in self.monbus_stats:
                self.monbus_stats[protocol_key] = 0
                
            self.monbus_stats[protocol_key] += 1
            self.protocol_counters[protocol.name] += 1
            
        except ValueError:
            self.monbus_stats['invalid_event_codes'] += 1

        # Packet type statistics - FIX THE KEY MAPPING
        try:
            pkt_type = PktType(packet.pkt_type)
            
            # ✅ FIX: Map packet type enum names to correct stats keys
            pkt_type_mapping = {
                'PktTypeError': 'error_packets',
                'PktTypeTimeout': 'timeout_packets', 
                'PktTypeCompletion': 'completion_packets',
                'PktTypeThreshold': 'threshold_packets',
                'PktTypePerf': 'perf_packets',
                'PktTypeDebug': 'debug_packets'
            }
            
            pkt_type_key = pkt_type_mapping.get(pkt_type.name, 'unknown_type_packets')
            
            # Create the key if it doesn't exist (for unknown packet types)
            if pkt_type_key not in self.monbus_stats:
                self.monbus_stats[pkt_type_key] = 0
                
            self.monbus_stats[pkt_type_key] += 1
            self.event_counters[pkt_type.name] += 1

            # ARB-specific event tracking - FIX THE KEY MAPPING
            if packet.protocol == ProtocolType.PROTOCOL_ARB.value:
                arb_event_mapping = {
                    'PktTypeError': 'arb_error_events',
                    'PktTypeTimeout': 'arb_timeout_events',
                    'PktTypeCompletion': 'arb_completion_events', 
                    'PktTypeThreshold': 'arb_threshold_events',
                    'PktTypePerf': 'arb_performance_events',
                    'PktTypeDebug': 'arb_debug_events'
                }
                
                arb_event_key = arb_event_mapping.get(pkt_type.name)
                if arb_event_key and arb_event_key in self.monbus_stats:
                    self.monbus_stats[arb_event_key] += 1

        except ValueError:
            self.monbus_stats['invalid_event_codes'] += 1

    # Public API Methods

    def add_packet_callback(self, callback: Callable[[MonbusPacket], None]):
        """Add callback for packet processing"""
        self.packet_callbacks.append(callback)

    def remove_packet_callback(self, callback: Callable[[MonbusPacket], None]):
        """Remove packet callback"""
        if callback in self.packet_callbacks:
            self.packet_callbacks.remove(callback)

    def set_ready_randomizer(self, randomizer: FlexRandomizer):
        """Set ready delay randomizer using AXI profile format"""
        self._ready_randomizer = randomizer

        # Update GAXISlave randomizer
        if hasattr(self, 'set_randomizer'):
            self.set_randomizer(randomizer)

        # Update statistics
        self.monbus_stats['ready_randomizer_profile'] = str(randomizer.constraints)

        if self.log:
            self.log.info(f"MonBus slave randomizer profile updated: {randomizer.constraints}")

    def get_ready_randomizer(self) -> Optional[FlexRandomizer]:
        """Get current ready delay randomizer"""
        return self._ready_randomizer

    def set_ready_probability(self, probability: float):
        """
        Set ready signal probability for backward compatibility

        NOTE: This is deprecated. Use set_ready_randomizer() with proper AXI profiles instead.
        """
        if self.log:
            self.log.warning("set_ready_probability() is deprecated. Use set_ready_randomizer() with AXI profiles.")

        # Convert probability to a basic AXI profile
        if probability >= 0.8:
            profile = {'ready_delay': ([(0, 0), (1, 2)], [8, 1])}  # Fast profile
        elif probability >= 0.5:
            profile = {'ready_delay': ([(0, 1), (2, 5)], [6, 3])}  # Medium delays
        else:
            profile = {'ready_delay': ([(1, 5), (6, 15)], [5, 4])}  # Slow profile

        new_randomizer = FlexRandomizer(profile)
        self.set_ready_randomizer(new_randomizer)

    def get_ready_probability(self) -> float:
        """
        Get approximate ready probability (deprecated)

        NOTE: This is an approximation. Use get_ready_randomizer() for exact profile.
        """
        if self._ready_randomizer is None:
            return 0.8

        # Approximate probability based on delay profile
        constraints = self._ready_randomizer.constraints
        if 'ready_delay' in constraints:
            ranges, weights = constraints['ready_delay']
            # Simple heuristic: lower delays = higher probability
            total_weight = sum(weights)
            zero_delay_weight = 0

            for i, (low, high) in enumerate(ranges):
                if low == 0 and high == 0:
                    zero_delay_weight = weights[i]
                    break

            return zero_delay_weight / total_weight if total_weight > 0 else 0.5

        return 0.5  # Default estimate

    async def get_received_packets(self, timeout_cycles: int = 100,
                                clear_after: bool = False,
                                drain_all: bool = False) -> List[MonbusPacket]:
        """
        Wait for and return received packets (async version for testbench compatibility)

        Args:
            timeout_cycles: Maximum cycles to wait
            clear_after: Whether to clear packets after returning
            drain_all: If True, ensure all queued packets are collected from FIFO.
                    Implements more aggressive collection strategy for comprehensive testing.

        Returns:
            List of received packets
        """
        initial_count = len(self.received_packets)
        cycles_waited = 0

        if drain_all:
            # DRAIN_ALL MODE: Comprehensive packet collection
            # Used in test cleanup and stress testing scenarios

            consecutive_no_new_packets = 0
            last_packet_count = initial_count

            while cycles_waited < timeout_cycles:
                current_count = len(self.received_packets)

                if current_count > last_packet_count:
                    # New packets arrived - reset stability counter
                    consecutive_no_new_packets = 0
                    last_packet_count = current_count
                else:
                    # No new packets this cycle
                    consecutive_no_new_packets += 1

                    # Consider drain complete after several stable cycles
                    # This accounts for FIFO depth and processing delays
                    if consecutive_no_new_packets >= 15:  # Configurable threshold
                        break

                await self.wait_clocks(1)
                cycles_waited += 1

            # ADDITIONAL STABILIZATION: Monitor for potential late arrivals
            # This is critical for stress tests and FIFO overflow scenarios
            stabilization_cycles = min(10, timeout_cycles - cycles_waited)
            late_packet_detected = False

            for _ in range(stabilization_cycles):
                if cycles_waited >= timeout_cycles:
                    break

                pre_stab_count = len(self.received_packets)
                await self.wait_clocks(1)
                cycles_waited += 1
                post_stab_count = len(self.received_packets)

                if post_stab_count > pre_stab_count:
                    late_packet_detected = True
                    # Extend stabilization if we're still getting packets
                    stabilization_cycles = min(stabilization_cycles + 5,
                                            timeout_cycles - cycles_waited)

            if self.log and late_packet_detected:
                self.log.debug(f"drain_all: Late packets detected during stabilization")

        else:
            # STANDARD MODE: Original behavior for backward compatibility
            while cycles_waited < timeout_cycles:
                if len(self.received_packets) > initial_count:
                    break
                await self.wait_clocks(1)
                cycles_waited += 1

        packets = self.received_packets.copy()

        if clear_after:
            self.clear_received_packets()

        # Enhanced logging for drain_all mode
        if drain_all and self.log:
            packet_delta = len(packets) - initial_count
            self.log.debug(f"drain_all collected {packet_delta} new packets "
                        f"({len(packets)} total) in {cycles_waited} cycles")

        return packets


    # =============================================================================
    # ADDITIONAL HELPER METHOD (Optional but recommended)
    # =============================================================================

    async def drain_all_packets_explicit(self, max_cycles: int = 200) -> List[MonbusPacket]:
        """
        Explicitly drain all packets from MonBus FIFO with clear semantics.

        This method provides a clear API for test scenarios that need comprehensive
        packet collection and cleanup.

        Args:
            max_cycles: Maximum cycles to spend draining

        Returns:
            All packets collected, buffer is cleared after collection
        """
        return await self.get_received_packets(
            timeout_cycles=max_cycles,
            clear_after=True,
            drain_all=True
        )

    def get_received_packets_sync(self, clear_after: bool = False) -> List[MonbusPacket]:
        """Get received packets (synchronous version)"""
        packets = self.received_packets.copy()
        if clear_after:
            self.clear_received_packets()
        return packets

    def clear_received_packets(self):
        """Clear received packets buffer"""
        self.received_packets.clear()
        if self.log:
            self.log.debug("MonBus received packets cleared")

    def find_packets(self, **criteria) -> List[MonbusPacket]:
        """Find packets matching given criteria"""
        matching_packets = []
        for packet in self.received_packets:
            match = True
            for key, value in criteria.items():
                if not hasattr(packet, key) or getattr(packet, key) != value:
                    match = False
                    break
            if match:
                matching_packets.append(packet)
        return matching_packets

    def count_packets(self, **criteria) -> int:
        """Count packets matching given criteria"""
        return len(self.find_packets(**criteria))

    def get_enhanced_statistics(self) -> Dict[str, Any]:
        """Get comprehensive statistics"""
        current_time = get_sim_time('ns')
        stats = self.monbus_stats.copy()

        # Add derived statistics
        duration = current_time - self.start_time
        stats['current_monitoring_duration'] = duration

        # Protocol breakdown
        stats['protocol_breakdown'] = dict(self.protocol_counters)

        # Event type breakdown
        stats['event_type_breakdown'] = dict(self.event_counters)

        # Rate calculations
        if duration > 0:
            stats['current_packet_rate'] = len(self.received_packets) / (duration / 1e9)

        # Add base GAXI slave statistics
        base_stats = self.get_stats()
        stats['gaxi_slave_stats'] = base_stats

        return stats

    def get_packet_history(self, count: Optional[int] = None) -> List[Dict[str, Any]]:
        """Get packet history with timestamps"""
        if count is None:
            return list(self.packet_history)
        else:
            return list(self.packet_history)[-count:]

    def reset_statistics(self):
        """Reset all statistics counters"""
        self.monbus_stats = self._initialize_complete_stats()
        self.event_counters.clear()
        self.protocol_counters.clear()
        self.start_time = get_sim_time('ns')

        if self.log:
            self.log.info("MonBus slave statistics reset")

    async def wait_for_packets(self, count: int, timeout_cycles: int = 1000) -> bool:
        """
        Wait for a specific number of packets to be received

        Args:
            count: Number of packets to wait for
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if packets received, False if timeout
        """
        initial_count = len(self.received_packets)
        target_count = initial_count + count
        cycles_waited = 0

        while len(self.received_packets) < target_count and cycles_waited < timeout_cycles:
            await self.wait_clocks(1)
            cycles_waited += 1

        return len(self.received_packets) >= target_count

    def validate_packet_sequence(self, expected_sequence: List[Dict[str, Any]],
                                start_index: int = 0) -> bool:
        """Validate a sequence of packets matches expected pattern"""
        if len(self.received_packets) - start_index < len(expected_sequence):
            return False

        for i, expected in enumerate(expected_sequence):
            packet_index = start_index + i
            if packet_index >= len(self.received_packets):
                return False

            packet = self.received_packets[packet_index]

            # Check each expected field
            for key, expected_value in expected.items():
                if not hasattr(packet, key):
                    if self.super_debug and self.log:
                        self.log.warning(f"⚠️ Packet missing field '{key}'")
                    return False

                actual_value = getattr(packet, key)
                if actual_value != expected_value:
                    if self.super_debug and self.log:
                        self.log.warning(f"⚠️ Field mismatch: {key} expected {expected_value}, got {actual_value}")
                    return False

        return True

    async def wait_clocks(self, cycles: int):
        """Wait for specified number of clock cycles"""
        from cocotb.triggers import RisingEdge
        for _ in range(cycles):
            await RisingEdge(self.clock)

    def __str__(self) -> str:
        """String representation"""
        profile_info = str(self._ready_randomizer.constraints) if self._ready_randomizer else 'default'
        return f"MonbusSlave('{self.title}', packets={len(self.received_packets)}, profile={profile_info})"

    def __repr__(self) -> str:
        """Detailed string representation"""
        return (f"MonbusSlave(title='{self.title}', prefix='{self.prefix}', "
                f"packets_received={len(self.received_packets)}, "
                f"randomizer_profile={self._ready_randomizer.constraints if self._ready_randomizer else 'None'}, "
                f"expected_protocol={self.expected_protocol})")

    def _debug_enum_values(self, packet: MonbusPacket):
        """Debug helper to see what enum values we're getting"""
        if self.log and self.super_debug:
            try:
                protocol = ProtocolType(packet.protocol)
                pkt_type = PktType(packet.pkt_type)
                
                self.log.debug(f"Packet enum values: protocol={protocol.name} ({packet.protocol}), "
                            f"pkt_type={pkt_type.name} ({packet.pkt_type})")
            except ValueError as e:
                self.log.debug(f"Invalid enum values: protocol={packet.protocol}, "
                            f"pkt_type={packet.pkt_type}, error={e}")
