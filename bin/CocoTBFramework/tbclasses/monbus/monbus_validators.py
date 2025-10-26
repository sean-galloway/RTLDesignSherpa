# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: monbus_validators
# Purpose: MonBus Validation Helper Functions - UPDATED for New Monitor Package
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
MonBus Validation Helper Functions - UPDATED for New Monitor Package

This module provides validation functions, packet matchers, and analysis tools
for MonBus packet validation and testing with complete ARB and CORE protocol support.

UPDATED FOR NEW MONITOR PACKAGE:
- Protocol field now 3 bits [59:57] supporting 5 protocols including CORE
- Event data field now 35 bits [34:0]
- Updated range validations and event code mappings
- Added comprehensive CORE protocol support
- Updated all field range validations for new packet format
"""

from typing import List, Dict, Any, Callable, Union, Optional, Tuple
from enum import IntEnum
import statistics
import time

from .monbus_types import (
    ProtocolType, PktType,
    # ARB Protocol codes
    ARBErrorCode, ARBTimeoutCode, ARBCompletionCode, ARBThresholdCode,
    ARBPerformanceCode, ARBDebugCode,
    # AXI Protocol codes
    AXIErrorCode, AXITimeoutCode,
    # APB Protocol codes  
    APBErrorCode,
    # AXIS Protocol codes
    AXISErrorCode,
    # CORE Protocol codes (NEW)
)
from .monbus_packet import MonbusPacket


# =============================================================================
# PACKET VALIDATION FUNCTIONS - UPDATED
# =============================================================================

def validate_packet_fields(packet: MonbusPacket, expected_fields: Dict[str, Any]) -> List[str]:
    """
    Validate packet fields against expected values

    Args:
        packet: MonbusPacket to validate
        expected_fields: Dict of field_name -> expected_value

    Returns:
        List of error messages (empty if all valid)
    """
    errors = []

    for field_name, expected_value in expected_fields.items():
        if hasattr(packet, field_name):
            actual_value = getattr(packet, field_name)
            # Handle enum comparisons
            if hasattr(expected_value, 'value'):
                expected_value = expected_value.value
            if actual_value != expected_value:
                errors.append(f"{field_name}: expected {expected_value}, got {actual_value}")
        else:
            errors.append(f"Field {field_name} not found in packet")

    return errors


def validate_packet_range(packet: MonbusPacket, field_ranges: Dict[str, Tuple[int, int]]) -> List[str]:
    """
    Validate packet fields are within specified ranges

    Args:
        packet: MonbusPacket to validate
        field_ranges: Dict of field_name -> (min_value, max_value)

    Returns:
        List of error messages (empty if all valid)
    """
    errors = []

    for field_name, (min_val, max_val) in field_ranges.items():
        if hasattr(packet, field_name):
            actual_value = getattr(packet, field_name)
            if not (min_val <= actual_value <= max_val):
                errors.append(f"{field_name}: {actual_value} not in range [{min_val}, {max_val}]")
        else:
            errors.append(f"Field {field_name} not found in packet")

    return errors


def validate_packet_enum_fields(packet: MonbusPacket) -> List[str]:
    """
    Validate that packet enum fields have valid values including ARB and CORE protocols

    Args:
        packet: MonbusPacket to validate

    Returns:
        List of error messages (empty if all valid)
    """
    errors = []

    # Check protocol enum
    try:
        ProtocolType(packet.protocol)
    except ValueError:
        errors.append(f"Invalid protocol value: {packet.protocol}")

    # Check packet type enum
    try:
        PktType(packet.pkt_type)
    except ValueError:
        errors.append(f"Invalid pkt_type value: {packet.pkt_type}")

    # Check event code validity with ARB and CORE protocol support
    if not is_valid_event_code(packet.protocol, packet.pkt_type, packet.event_code):
        errors.append(f"Invalid event_code {packet.event_code} for "
                    f"{packet.get_protocol_name()}.{packet.get_packet_type_name()}")

    return errors


def is_valid_event_code(protocol: int, pkt_type: int, event_code: int) -> bool:
    """Check if event code is valid for given protocol and packet type"""
    from .monbus_types import is_valid_event_code
    return is_valid_event_code(protocol, pkt_type, event_code)


def validate_packet_consistency(packet: MonbusPacket) -> List[str]:
    """
    Validate packet internal consistency - UPDATED for new field ranges

    Args:
        packet: MonbusPacket to validate

    Returns:
        List of error messages (empty if all valid)
    """
    errors = []

    # Check basic field ranges - UPDATED
    field_ranges = {
        'protocol': (0, 7),           # 3 bits ✅ CORRECTED: 0-7 range
        'pkt_type': (0, 15),          # 4 bits
        'event_code': (0, 15),        # 4 bits
        'unit_id': (0, 15),           # 4 bits
        'channel_id': (0, 63),        # 6 bits
        'agent_id': (0, 255),         # 8 bits
        'data': (0, (1 << 35) - 1)    # 35 bits ✅ CORRECTED: 35-bit max
    }

    errors.extend(validate_packet_range(packet, field_ranges))
    errors.extend(validate_packet_enum_fields(packet))

    return errors


def validate_arb_protocol_packet(packet: MonbusPacket) -> List[str]:
    """
    Validate ARB protocol specific packet constraints

    Args:
        packet: MonbusPacket to validate (should be ARB protocol)

    Returns:
        List of error messages (empty if all valid)
    """
    errors = []

    if not packet.is_arb_protocol():
        errors.append("Packet is not ARB protocol")
        return errors

    # Validate ARB-specific constraints
    try:
        packet_type = PktType(packet.pkt_type)
    except ValueError:
        errors.append(f"Invalid packet type: {packet.pkt_type}")
        return errors

    event_code = packet.event_code

    # ARB protocol specific validations
    if packet_type == PktType.ERROR:
        try:
            ARBErrorCode(event_code)
        except ValueError:
            errors.append(f"Invalid ARB error code: {event_code}")

    elif packet_type == PktType.TIMEOUT:
        try:
            ARBTimeoutCode(event_code)
        except ValueError:
            errors.append(f"Invalid ARB timeout code: {event_code}")

    elif packet_type == PktType.THRESHOLD:
        try:
            ARBThresholdCode(event_code)
        except ValueError:
            errors.append(f"Invalid ARB threshold code: {event_code}")

    elif packet_type == PktType.PERF:
        try:
            ARBPerformanceCode(event_code)
        except ValueError:
            errors.append(f"Invalid ARB performance code: {event_code}")

    elif packet_type == PktType.COMPLETION:
        try:
            ARBCompletionCode(event_code)
        except ValueError:
            errors.append(f"Invalid ARB completion code: {event_code}")

    elif packet_type == PktType.DEBUG:
        try:
            ARBDebugCode(event_code)
        except ValueError:
            errors.append(f"Invalid ARB debug code: {event_code}")

    return errors


def validate_core_protocol_packet(packet: MonbusPacket) -> List[str]:
    """
    Validate CORE protocol specific packet constraints - NEW

    Args:
        packet: MonbusPacket to validate (should be CORE protocol)

    Returns:
        List of error messages (empty if all valid)
    """
    errors = []

    if not packet.is_core_protocol():
        errors.append("Packet is not CORE protocol")
        return errors

    # Validate CORE-specific constraints
    try:
        packet_type = PktType(packet.pkt_type)
    except ValueError:
        errors.append(f"Invalid packet type: {packet.pkt_type}")
        return errors

    event_code = packet.event_code

    # CORE protocol specific validations
    if packet_type == PktType.ERROR:
        try:
            COREErrorCode(event_code)
        except ValueError:
            errors.append(f"Invalid CORE error code: {event_code}")

    elif packet_type == PktType.TIMEOUT:
        try:
            CORETimeoutCode(event_code)
        except ValueError:
            errors.append(f"Invalid CORE timeout code: {event_code}")

    elif packet_type == PktType.THRESHOLD:
        try:
            COREThresholdCode(event_code)
        except ValueError:
            errors.append(f"Invalid CORE threshold code: {event_code}")

    elif packet_type == PktType.PERF:
        try:
            COREPerformanceCode(event_code)
        except ValueError:
            errors.append(f"Invalid CORE performance code: {event_code}")

    elif packet_type == PktType.COMPLETION:
        try:
            CORECompletionCode(event_code)
        except ValueError:
            errors.append(f"Invalid CORE completion code: {event_code}")

    elif packet_type == PktType.DEBUG:
        try:
            COREDebugCode(event_code)
        except ValueError:
            errors.append(f"Invalid CORE debug code: {event_code}")

    return errors


# =============================================================================
# PACKET MATCHER FUNCTIONS - UPDATED
# =============================================================================

def create_packet_matcher(protocol: Union[ProtocolType, int] = None,
                        packet_type: Union[PktType, int] = None,
                        event_code: Union[IntEnum, int] = None,
                        channel_id: int = None,
                        unit_id: int = None,
                        agent_id: int = None,
                        data: int = None,
                        data_mask: int = None) -> Callable[[MonbusPacket], bool]:
    """
    Create a packet matching function for filtering

    Args:
        Various packet fields to match (None means don't check that field)
        data_mask: Optional mask for data field comparison (35-bit max)

    Returns:
        Function that takes a MonbusPacket and returns True if it matches
    """
    def matcher(packet: MonbusPacket) -> bool:
        if protocol is not None:
            protocol_val = protocol.value if hasattr(protocol, 'value') else protocol
            if packet.protocol != protocol_val:
                return False

        if packet_type is not None:
            pkt_type_val = packet_type.value if hasattr(packet_type, 'value') else packet_type
            if packet.pkt_type != pkt_type_val:
                return False

        if event_code is not None:
            event_code_val = event_code.value if hasattr(event_code, 'value') else event_code
            if packet.event_code != event_code_val:
                return False

        if channel_id is not None and packet.channel_id != channel_id:
            return False

        if unit_id is not None and packet.unit_id != unit_id:
            return False

        if agent_id is not None and packet.agent_id != agent_id:
            return False

        if data is not None:
            if data_mask is not None:
                if (packet.data & data_mask) != (data & data_mask):
                    return False
            else:
                if packet.data != data:
                    return False

        return True

    return matcher


def create_arb_error_matcher(error_code: ARBErrorCode = None,
                        client_id: int = None) -> Callable[[MonbusPacket], bool]:
    """Create matcher for ARB error packets"""
    return create_packet_matcher(
        protocol=ProtocolType.PROTOCOL_ARB,
        packet_type=PktType.ERROR,
        event_code=error_code,
        channel_id=client_id
    )


def create_arb_starvation_matcher(client_id: int = None) -> Callable[[MonbusPacket], bool]:
    """Create matcher for ARB starvation events"""
    return create_arb_error_matcher(ARBErrorCode.STARVATION, client_id)


def create_arb_fairness_matcher(client_id: int = None) -> Callable[[MonbusPacket], bool]:
    """Create matcher for ARB fairness violation events"""
    return create_arb_error_matcher(ARBErrorCode.FAIRNESS_VIOLATION, client_id)


def create_arb_threshold_matcher(threshold_code: ARBThresholdCode = None,
                            client_id: int = None) -> Callable[[MonbusPacket], bool]:
    """Create matcher for ARB threshold events"""
    return create_packet_matcher(
        protocol=ProtocolType.PROTOCOL_ARB,
        packet_type=PktType.THRESHOLD,
        event_code=threshold_code,
        channel_id=client_id
    )


def create_arb_performance_matcher(perf_code: ARBPerformanceCode = None) -> Callable[[MonbusPacket], bool]:
    """Create matcher for ARB performance events"""
    return create_packet_matcher(
        protocol=ProtocolType.PROTOCOL_ARB,
        packet_type=PktType.PERF,
        event_code=perf_code
    )


# =============================================================================
# CORE PROTOCOL MATCHERS - NEW
# =============================================================================

# def create_core_error_matcher(error_code: COREErrorCode = None,
#                         channel_id: int = None) -> Callable[[MonbusPacket], bool]:
#     """Create matcher for CORE error packets - NEW"""
#     return create_packet_matcher(
#         protocol=ProtocolType.PROTOCOL_CORE,
#         packet_type=PktType.ERROR,
#         event_code=error_code,
#         channel_id=channel_id
#     )


# def create_core_descriptor_error_matcher(channel_id: int = None) -> Callable[[MonbusPacket], bool]:
#     """Create matcher for CORE descriptor malformed events - NEW"""
#     return create_core_error_matcher(COREErrorCode.DESCRIPTOR_MALFORMED, channel_id)


# def create_core_credit_error_matcher(channel_id: int = None) -> Callable[[MonbusPacket], bool]:
#     """Create matcher for CORE credit underflow events - NEW"""
#     return create_core_error_matcher(COREErrorCode.CREDIT_UNDERFLOW, channel_id)


# def create_core_timeout_matcher(timeout_code: CORETimeoutCode = None,
#                             channel_id: int = None) -> Callable[[MonbusPacket], bool]:
#     """Create matcher for CORE timeout events - NEW"""
#     return create_packet_matcher(
#         protocol=ProtocolType.PROTOCOL_CORE,
#         packet_type=PktType.TIMEOUT,
#         event_code=timeout_code,
#         channel_id=channel_id
#     )


# def create_core_completion_matcher(completion_code: CORECompletionCode = None,
#                                 channel_id: int = None) -> Callable[[MonbusPacket], bool]:
#     """Create matcher for CORE completion events - NEW"""
#     return create_packet_matcher(
#         protocol=ProtocolType.PROTOCOL_CORE,
#         packet_type=PktType.COMPLETION,
#         event_code=completion_code,
#         channel_id=channel_id
#     )


# def create_core_threshold_matcher(threshold_code: COREThresholdCode = None,
#                                 channel_id: int = None) -> Callable[[MonbusPacket], bool]:
#     """Create matcher for CORE threshold events - NEW"""
#     return create_packet_matcher(
#         protocol=ProtocolType.PROTOCOL_CORE,
#         packet_type=PktType.THRESHOLD,
#         event_code=threshold_code,
#         channel_id=channel_id
#     )


# def create_core_performance_matcher(perf_code: COREPerformanceCode = None,
#                                 channel_id: int = None) -> Callable[[MonbusPacket], bool]:
#     """Create matcher for CORE performance events - NEW"""
#     return create_packet_matcher(
#         protocol=ProtocolType.PROTOCOL_CORE,
#         packet_type=PktType.PERF,
#         event_code=perf_code,
#         channel_id=channel_id
#     )


# =============================================================================
# PACKET SEARCH FUNCTIONS - UPDATED
# =============================================================================

def find_packets(packets: List[MonbusPacket],
                matcher: Callable[[MonbusPacket], bool]) -> List[MonbusPacket]:
    """
    Find packets matching a matcher function

    Args:
        packets: List of packets to search
        matcher: Function that returns True for matching packets

    Returns:
        List of matching packets
    """
    return [p for p in packets if matcher(p)]


def find_packets_by_criteria(packets: List[MonbusPacket], **criteria) -> List[MonbusPacket]:
    """
    Find packets matching specified criteria

    Args:
        packets: List of packets to search
        **criteria: Field names and values to match

    Returns:
        List of matching packets
    """
    return [p for p in packets if p.matches(**criteria)]


def find_error_packets(packets: List[MonbusPacket],
                    protocol: Union[ProtocolType, int] = None) -> List[MonbusPacket]:
    """Find all error packets, optionally filtered by protocol"""
    matcher = create_packet_matcher(
        protocol=protocol,
        packet_type=PktType.ERROR
    )
    return find_packets(packets, matcher)


def find_arb_packets(packets: List[MonbusPacket],
                    packet_type: Union[PktType, int] = None) -> List[MonbusPacket]:
    """Find all ARB protocol packets, optionally filtered by packet type"""
    matcher = create_packet_matcher(
        protocol=ProtocolType.PROTOCOL_ARB,
        packet_type=packet_type
    )
    return find_packets(packets, matcher)


def find_core_packets(packets: List[MonbusPacket],
                    packet_type: Union[PktType, int] = None) -> List[MonbusPacket]:
    """Find all CORE protocol packets, optionally filtered by packet type - NEW"""
    matcher = create_packet_matcher(
        protocol=ProtocolType.PROTOCOL_CORE,
        packet_type=packet_type
    )
    return find_packets(packets, matcher)


def find_arb_starvation_events(packets: List[MonbusPacket],
                            client_id: int = None) -> List[MonbusPacket]:
    """Find ARB starvation events, optionally for specific client"""
    matcher = create_arb_starvation_matcher(client_id)
    return find_packets(packets, matcher)


def find_arb_fairness_violations(packets: List[MonbusPacket],
                                client_id: int = None) -> List[MonbusPacket]:
    """Find ARB fairness violations, optionally for specific client"""
    matcher = create_arb_fairness_matcher(client_id)
    return find_packets(packets, matcher)


def find_core_descriptor_errors(packets: List[MonbusPacket],
                            channel_id: int = None) -> List[MonbusPacket]:
    """Find CORE descriptor malformed events, optionally for specific channel - NEW"""
    matcher = create_core_descriptor_error_matcher(channel_id)
    return find_packets(packets, matcher)


def find_core_credit_errors(packets: List[MonbusPacket],
                        channel_id: int = None) -> List[MonbusPacket]:
    """Find CORE credit underflow events, optionally for specific channel - NEW"""
    matcher = create_core_credit_error_matcher(channel_id)
    return find_packets(packets, matcher)


def find_packets_in_time_range(packets: List[MonbusPacket],
                            start_time: float, end_time: float) -> List[MonbusPacket]:
    """Find packets within a specific time range"""
    return [p for p in packets if start_time <= p.timestamp <= end_time]


def find_sequential_packets(packets: List[MonbusPacket],
                        channel_id: int) -> List[MonbusPacket]:
    """Find packets for a specific channel in chronological order"""
    channel_packets = [p for p in packets if p.channel_id == channel_id]
    return sorted(channel_packets, key=lambda p: p.timestamp)


# =============================================================================
# PACKET ANALYSIS FUNCTIONS - UPDATED
# =============================================================================

def analyze_packet_distribution(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Analyze the distribution of packet types and protocols including ARB and CORE

    Args:
        packets: List of packets to analyze

    Returns:
        Dictionary with distribution statistics
    """
    analysis = {
        'total_packets': len(packets),
        'protocol_distribution': {},
        'packet_type_distribution': {},
        'event_code_distribution': {},
        'channel_distribution': {},
        'agent_distribution': {},
        'unit_distribution': {},
        'arb_specific_analysis': {},
        'core_specific_analysis': {}  # ✅ NEW
    }

    if not packets:
        return analysis

    # Protocol distribution including ARB and CORE
    for protocol in ProtocolType:
        count = len([p for p in packets if p.protocol == protocol.value])
        analysis['protocol_distribution'][protocol.name] = count

    # Packet type distribution
    for pkt_type in PktType:
        count = len([p for p in packets if p.pkt_type == pkt_type.value])
        analysis['packet_type_distribution'][pkt_type.name] = count

    # Event code distribution by protocol
    for protocol in ProtocolType:
        protocol_packets = [p for p in packets if p.protocol == protocol.value]
        if protocol_packets:
            event_codes = {}
            for packet in protocol_packets:
                event_codes[packet.event_code] = event_codes.get(packet.event_code, 0) + 1
            analysis['event_code_distribution'][protocol.name] = event_codes

    # Channel, agent, unit distributions
    for field, field_name in [('channel_id', 'channel_distribution'),
                            ('agent_id', 'agent_distribution'),
                            ('unit_id', 'unit_distribution')]:
        field_counts = {}
        for packet in packets:
            field_value = getattr(packet, field)
            field_counts[field_value] = field_counts.get(field_value, 0) + 1
        analysis[field_name] = field_counts

    # ARB-specific analysis
    arb_packets = find_arb_packets(packets)
    if arb_packets:
        analysis['arb_specific_analysis'] = analyze_arb_packets(arb_packets)

    # CORE-specific analysis - NEW
    core_packets = find_core_packets(packets)
    if core_packets:
        analysis['core_specific_analysis'] = analyze_core_packets(core_packets)

    return analysis


def analyze_arb_packets(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Analyze ARB protocol specific packet patterns

    Args:
        packets: List of ARB protocol packets

    Returns:
        Dictionary with ARB-specific analysis
    """
    analysis = {
        'total_arb_packets': len(packets),
        'error_breakdown': {},
        'timeout_breakdown': {},
        'threshold_breakdown': {},
        'performance_breakdown': {},
        'completion_breakdown': {},
        'debug_breakdown': {},
        'client_activity': {},
        'starvation_analysis': {},
        'fairness_analysis': {}
    }

    if not packets:
        return analysis

    # Breakdown by packet type and event code
    for packet in packets:
        try:
            pkt_type = PktType(packet.pkt_type)
        except ValueError:
            continue

        if pkt_type == PktType.ERROR:
            try:
                error_code = ARBErrorCode(packet.event_code)
                analysis['error_breakdown'][error_code.name] = \
                    analysis['error_breakdown'].get(error_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.TIMEOUT:
            try:
                timeout_code = ARBTimeoutCode(packet.event_code)
                analysis['timeout_breakdown'][timeout_code.name] = \
                    analysis['timeout_breakdown'].get(timeout_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.THRESHOLD:
            try:
                threshold_code = ARBThresholdCode(packet.event_code)
                analysis['threshold_breakdown'][threshold_code.name] = \
                    analysis['threshold_breakdown'].get(threshold_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.PERF:
            try:
                perf_code = ARBPerformanceCode(packet.event_code)
                analysis['performance_breakdown'][perf_code.name] = \
                    analysis['performance_breakdown'].get(perf_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.COMPLETION:
            try:
                comp_code = ARBCompletionCode(packet.event_code)
                analysis['completion_breakdown'][comp_code.name] = \
                    analysis['completion_breakdown'].get(comp_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.DEBUG:
            try:
                debug_code = ARBDebugCode(packet.event_code)
                analysis['debug_breakdown'][debug_code.name] = \
                    analysis['debug_breakdown'].get(debug_code.name, 0) + 1
            except ValueError:
                pass

    # Client activity analysis
    for packet in packets:
        client_id = packet.channel_id
        if client_id not in analysis['client_activity']:
            analysis['client_activity'][client_id] = {
                'total_events': 0,
                'errors': 0,
                'starvation_events': 0,
                'fairness_violations': 0,
                'threshold_violations': 0
            }

        analysis['client_activity'][client_id]['total_events'] += 1

        if packet.is_error_packet():
            analysis['client_activity'][client_id]['errors'] += 1

            if packet.event_code == ARBErrorCode.STARVATION.value:
                analysis['client_activity'][client_id]['starvation_events'] += 1
            elif packet.event_code == ARBErrorCode.FAIRNESS_VIOLATION.value:
                analysis['client_activity'][client_id]['fairness_violations'] += 1

        elif packet.is_threshold_packet():
            analysis['client_activity'][client_id]['threshold_violations'] += 1

    # Starvation-specific analysis
    starvation_packets = find_arb_starvation_events(packets)
    if starvation_packets:
        analysis['starvation_analysis'] = {
            'total_starvation_events': len(starvation_packets),
            'clients_affected': len(set(p.channel_id for p in starvation_packets)),
            'avg_starvation_data': statistics.mean(p.data for p in starvation_packets),
            'max_starvation_data': max(p.data for p in starvation_packets),
            'starvation_by_client': {}
        }

        for packet in starvation_packets:
            client_id = packet.channel_id
            if client_id not in analysis['starvation_analysis']['starvation_by_client']:
                analysis['starvation_analysis']['starvation_by_client'][client_id] = []
            analysis['starvation_analysis']['starvation_by_client'][client_id].append(packet.data)

    # Fairness-specific analysis
    fairness_packets = find_arb_fairness_violations(packets)
    if fairness_packets:
        analysis['fairness_analysis'] = {
            'total_fairness_violations': len(fairness_packets),
            'clients_affected': len(set(p.channel_id for p in fairness_packets)),
            'avg_deviation': statistics.mean(p.data for p in fairness_packets),
            'max_deviation': max(p.data for p in fairness_packets),
            'violations_by_client': {}
        }

        for packet in fairness_packets:
            client_id = packet.channel_id
            if client_id not in analysis['fairness_analysis']['violations_by_client']:
                analysis['fairness_analysis']['violations_by_client'][client_id] = []
            analysis['fairness_analysis']['violations_by_client'][client_id].append(packet.data)

    return analysis


def analyze_core_packets(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Analyze CORE protocol specific packet patterns - NEW

    Args:
        packets: List of CORE protocol packets

    Returns:
        Dictionary with CORE-specific analysis
    """
    analysis = {
        'total_core_packets': len(packets),
        'error_breakdown': {},
        'timeout_breakdown': {},
        'threshold_breakdown': {},
        'performance_breakdown': {},
        'completion_breakdown': {},
        'debug_breakdown': {},
        'channel_activity': {},
        'descriptor_analysis': {},
        'credit_analysis': {},
        'fsm_analysis': {}
    }

    if not packets:
        return analysis

    # Breakdown by packet type and event code
    for packet in packets:
        try:
            pkt_type = PktType(packet.pkt_type)
        except ValueError:
            continue

        if pkt_type == PktType.ERROR:
            try:
                error_code = COREErrorCode(packet.event_code)
                analysis['error_breakdown'][error_code.name] = \
                    analysis['error_breakdown'].get(error_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.TIMEOUT:
            try:
                timeout_code = CORETimeoutCode(packet.event_code)
                analysis['timeout_breakdown'][timeout_code.name] = \
                    analysis['timeout_breakdown'].get(timeout_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.THRESHOLD:
            try:
                threshold_code = COREThresholdCode(packet.event_code)
                analysis['threshold_breakdown'][threshold_code.name] = \
                    analysis['threshold_breakdown'].get(threshold_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.PERF:
            try:
                perf_code = COREPerformanceCode(packet.event_code)
                analysis['performance_breakdown'][perf_code.name] = \
                    analysis['performance_breakdown'].get(perf_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.COMPLETION:
            try:
                comp_code = CORECompletionCode(packet.event_code)
                analysis['completion_breakdown'][comp_code.name] = \
                    analysis['completion_breakdown'].get(comp_code.name, 0) + 1
            except ValueError:
                pass

        elif pkt_type == PktType.DEBUG:
            try:
                debug_code = COREDebugCode(packet.event_code)
                analysis['debug_breakdown'][debug_code.name] = \
                    analysis['debug_breakdown'].get(debug_code.name, 0) + 1
            except ValueError:
                pass

    # Channel activity analysis
    for packet in packets:
        channel_id = packet.channel_id
        if channel_id not in analysis['channel_activity']:
            analysis['channel_activity'][channel_id] = {
                'total_events': 0,
                'errors': 0,
                'descriptor_errors': 0,
                'credit_errors': 0,
                'timeouts': 0,
                'completions': 0
            }

        analysis['channel_activity'][channel_id]['total_events'] += 1

        if packet.is_error_packet():
            analysis['channel_activity'][channel_id]['errors'] += 1

            if packet.event_code == COREErrorCode.DESCRIPTOR_MALFORMED.value:
                analysis['channel_activity'][channel_id]['descriptor_errors'] += 1
            elif packet.event_code == COREErrorCode.CREDIT_UNDERFLOW.value:
                analysis['channel_activity'][channel_id]['credit_errors'] += 1

        elif packet.is_timeout_packet():
            analysis['channel_activity'][channel_id]['timeouts'] += 1

        elif packet.is_completion_packet():
            analysis['channel_activity'][channel_id]['completions'] += 1

    # Descriptor-specific analysis
    descriptor_packets = find_core_descriptor_errors(packets)
    if descriptor_packets:
        analysis['descriptor_analysis'] = {
            'total_descriptor_errors': len(descriptor_packets),
            'channels_affected': len(set(p.channel_id for p in descriptor_packets)),
            'avg_error_data': statistics.mean(p.data for p in descriptor_packets),
            'max_error_data': max(p.data for p in descriptor_packets),
            'errors_by_channel': {}
        }

        for packet in descriptor_packets:
            channel_id = packet.channel_id
            if channel_id not in analysis['descriptor_analysis']['errors_by_channel']:
                analysis['descriptor_analysis']['errors_by_channel'][channel_id] = []
            analysis['descriptor_analysis']['errors_by_channel'][channel_id].append(packet.data)

    # Credit-specific analysis
    credit_packets = find_core_credit_errors(packets)
    if credit_packets:
        analysis['credit_analysis'] = {
            'total_credit_errors': len(credit_packets),
            'channels_affected': len(set(p.channel_id for p in credit_packets)),
            'avg_credit_data': statistics.mean(p.data for p in credit_packets),
            'max_credit_data': max(p.data for p in credit_packets),
            'errors_by_channel': {}
        }

        for packet in credit_packets:
            channel_id = packet.channel_id
            if channel_id not in analysis['credit_analysis']['errors_by_channel']:
                analysis['credit_analysis']['errors_by_channel'][channel_id] = []
            analysis['credit_analysis']['errors_by_channel'][channel_id].append(packet.data)

    # FSM state analysis (from debug packets)
    fsm_packets = []
    for packet in packets:
        if (packet.is_debug_packet() and 
            packet.event_code == COREDebugCode.FSM_STATE_CHANGE.value):
            fsm_packets.append(packet)

    if fsm_packets:
        analysis['fsm_analysis'] = {
            'total_state_changes': len(fsm_packets),
            'channels_with_changes': len(set(p.channel_id for p in fsm_packets)),
            'state_transitions': []
        }

        for packet in fsm_packets:
            # Assume data field contains state transition info
            analysis['fsm_analysis']['state_transitions'].append({
                'channel_id': packet.channel_id,
                'timestamp': packet.timestamp,
                'state_data': packet.data
            })

    return analysis


def measure_latency_metrics(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Measure latency-related metrics from packets

    Args:
        packets: List of packets to analyze

    Returns:
        Dictionary with latency statistics
    """
    analysis = {
        'total_packets': len(packets),
        'latency_events': [],
        'avg_latency': 0,
        'max_latency': 0,
        'min_latency': 0,
        'latency_distribution': {}
    }

    if not packets:
        return analysis

    # Extract latency data from ARB threshold packets
    latency_packets = []
    for packet in packets:
        if (packet.is_arb_protocol() and
            packet.is_threshold_packet() and
            packet.event_code == ARBThresholdCode.REQUEST_LATENCY.value):
            latency_packets.append(packet)
            analysis['latency_events'].append({
                'client_id': packet.channel_id,
                'latency_value': packet.data,
                'latency_type': ARBThresholdCode.REQUEST_LATENCY.name,
                'timestamp': packet.timestamp
            })

        # Also check CORE latency thresholds - NEW
        elif (packet.is_core_protocol() and
              packet.is_threshold_packet() and
              packet.event_code == COREThresholdCode.LATENCY.value):
            latency_packets.append(packet)
            analysis['latency_events'].append({
                'channel_id': packet.channel_id,
                'latency_value': packet.data,
                'latency_type': COREThresholdCode.LATENCY.name,
                'timestamp': packet.timestamp
            })

    if latency_packets:
        latency_values = [p.data for p in latency_packets]
        analysis['avg_latency'] = statistics.mean(latency_values)
        analysis['max_latency'] = max(latency_values)
        analysis['min_latency'] = min(latency_values)

        # Create latency distribution
        for value in latency_values:
            range_key = f"{(value // 10) * 10}-{(value // 10) * 10 + 9}"
            analysis['latency_distribution'][range_key] = \
                analysis['latency_distribution'].get(range_key, 0) + 1

    return analysis


def analyze_grant_fairness(packets: List[MonbusPacket], num_clients: int) -> Dict[str, Any]:
    """
    Analyze fairness of grant distribution from ARB completion events

    Args:
        packets: List of packets to analyze
        num_clients: Number of clients in the system

    Returns:
        Dictionary with fairness analysis
    """
    # Find ARB grant completion events
    grant_packets = []
    for packet in packets:
        if (packet.is_arb_protocol() and
            packet.is_completion_packet() and
            packet.event_code == ARBCompletionCode.GRANT_ISSUED.value):
            grant_packets.append(packet)

    grants_per_client = {i: 0 for i in range(num_clients)}

    for packet in grant_packets:
        if packet.channel_id < num_clients:
            grants_per_client[packet.channel_id] += 1

    total_grants = sum(grants_per_client.values())
    expected_per_client = total_grants / num_clients if num_clients > 0 else 0

    analysis = {
        'total_grants': total_grants,
        'grants_per_client': grants_per_client,
        'expected_per_client': expected_per_client,
        'fairness_deviation': {},
        'max_deviation': 0,
        'fairness_index': 0  # Jain's fairness index
    }

    if total_grants > 0:
        # Calculate deviations
        for client_id, grants in grants_per_client.items():
            deviation = abs(grants - expected_per_client) / expected_per_client * 100 if expected_per_client > 0 else 0
            analysis['fairness_deviation'][client_id] = deviation
            analysis['max_deviation'] = max(analysis['max_deviation'], deviation)

        # Calculate Jain's fairness index
        sum_grants = sum(grants_per_client.values())
        sum_grants_squared = sum(g*g for g in grants_per_client.values())

        if sum_grants_squared > 0:
            analysis['fairness_index'] = (sum_grants * sum_grants) / (num_clients * sum_grants_squared)

    return analysis


# =============================================================================
# SEQUENCE VALIDATION FUNCTIONS - UPDATED
# =============================================================================

def validate_packet_sequence(packets: List[MonbusPacket],
                        expected_sequence: List[Dict[str, Any]],
                        strict_order: bool = True) -> Dict[str, Any]:
    """
    Validate a sequence of packets against expected patterns

    Args:
        packets: List of packets to validate
        expected_sequence: List of expected packet patterns
        strict_order: If True, packets must be in exact order

    Returns:
        Validation result dictionary
    """
    result = {
        'valid': False,
        'matched_count': 0,
        'total_expected': len(expected_sequence),
        'errors': [],
        'matched_packets': []
    }

    if strict_order:
        # Strict order validation
        if len(packets) < len(expected_sequence):
            result['errors'].append(f"Not enough packets: got {len(packets)}, expected {len(expected_sequence)}")
            return result

        for i, expected in enumerate(expected_sequence):
            if i >= len(packets):
                result['errors'].append(f"Missing packet at index {i}")
                break

            packet = packets[i]
            if packet.matches(**expected):
                result['matched_count'] += 1
                result['matched_packets'].append(packet)
            else:
                result['errors'].append(f"Packet {i} doesn't match expected pattern")
                result['errors'].append(f"  Expected: {expected}")
                result['errors'].append(f"  Got: {packet.to_dict()}")
                break
    else:
        # Flexible order validation
        remaining_packets = packets.copy()

        for i, expected in enumerate(expected_sequence):
            found = False
            for j, packet in enumerate(remaining_packets):
                if packet.matches(**expected):
                    result['matched_count'] += 1
                    result['matched_packets'].append(packet)
                    remaining_packets.pop(j)
                    found = True
                    break

            if not found:
                result['errors'].append(f"Expected packet {i} not found: {expected}")

    result['valid'] = (result['matched_count'] == len(expected_sequence)) and (len(result['errors']) == 0)
    return result


def validate_arb_starvation_sequence(packets: List[MonbusPacket],
                                expected_clients: List[int],
                                max_time_between: float = 1.0) -> Dict[str, Any]:
    """
    Validate ARB starvation event sequence

    Args:
        packets: List of packets to validate
        expected_clients: List of client IDs expected to have starvation
        max_time_between: Maximum time between starvation events

    Returns:
        Validation result dictionary
    """
    starvation_packets = find_arb_starvation_events(packets)

    result = {
        'valid': True,
        'found_clients': [],
        'missing_clients': [],
        'extra_clients': [],
        'timing_violations': [],
        'starvation_events': len(starvation_packets)
    }

    # Check which clients had starvation events
    found_clients = list(set(p.channel_id for p in starvation_packets))
    result['found_clients'] = found_clients

    # Find missing and extra clients
    result['missing_clients'] = [c for c in expected_clients if c not in found_clients]
    result['extra_clients'] = [c for c in found_clients if c not in expected_clients]

    # Check timing between events
    if len(starvation_packets) > 1:
        sorted_packets = sorted(starvation_packets, key=lambda p: p.timestamp)
        for i in range(1, len(sorted_packets)):
            time_diff = sorted_packets[i].timestamp - sorted_packets[i-1].timestamp
            if time_diff > max_time_between:
                result['timing_violations'].append({
                    'index': i,
                    'time_gap': time_diff,
                    'max_allowed': max_time_between
                })

    # Overall validation
    result['valid'] = (len(result['missing_clients']) == 0 and
                    len(result['extra_clients']) == 0 and
                    len(result['timing_violations']) == 0)

    return result


def validate_core_descriptor_sequence(packets: List[MonbusPacket],
                                    expected_channels: List[int],
                                    max_time_between: float = 1.0) -> Dict[str, Any]:
    """
    Validate CORE descriptor error event sequence - NEW

    Args:
        packets: List of packets to validate
        expected_channels: List of channel IDs expected to have descriptor errors
        max_time_between: Maximum time between descriptor error events

    Returns:
        Validation result dictionary
    """
    descriptor_packets = find_core_descriptor_errors(packets)

    result = {
        'valid': True,
        'found_channels': [],
        'missing_channels': [],
        'extra_channels': [],
        'timing_violations': [],
        'descriptor_errors': len(descriptor_packets)
    }

    # Check which channels had descriptor errors
    found_channels = list(set(p.channel_id for p in descriptor_packets))
    result['found_channels'] = found_channels

    # Find missing and extra channels
    result['missing_channels'] = [c for c in expected_channels if c not in found_channels]
    result['extra_channels'] = [c for c in found_channels if c not in expected_channels]

    # Check timing between events
    if len(descriptor_packets) > 1:
        sorted_packets = sorted(descriptor_packets, key=lambda p: p.timestamp)
        for i in range(1, len(sorted_packets)):
            time_diff = sorted_packets[i].timestamp - sorted_packets[i-1].timestamp
            if time_diff > max_time_between:
                result['timing_violations'].append({
                    'index': i,
                    'time_gap': time_diff,
                    'max_allowed': max_time_between
                })

    # Overall validation
    result['valid'] = (len(result['missing_channels']) == 0 and
                    len(result['extra_channels']) == 0 and
                    len(result['timing_violations']) == 0)

    return result


def validate_state_machine_sequence(packets: List[MonbusPacket],
                                state_transitions: List[Tuple[Dict[str, Any], Dict[str, Any]]]) -> Dict[str, Any]:
    """
    Validate packets represent valid state machine transitions

    Args:
        packets: List of packets to validate
        state_transitions: List of (from_state, to_state) tuples

    Returns:
        Validation result dictionary
    """
    result = {
        'valid': True,
        'transitions_found': 0,
        'invalid_transitions': [],
        'missing_transitions': []
    }

    # Find state change debug packets (ARB and CORE)
    state_packets = []
    for packet in packets:
        if ((packet.is_arb_protocol() and
             packet.is_debug_packet() and
             packet.event_code == ARBDebugCode.STATE_CHANGE.value) or
            (packet.is_core_protocol() and
             packet.is_debug_packet() and
             packet.event_code == COREDebugCode.FSM_STATE_CHANGE.value)):
            state_packets.append(packet)

    # Extract state transitions from packets
    found_transitions = []
    for packet in state_packets:
        # Assume data field contains old_state << 16 | new_state
        old_state = (packet.data >> 16) & 0xFFFF
        new_state = packet.data & 0xFFFF
        found_transitions.append((old_state, new_state))

    result['transitions_found'] = len(found_transitions)

    # Validate expected transitions are present
    for expected_from, expected_to in state_transitions:
        from_state = expected_from.get('state', 0)
        to_state = expected_to.get('state', 0)

        if (from_state, to_state) not in found_transitions:
            result['missing_transitions'].append((from_state, to_state))
            result['valid'] = False

    return result


# =============================================================================
# REPORTING FUNCTIONS - UPDATED
# =============================================================================

def generate_validation_report(packets: List[MonbusPacket],
                            validation_results: List[Dict[str, Any]]) -> str:
    """
    Generate a comprehensive validation report

    Args:
        packets: List of packets analyzed
        validation_results: List of validation result dictionaries

    Returns:
        Formatted validation report string
    """
    lines = [
        "=== MonBus Packet Validation Report ===",
        f"Total packets analyzed: {len(packets)}",
        f"Validation tests performed: {len(validation_results)}",
        ""
    ]

    # Summary statistics
    distribution = analyze_packet_distribution(packets)
    lines.extend([
        "Protocol Distribution:",
        *[f"  {proto}: {count}" for proto, count in distribution['protocol_distribution'].items() if count > 0],
        "",
        "Packet Type Distribution:",
        *[f"  {ptype}: {count}" for ptype, count in distribution['packet_type_distribution'].items() if count > 0],
        ""
    ])

    # ARB-specific analysis if present
    if distribution['protocol_distribution'].get('PROTOCOL_ARB', 0) > 0:
        arb_analysis = distribution['arb_specific_analysis']
        lines.extend([
            "ARB Protocol Analysis:",
            f"  Total ARB packets: {arb_analysis['total_arb_packets']}",
            ""
        ])

        if arb_analysis['error_breakdown']:
            lines.append("  Error Breakdown:")
            lines.extend([f"    {error}: {count}" for error, count in arb_analysis['error_breakdown'].items()])
            lines.append("")

    # CORE-specific analysis if present - NEW
    if distribution['protocol_distribution'].get('PROTOCOL_CORE', 0) > 0:
        core_analysis = distribution['core_specific_analysis']
        lines.extend([
            "CORE Protocol Analysis:",
            f"  Total CORE packets: {core_analysis['total_core_packets']}",
            ""
        ])

        if core_analysis['error_breakdown']:
            lines.append("  Error Breakdown:")
            lines.extend([f"    {error}: {count}" for error, count in core_analysis['error_breakdown'].items()])
            lines.append("")

    # Validation results
    passed = sum(1 for result in validation_results if result.get('valid', False))
    failed = len(validation_results) - passed

    lines.extend([
        f"Validation Results: {passed} passed, {failed} failed",
        ""
    ])

    for i, result in enumerate(validation_results):
        status = "PASS" if result.get('valid', False) else "FAIL"
        lines.append(f"Test {i+1}: {status}")

        if result.get('errors'):
            lines.extend([f"  Error: {error}" for error in result['errors'][:3]])  # Limit errors shown
            if len(result['errors']) > 3:
                lines.append(f"  ... and {len(result['errors']) - 3} more errors")

        lines.append("")

    return "\n".join(lines)