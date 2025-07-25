"""
MonBus Validation Helper Functions

This module provides validation functions, packet matchers, and analysis tools
for MonBus packet validation and testing.
"""

from typing import List, Dict, Any, Callable, Union, Optional, Tuple
from enum import IntEnum
import statistics

from .monbus_types import ProtocolType, PktType
from .monbus_packet import MonbusPacket


# =============================================================================
# PACKET VALIDATION FUNCTIONS
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
    Validate that packet enum fields have valid values

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
        PktType(packet.packet_type)
    except ValueError:
        errors.append(f"Invalid packet_type value: {packet.packet_type}")

    # Check event code validity
    if not packet.is_valid_event_code():
        errors.append(f"Invalid event_code {packet.event_code} for "
                        f"{packet.get_protocol_name()}.{packet.get_packet_type_name()}")

    return errors


def validate_packet_consistency(packet: MonbusPacket) -> List[str]:
    """
    Validate packet internal consistency

    Args:
        packet: MonbusPacket to validate

    Returns:
        List of error messages (empty if all valid)
    """
    errors = []

    # Check basic field ranges
    field_ranges = {
        'protocol': (0, 3),         # 2 bits
        'packet_type': (0, 15),     # 4 bits
        'event_code': (0, 15),      # 4 bits
        'unit_id': (0, 15),         # 4 bits
        'channel_id': (0, 63),      # 6 bits
        'agent_id': (0, 255),       # 8 bits
        'data': (0, (1 << 36) - 1)  # 36 bits
    }

    errors.extend(validate_packet_range(packet, field_ranges))
    errors.extend(validate_packet_enum_fields(packet))

    return errors


# =============================================================================
# PACKET MATCHER FUNCTIONS
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
        data_mask: Optional mask for data field comparison

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
            if packet.packet_type != pkt_type_val:
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


def create_range_matcher(field_ranges: Dict[str, Tuple[int, int]]) -> Callable[[MonbusPacket], bool]:
    """
    Create a matcher for packets with fields in specified ranges

    Args:
        field_ranges: Dict of field_name -> (min_value, max_value)

    Returns:
        Function that returns True if all fields are in range
    """
    def matcher(packet: MonbusPacket) -> bool:
        for field_name, (min_val, max_val) in field_ranges.items():
            if hasattr(packet, field_name):
                actual_value = getattr(packet, field_name)
                if not (min_val <= actual_value <= max_val):
                    return False
            else:
                return False  # Field doesn't exist
        return True

    return matcher


def create_temporal_matcher(time_window: float) -> Callable[[MonbusPacket], bool]:
    """
    Create a matcher for packets within a time window

    Args:
        time_window: Time window in seconds from current time

    Returns:
        Function that returns True if packet is within time window
    """
    import time

    def matcher(packet: MonbusPacket) -> bool:
        current_time = time.time()
        return (current_time - packet.timestamp) <= time_window

    return matcher


# =============================================================================
# PACKET SEARCH AND FILTER FUNCTIONS
# =============================================================================

def find_packets(packets: List[MonbusPacket],
                matcher: Callable[[MonbusPacket], bool]) -> List[MonbusPacket]:
    """
    Find packets matching a criteria function

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
# PACKET ANALYSIS FUNCTIONS
# =============================================================================

def analyze_packet_distribution(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Analyze the distribution of packet types and protocols

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
        'unit_distribution': {}
    }

    if not packets:
        return analysis

    # Protocol distribution
    for protocol in ProtocolType:
        count = len([p for p in packets if p.protocol == protocol.value])
        if count > 0:
            analysis['protocol_distribution'][protocol.name] = count

    # Packet type distribution
    for pkt_type in PktType:
        count = len([p for p in packets if p.packet_type == pkt_type.value])
        if count > 0:
            analysis['packet_type_distribution'][pkt_type.name] = count

    # Event code distribution
    event_codes = {}
    for packet in packets:
        event_name = packet.get_event_code_name()
        event_codes[event_name] = event_codes.get(event_name, 0) + 1
    analysis['event_code_distribution'] = event_codes

    # Channel distribution
    channels = {}
    for packet in packets:
        channels[packet.channel_id] = channels.get(packet.channel_id, 0) + 1
    analysis['channel_distribution'] = dict(sorted(channels.items()))

    # Agent distribution
    agents = {}
    for packet in packets:
        agents[packet.agent_id] = agents.get(packet.agent_id, 0) + 1
    analysis['agent_distribution'] = dict(sorted(agents.items()))

    # Unit distribution
    units = {}
    for packet in packets:
        units[packet.unit_id] = units.get(packet.unit_id, 0) + 1
    analysis['unit_distribution'] = dict(sorted(units.items()))

    return analysis


def analyze_timing_patterns(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Analyze timing patterns in packet arrival

    Args:
        packets: List of packets to analyze

    Returns:
        Dictionary with timing statistics
    """
    if len(packets) < 2:
        return {'error': 'Need at least 2 packets for timing analysis'}

    # Sort packets by timestamp
    sorted_packets = sorted(packets, key=lambda p: p.timestamp)

    # Calculate inter-arrival times
    inter_arrival_times = []
    for i in range(1, len(sorted_packets)):
        delta = sorted_packets[i].timestamp - sorted_packets[i-1].timestamp
        inter_arrival_times.append(delta)

    analysis = {
        'total_duration': sorted_packets[-1].timestamp - sorted_packets[0].timestamp,
        'packet_rate': len(packets) / (sorted_packets[-1].timestamp - sorted_packets[0].timestamp),
        'inter_arrival_stats': {
            'mean': statistics.mean(inter_arrival_times),
            'median': statistics.median(inter_arrival_times),
            'min': min(inter_arrival_times),
            'max': max(inter_arrival_times),
            'stdev': statistics.stdev(inter_arrival_times) if len(inter_arrival_times) > 1 else 0
        }
    }

    return analysis


def analyze_error_patterns(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Analyze error patterns in packet stream

    Args:
        packets: List of packets to analyze

    Returns:
        Dictionary with error analysis
    """
    error_packets = find_error_packets(packets)

    analysis = {
        'total_errors': len(error_packets),
        'error_rate': len(error_packets) / len(packets) if packets else 0,
        'error_by_protocol': {},
        'error_by_code': {},
        'error_by_channel': {},
        'consecutive_errors': 0
    }

    # Error distribution by protocol
    for protocol in ProtocolType:
        protocol_errors = [p for p in error_packets if p.protocol == protocol.value]
        if protocol_errors:
            analysis['error_by_protocol'][protocol.name] = len(protocol_errors)

    # Error distribution by event code
    for packet in error_packets:
        event_name = packet.get_event_code_name()
        analysis['error_by_code'][event_name] = analysis['error_by_code'].get(event_name, 0) + 1

    # Error distribution by channel
    for packet in error_packets:
        channel = packet.channel_id
        analysis['error_by_channel'][channel] = analysis['error_by_channel'].get(channel, 0) + 1

    # Find consecutive errors
    sorted_packets = sorted(packets, key=lambda p: p.timestamp)
    max_consecutive = 0
    current_consecutive = 0

    for packet in sorted_packets:
        if packet.is_error_packet():
            current_consecutive += 1
            max_consecutive = max(max_consecutive, current_consecutive)
        else:
            current_consecutive = 0

    analysis['consecutive_errors'] = max_consecutive

    return analysis


def analyze_fairness(packets: List[MonbusPacket], num_clients: int) -> Dict[str, Any]:
    """
    Analyze fairness of grants across clients

    Args:
        packets: List of packets to analyze
        num_clients: Number of clients in the system

    Returns:
        Dictionary with fairness analysis
    """
    # Find grant efficiency packets (performance packets with grant data)
    grant_packets = [p for p in packets if p.is_performance_packet()]

    # Count grants per client
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
            deviation = abs(grants - expected_per_client) / expected_per_client * 100
            analysis['fairness_deviation'][client_id] = deviation
            analysis['max_deviation'] = max(analysis['max_deviation'], deviation)

        # Calculate Jain's fairness index
        sum_grants = sum(grants_per_client.values())
        sum_grants_squared = sum(g*g for g in grants_per_client.values())

        if sum_grants_squared > 0:
            analysis['fairness_index'] = (sum_grants * sum_grants) / (num_clients * sum_grants_squared)

    return analysis


# =============================================================================
# SEQUENCE VALIDATION FUNCTIONS
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
                result['errors'].append(f"Packet {i} doesn't match expected pattern: {expected}")
                break
    else:
        # Flexible order validation - find each expected packet somewhere in the list
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

    # This is a placeholder for state machine validation
    # Implementation would depend on specific state machine definition

    return result


# =============================================================================
# PERFORMANCE ANALYSIS FUNCTIONS
# =============================================================================

def measure_latency_metrics(packets: List[MonbusPacket]) -> Dict[str, Any]:
    """
    Measure latency-related metrics from packets

    Args:
        packets: List of packets to analyze

    Returns:
        Dictionary with latency metrics
    """
    # Find latency threshold packets
    latency_packets = [p for p in packets if
                        p.is_threshold_packet() and
                        p.get_event_code_name().endswith('_LATENCY')]

    if not latency_packets:
        return {'error': 'No latency packets found'}

    latencies = [p.data for p in latency_packets]

    metrics = {
        'count': len(latencies),
        'min_latency': min(latencies),
        'max_latency': max(latencies),
        'mean_latency': statistics.mean(latencies),
        'median_latency': statistics.median(latencies)
    }

    if len(latencies) > 1:
        metrics['stdev_latency'] = statistics.stdev(latencies)

    return metrics


def measure_throughput_metrics(packets: List[MonbusPacket],
                                time_window: float = None) -> Dict[str, Any]:
    """
    Measure throughput-related metrics from packets

    Args:
        packets: List of packets to analyze
        time_window: Time window for throughput calculation

    Returns:
        Dictionary with throughput metrics
    """
    if not packets:
        return {'error': 'No packets to analyze'}

    sorted_packets = sorted(packets, key=lambda p: p.timestamp)

    if time_window is None:
        time_window = sorted_packets[-1].timestamp - sorted_packets[0].timestamp

    metrics = {
        'total_packets': len(packets),
        'time_window': time_window,
        'packets_per_second': len(packets) / time_window if time_window > 0 else 0,
        'peak_rate': 0,
        'min_rate': float('inf')
    }

    # Calculate sliding window rates (this is a simplified version)
    window_size = min(10, len(packets) // 4)  # Use 1/4 of packets or 10, whichever is smaller

    if window_size > 1:
        for i in range(len(sorted_packets) - window_size + 1):
            window_packets = sorted_packets[i:i + window_size]
            window_time = window_packets[-1].timestamp - window_packets[0].timestamp

            if window_time > 0:
                rate = window_size / window_time
                metrics['peak_rate'] = max(metrics['peak_rate'], rate)
                metrics['min_rate'] = min(metrics['min_rate'], rate)

    if metrics['min_rate'] == float('inf'):
        metrics['min_rate'] = 0

    return metrics
