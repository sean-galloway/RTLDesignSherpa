"""
MonBus Event Factory Functions

This module provides factory functions for creating expected event dictionaries
using enum constants instead of magic numbers.
"""

from typing import Dict, Any, Union
from .monbus_types import (
    ProtocolType, PktType,
    AXIErrorCode, AXICompletionCode, AXITimeoutCode, AXIThresholdCode,
    AXIPerformanceCode, AXIAddrMatchCode, AXIDebugCode,
    APBErrorCode, APBCompletionCode, APBTimeoutCode, APBThresholdCode,
    APBPerformanceCode, APBDebugCode,
    NOCErrorCode, NOCCreditCode
)


# =============================================================================
# AXI EVENT FACTORIES
# =============================================================================

def create_axi_error_event(error_code: AXIErrorCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI error event"""
    return {
        'packet_type': PktType.ERROR.value,
        'protocol': ProtocolType.AXI.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_axi_completion_event(completion_code: AXICompletionCode, channel_id: int = 0,
                                unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI completion event"""
    return {
        'packet_type': PktType.COMPLETION.value,
        'protocol': ProtocolType.AXI.value,
        'event_code': completion_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_axi_timeout_event(timeout_code: AXITimeoutCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI timeout event"""
    return {
        'packet_type': PktType.TIMEOUT.value,
        'protocol': ProtocolType.AXI.value,
        'event_code': timeout_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_axi_threshold_event(threshold_code: AXIThresholdCode, channel_id: int = 0,
                                unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI threshold event"""
    return {
        'packet_type': PktType.THRESHOLD.value,
        'protocol': ProtocolType.AXI.value,
        'event_code': threshold_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_axi_performance_event(perf_code: AXIPerformanceCode, channel_id: int = 0,
                                unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI performance event"""
    return {
        'packet_type': PktType.PERF.value,
        'protocol': ProtocolType.AXI.value,
        'event_code': perf_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_axi_addr_match_event(addr_match_code: AXIAddrMatchCode, channel_id: int = 0,
                                unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI address match event"""
    return {
        'packet_type': PktType.ADDR_MATCH.value,
        'protocol': ProtocolType.AXI.value,
        'event_code': addr_match_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_axi_debug_event(debug_code: AXIDebugCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI debug event"""
    return {
        'packet_type': PktType.DEBUG.value,
        'protocol': ProtocolType.AXI.value,
        'event_code': debug_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


# =============================================================================
# APB EVENT FACTORIES
# =============================================================================

def create_apb_error_event(error_code: APBErrorCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected APB error event"""
    return {
        'packet_type': PktType.ERROR.value,
        'protocol': ProtocolType.APB.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_apb_completion_event(completion_code: APBCompletionCode = APBCompletionCode.TRANS_COMPLETE,
                                channel_id: int = 0, unit_id: int = 0, agent_id: int = 0,
                                data: int = 0) -> Dict[str, Any]:
    """Create expected APB completion event"""
    return {
        'packet_type': PktType.COMPLETION.value,
        'protocol': ProtocolType.APB.value,
        'event_code': completion_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_apb_timeout_event(timeout_code: APBTimeoutCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected APB timeout event"""
    return {
        'packet_type': PktType.TIMEOUT.value,
        'protocol': ProtocolType.APB.value,
        'event_code': timeout_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_apb_threshold_event(threshold_code: APBThresholdCode, channel_id: int = 0,
                                unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected APB threshold event"""
    return {
        'packet_type': PktType.THRESHOLD.value,
        'protocol': ProtocolType.APB.value,
        'event_code': threshold_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_apb_performance_event(perf_code: APBPerformanceCode, channel_id: int = 0,
                                unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected APB performance event"""
    return {
        'packet_type': PktType.PERF.value,
        'protocol': ProtocolType.APB.value,
        'event_code': perf_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_apb_debug_event(debug_code: APBDebugCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected APB debug event"""
    return {
        'packet_type': PktType.DEBUG.value,
        'protocol': ProtocolType.APB.value,
        'event_code': debug_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


# =============================================================================
# NOC EVENT FACTORIES
# =============================================================================

def create_noc_error_event(error_code: NOCErrorCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected NOC error event"""
    return {
        'packet_type': PktType.ERROR.value,
        'protocol': ProtocolType.NOC.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


def create_noc_credit_event(credit_code: NOCCreditCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected NOC credit event"""
    return {
        'packet_type': PktType.CREDIT.value,
        'protocol': ProtocolType.NOC.value,
        'event_code': credit_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


# =============================================================================
# ARBITER-SPECIFIC EVENT FACTORIES
# =============================================================================

def create_arbiter_starvation_event(client_id: int, timer_value: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter starvation event for specific client"""
    return create_axi_error_event(
        error_code=AXIErrorCode.ARBITER_STARVATION,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=timer_value
    )


def create_arbiter_grant_latency_event(client_id: int, latency_value: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter grant latency threshold event"""
    return create_axi_threshold_event(
        threshold_code=AXIThresholdCode.GRANT_LATENCY,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=latency_value
    )


def create_arbiter_active_count_event(active_count: int, unit_id: int = 0,
                                        agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter active request count threshold event"""
    return create_axi_threshold_event(
        threshold_code=AXIThresholdCode.ACTIVE_COUNT,
        channel_id=0,  # Not client-specific
        unit_id=unit_id,
        agent_id=agent_id,
        data=active_count
    )


def create_arbiter_grant_efficiency_event(client_id: int, grant_count: int,
                                            active_count: int, unit_id: int = 0,
                                            agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter grant efficiency performance event"""
    # Pack grant_count and active_count into data field
    # Upper 16 bits: grant_count, Lower 12 bits: reserved, Lowest 8 bits: active_count
    packed_data = (grant_count << 16) | (active_count & 0xFF)

    return create_axi_performance_event(
        perf_code=AXIPerformanceCode.GRANT_EFFICIENCY,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=packed_data
    )


def create_arbiter_fairness_event(dominant_client: int, grant_percentage: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter fairness violation event"""
    return create_axi_threshold_event(
        threshold_code=AXIThresholdCode.FAIRNESS,
        channel_id=dominant_client,
        unit_id=unit_id,
        agent_id=agent_id,
        data=grant_percentage
    )


# =============================================================================
# PWM-SPECIFIC EVENT FACTORIES
# =============================================================================

def create_pwm_start_event(channel_id: int = 0, duty_cycle: int = 0,
                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create PWM start debug event"""
    return create_axi_debug_event(
        debug_code=AXIDebugCode.STATE_CHANGE,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=duty_cycle
    )


def create_pwm_complete_event(channel_id: int = 0, cycle_count: int = 0,
                                unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create PWM completion event"""
    return create_axi_completion_event(
        completion_code=AXICompletionCode.TRANS_COMPLETE,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=cycle_count
    )


def create_pwm_block_event(block_state: bool, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create PWM arbiter block event"""
    return create_axi_debug_event(
        debug_code=AXIDebugCode.BLOCK_EVENT,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=1 if block_state else 0
    )


# =============================================================================
# GENERIC EVENT FACTORY
# =============================================================================

def create_generic_event(protocol: ProtocolType, packet_type: PktType,
                        event_code: int, channel_id: int = 0, unit_id: int = 0,
                        agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create a generic event with specified parameters"""
    return {
        'packet_type': packet_type.value,
        'protocol': protocol.value,
        'event_code': event_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data
    }


# =============================================================================
# EVENT SEQUENCE FACTORIES
# =============================================================================

def create_arbiter_test_sequence(num_clients: int, unit_id: int = 0,
                                agent_id: int = 0) -> list:
    """Create a typical arbiter test event sequence"""
    events = []

    # Start with some grant efficiency events for each client
    for client in range(num_clients):
        events.append(create_arbiter_grant_efficiency_event(
            client_id=client,
            grant_count=1,
            active_count=num_clients,
            unit_id=unit_id,
            agent_id=agent_id
        ))

    # Add some threshold events
    events.append(create_arbiter_active_count_event(
        active_count=num_clients,
        unit_id=unit_id,
        agent_id=agent_id
    ))

    return events


def create_pwm_test_sequence(duty_cycle: int, period: int, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0) -> list:
    """Create a typical PWM test event sequence"""
    events = []

    # PWM start
    events.append(create_pwm_start_event(
        channel_id=channel_id,
        duty_cycle=duty_cycle,
        unit_id=unit_id,
        agent_id=agent_id
    ))

    # Block events during PWM high period
    for _ in range(duty_cycle):
        events.append(create_pwm_block_event(
            block_state=True,
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id
        ))

    # Unblock events during PWM low period
    for _ in range(period - duty_cycle):
        events.append(create_pwm_block_event(
            block_state=False,
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id
        ))

    # PWM complete
    events.append(create_pwm_complete_event(
        channel_id=channel_id,
        cycle_count=period,
        unit_id=unit_id,
        agent_id=agent_id
    ))

    return events


# =============================================================================
# LEGACY COMPATIBILITY FUNCTIONS (for backward compatibility)
# =============================================================================

def create_apb_timeout_event_legacy(timeout_code: APBTimeoutCode,
                                    expected_addr: int = None) -> Dict[str, Any]:
    """Legacy APB timeout event creation (for backward compatibility)"""
    return create_apb_timeout_event(
        timeout_code=timeout_code,
        data=expected_addr or 0
    )


def create_apb_performance_event_legacy(perf_code: APBPerformanceCode,
                                        expected_data: int = None) -> Dict[str, Any]:
    """Legacy APB performance event creation (for backward compatibility)"""
    return create_apb_performance_event(
        perf_code=perf_code,
        data=expected_data or 0
    )


def create_apb_debug_event_legacy(debug_code: APBDebugCode,
                                    expected_data: int = None) -> Dict[str, Any]:
    """Legacy APB debug event creation (for backward compatibility)"""
    return create_apb_debug_event(
        debug_code=debug_code,
        data=expected_data or 0
    )
