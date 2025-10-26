# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: monbus_event_factories
# Purpose: MonBus Event Factories - UPDATED for New Monitor Package
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
MonBus Event Factories - UPDATED for New Monitor Package

This module provides factory functions for creating expected MonBus packet events
with proper protocol separation including CORE protocol support. Arbitration events 
now use ARB protocol codes with updated field mappings.

UPDATED FOR NEW MONITOR PACKAGE:
- Protocol field now 3 bits [59:57] supporting 5 protocols
- Event data field now 35 bits [34:0]
- Added comprehensive CORE protocol event factories
- Updated all data field constraints for 35-bit limit
- Corrected all imports to match actual monbus_types.py definitions
"""

from typing import Dict, Any
from .monbus_types import (
    ProtocolType, PktType,
    # AXI Protocol codes (arbitration codes removed)
    AXIErrorCode, AXITimeoutCode,
    # ARB Protocol codes (corrected names)
    ARBErrorCode, ARBTimeoutCode, ARBCompletionCode, ARBThresholdCode,
    ARBPerformanceCode, ARBDebugCode,
    # APB Protocol codes (corrected names)
    APBErrorCode,
    # AXIS Protocol codes
    AXISErrorCode,
    # CORE Protocol codes (NEW)
    COREErrorCode, CORETimeoutCode, CORECompletionCode, COREThresholdCode,
    COREPerformanceCode, COREDebugCode
)


# =============================================================================
# DATA FIELD VALIDATION - UPDATED
# =============================================================================

def validate_data_field(data: int) -> int:
    """Validate and clamp data field to 35-bit maximum"""
    max_35_bit = (1 << 35) - 1  # 0x7FFFFFFFF
    if data > max_35_bit:
        raise ValueError(f"Data field {data:X} exceeds 35-bit maximum {max_35_bit:X}")
    return data & max_35_bit


# =============================================================================
# AXI EVENT FACTORIES (arbitration events removed)
# =============================================================================

def create_axi_error_event(error_code: AXIErrorCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI error event (no longer includes arbitration errors)"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': ProtocolType.PROTOCOL_AXI.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_axi_timeout_event(timeout_code: AXITimeoutCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXI timeout event"""
    return {
        'pkt_type': PktType.TIMEOUT.value,
        'protocol': ProtocolType.PROTOCOL_AXI.value,
        'event_code': timeout_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


# =============================================================================
# ARB EVENT FACTORIES (all arbitration-specific events)
# =============================================================================

def create_arb_error_event(error_code: ARBErrorCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected ARB error event"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_arb_timeout_event(timeout_code: ARBTimeoutCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected ARB timeout event"""
    return {
        'pkt_type': PktType.TIMEOUT.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': timeout_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_arb_completion_event(completion_code: ARBCompletionCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected ARB completion event"""
    return {
        'pkt_type': PktType.COMPLETION.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': completion_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_arb_threshold_event(threshold_code: ARBThresholdCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected ARB threshold event"""
    return {
        'pkt_type': PktType.THRESHOLD.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': threshold_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_arb_performance_event(perf_code: ARBPerformanceCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected ARB performance event"""
    return {
        'pkt_type': PktType.PERF.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': perf_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_arb_debug_event(debug_code: ARBDebugCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected ARB debug event"""
    return {
        'pkt_type': PktType.DEBUG.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': debug_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


# =============================================================================
# CORE EVENT FACTORIES (NEW - comprehensive CORE protocol support)
# =============================================================================

def create_core_error_event(error_code: COREErrorCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected CORE error event - NEW"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': ProtocolType.PROTOCOL_CORE.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_core_timeout_event(timeout_code: CORETimeoutCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected CORE timeout event - NEW"""
    return {
        'pkt_type': PktType.TIMEOUT.value,
        'protocol': ProtocolType.PROTOCOL_CORE.value,
        'event_code': timeout_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_core_completion_event(completion_code: CORECompletionCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected CORE completion event - NEW"""
    return {
        'pkt_type': PktType.COMPLETION.value,
        'protocol': ProtocolType.PROTOCOL_CORE.value,
        'event_code': completion_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_core_threshold_event(threshold_code: COREThresholdCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected CORE threshold event - NEW"""
    return {
        'pkt_type': PktType.THRESHOLD.value,
        'protocol': ProtocolType.PROTOCOL_CORE.value,
        'event_code': threshold_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_core_performance_event(perf_code: COREPerformanceCode, channel_id: int = 0,
                            unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected CORE performance event - NEW"""
    return {
        'pkt_type': PktType.PERF.value,
        'protocol': ProtocolType.PROTOCOL_CORE.value,
        'event_code': perf_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_core_debug_event(debug_code: COREDebugCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected CORE debug event - NEW"""
    return {
        'pkt_type': PktType.DEBUG.value,
        'protocol': ProtocolType.PROTOCOL_CORE.value,
        'event_code': debug_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


# =============================================================================
# ARB-SPECIFIC CONVENIENCE FACTORIES (UPDATED)
# =============================================================================

def create_arbiter_starvation_event(client_id: int, timer_value: int,
                                unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter starvation event for specific client (USES ARB PROTOCOL)"""
    return create_arb_error_event(
        error_code=ARBErrorCode.STARVATION,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=timer_value
    )


def create_arbiter_fairness_violation_event(client_id: int, deviation_value: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter fairness violation event (USES ARB PROTOCOL)"""
    return create_arb_error_event(
        error_code=ARBErrorCode.FAIRNESS_VIOLATION,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=deviation_value
    )


def create_arbiter_request_timeout_event(client_id: int, timeout_value: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter request timeout event (USES ARB PROTOCOL)"""
    return create_arb_timeout_event(
        timeout_code=ARBTimeoutCode.REQUEST_HOLD,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=timeout_value
    )


def create_arbiter_grant_timeout_event(client_id: int, timeout_value: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter grant timeout event (USES ARB PROTOCOL)"""
    return create_arb_timeout_event(
        timeout_code=ARBTimeoutCode.GRANT_ACK,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=timeout_value
    )


def create_arbiter_ack_timeout_event(client_id: int, timeout_value: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter ACK timeout event (USES ARB PROTOCOL)"""
    return create_arb_timeout_event(
        timeout_code=ARBTimeoutCode.GRANT_ACK,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=timeout_value
    )


def create_arbiter_latency_threshold_event(client_id: int, latency_value: int,
                                                unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter latency threshold event (USES ARB PROTOCOL)"""
    return create_arb_threshold_event(
        threshold_code=ARBThresholdCode.REQUEST_LATENCY,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=latency_value
    )


def create_arbiter_queue_depth_threshold_event(queue_depth: int,
                                                unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter queue depth threshold event (USES ARB PROTOCOL)"""
    return create_arb_threshold_event(
        threshold_code=ARBThresholdCode.ACTIVE_REQUESTS,
        channel_id=0,
        unit_id=unit_id,
        agent_id=agent_id,
        data=queue_depth
    )


def create_arbiter_fairness_threshold_event(fairness_metric: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter fairness threshold event (USES ARB PROTOCOL)"""
    return create_arb_threshold_event(
        threshold_code=ARBThresholdCode.FAIRNESS_DEV,
        channel_id=0,
        unit_id=unit_id,
        agent_id=agent_id,
        data=fairness_metric
    )


def create_arbiter_active_requests_threshold_event(active_count: int,
                                                unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter active requests threshold event (USES ARB PROTOCOL)"""
    return create_arb_threshold_event(
        threshold_code=ARBThresholdCode.ACTIVE_REQUESTS,
        channel_id=0,
        unit_id=unit_id,
        agent_id=agent_id,
        data=active_count
    )


def create_arbiter_starvation_time_threshold_event(client_id: int, starvation_time: int,
                                                unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter starvation time threshold event (USES ARB PROTOCOL)"""
    return create_arb_threshold_event(
        threshold_code=ARBThresholdCode.STARVATION_TIME,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=starvation_time
    )


def create_arbiter_throughput_performance_event(throughput_value: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter throughput performance event (USES ARB PROTOCOL)"""
    return create_arb_performance_event(
        perf_code=ARBPerformanceCode.THROUGHPUT,
        channel_id=0,
        unit_id=unit_id,
        agent_id=agent_id,
        data=throughput_value
    )


def create_arbiter_latency_performance_event(latency_value: int, client_id: int = 0,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter latency performance event (USES ARB PROTOCOL)"""
    return create_arb_performance_event(
        perf_code=ARBPerformanceCode.LATENCY_AVG,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=latency_value
    )


def create_arbiter_fairness_performance_event(fairness_value: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter fairness performance event (USES ARB PROTOCOL)"""
    return create_arb_performance_event(
        perf_code=ARBPerformanceCode.FAIRNESS_METRIC,
        channel_id=0,
        unit_id=unit_id,
        agent_id=agent_id,
        data=fairness_value
    )


def create_arbiter_grant_issued_event(client_id: int, grant_id: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter grant issued performance event (USES ARB PROTOCOL)"""
    return create_arb_performance_event(
        perf_code=ARBPerformanceCode.GRANT_ISSUED,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=grant_id
    )


def create_arbiter_ack_received_event(client_id: int, ack_data: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter ACK received performance event (USES ARB PROTOCOL)"""
    return create_arb_performance_event(
        perf_code=ARBPerformanceCode.ACK_RECEIVED,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=ack_data
    )


def create_arbiter_transaction_complete_event(client_id: int, transaction_id: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create arbiter transaction completion event (USES ARB PROTOCOL)"""
    return create_arb_completion_event(
        completion_code=ARBCompletionCode.TRANSACTION,
        channel_id=client_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=transaction_id
    )


# =============================================================================
# CORE-SPECIFIC CONVENIENCE FACTORIES (NEW)
# =============================================================================

def create_core_descriptor_malformed_event(channel_id: int, descriptor_addr: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE descriptor malformed error event - NEW"""
    return create_core_error_event(
        error_code=COREErrorCode.DESCRIPTOR_MALFORMED,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=descriptor_addr
    )


def create_core_descriptor_bad_addr_event(channel_id: int, bad_addr: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE descriptor bad address error event - NEW"""
    return create_core_error_event(
        error_code=COREErrorCode.DESCRIPTOR_BAD_ADDR,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=bad_addr
    )


def create_core_data_bad_addr_event(channel_id: int, bad_addr: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE data bad address error event - NEW"""
    return create_core_error_event(
        error_code=COREErrorCode.DATA_BAD_ADDR,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=bad_addr
    )


def create_core_flag_comparison_error_event(channel_id: int, flag_data: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE flag comparison error event - NEW"""
    return create_core_error_event(
        error_code=COREErrorCode.FLAG_COMPARISON,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=flag_data
    )


def create_core_credit_underflow_event(channel_id: int, credit_level: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE credit underflow error event - NEW"""
    return create_core_error_event(
        error_code=COREErrorCode.CREDIT_UNDERFLOW,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=credit_level
    )


def create_core_state_machine_error_event(channel_id: int, fsm_state: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE state machine error event - NEW"""
    return create_core_error_event(
        error_code=COREErrorCode.STATE_MACHINE,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=fsm_state
    )


def create_core_descriptor_fetch_timeout_event(channel_id: int, timeout_cycles: int,
                                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE descriptor fetch timeout event - NEW"""
    return create_core_timeout_event(
        timeout_code=CORETimeoutCode.DESCRIPTOR_FETCH,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=timeout_cycles
    )


def create_core_flag_retry_timeout_event(channel_id: int, retry_count: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE flag retry timeout event - NEW"""
    return create_core_timeout_event(
        timeout_code=CORETimeoutCode.FLAG_RETRY,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=retry_count
    )


def create_core_descriptor_loaded_completion_event(channel_id: int, descriptor_id: int,
                                                unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE descriptor loaded completion event - NEW"""
    return create_core_completion_event(
        completion_code=CORECompletionCode.DESCRIPTOR_LOADED,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=descriptor_id
    )


def create_core_flag_matched_completion_event(channel_id: int, flag_value: int,
                                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE flag matched completion event - NEW"""
    return create_core_completion_event(
        completion_code=CORECompletionCode.FLAG_MATCHED,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=flag_value
    )


def create_core_data_transfer_completion_event(channel_id: int, transfer_size: int,
                                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE data transfer completion event - NEW"""
    return create_core_completion_event(
        completion_code=CORECompletionCode.DATA_TRANSFER,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=transfer_size
    )


def create_core_credit_low_threshold_event(channel_id: int, credit_level: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE credit low threshold event - NEW"""
    return create_core_threshold_event(
        threshold_code=COREThresholdCode.CREDIT_LOW,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=credit_level
    )


def create_core_latency_threshold_event(channel_id: int, latency_value: int,
                                    unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE latency threshold event - NEW"""
    return create_core_threshold_event(
        threshold_code=COREThresholdCode.LATENCY,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=latency_value
    )


def create_core_throughput_threshold_event(channel_id: int, throughput_value: int,
                                        unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE throughput threshold event - NEW"""
    return create_core_threshold_event(
        threshold_code=COREThresholdCode.THROUGHPUT,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=throughput_value
    )


def create_core_end_of_data_performance_event(channel_id: int, data_count: int,
                                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE end of data performance event - NEW"""
    return create_core_performance_event(
        perf_code=COREPerformanceCode.END_OF_DATA,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=data_count
    )


def create_core_end_of_stream_performance_event(channel_id: int, stream_id: int,
                                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE end of stream performance event - NEW"""
    return create_core_performance_event(
        perf_code=COREPerformanceCode.END_OF_STREAM,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=stream_id
    )


def create_core_fsm_state_change_debug_event(channel_id: int, old_state: int, new_state: int,
                                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE FSM state change debug event - NEW"""
    # Pack old and new state into data field
    state_data = (old_state << 16) | new_state
    return create_core_debug_event(
        debug_code=COREDebugCode.FSM_STATE_CHANGE,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=state_data
    )


def create_core_descriptor_content_debug_event(channel_id: int, descriptor_data: int,
                                            unit_id: int = 0, agent_id: int = 0) -> Dict[str, Any]:
    """Create CORE descriptor content debug event - NEW"""
    return create_core_debug_event(
        debug_code=COREDebugCode.DESCRIPTOR_CONTENT,
        channel_id=channel_id,
        unit_id=unit_id,
        agent_id=agent_id,
        data=descriptor_data
    )


# =============================================================================
# APB EVENT FACTORIES (simplified - only error for now)
# =============================================================================

def create_apb_error_event(error_code: APBErrorCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected APB error event"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': ProtocolType.PROTOCOL_APB.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


# =============================================================================
# AXIS EVENT FACTORIES (simplified - only error for now)
# =============================================================================

def create_axis_error_event(error_code: AXISErrorCode, channel_id: int = 0,
                        unit_id: int = 0, agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create expected AXIS error event"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': ProtocolType.PROTOCOL_AXIS.value,
        'event_code': error_code.value,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


# =============================================================================
# PROTOCOL-SPECIFIC CONVENIENCE FUNCTIONS
# =============================================================================

def create_protocol_error_event(protocol: ProtocolType, error_code: int,
                            channel_id: int = 0, unit_id: int = 0,
                            agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create error event for any protocol with raw error code"""
    return {
        'pkt_type': PktType.ERROR.value,
        'protocol': protocol.value,
        'event_code': error_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_protocol_performance_event(protocol: ProtocolType, perf_code: int,
                                    channel_id: int = 0, unit_id: int = 0,
                                    agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create performance event for any protocol with raw performance code"""
    return {
        'pkt_type': PktType.PERF.value,
        'protocol': protocol.value,
        'event_code': perf_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_protocol_threshold_event(protocol: ProtocolType, threshold_code: int,
                                channel_id: int = 0, unit_id: int = 0,
                                agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create threshold event for any protocol with raw threshold code"""
    return {
        'pkt_type': PktType.THRESHOLD.value,
        'protocol': protocol.value,
        'event_code': threshold_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_protocol_completion_event(protocol: ProtocolType, completion_code: int,
                                channel_id: int = 0, unit_id: int = 0,
                                agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create completion event for any protocol with raw completion code"""
    return {
        'pkt_type': PktType.COMPLETION.value,
        'protocol': protocol.value,
        'event_code': completion_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_protocol_timeout_event(protocol: ProtocolType, timeout_code: int,
                                channel_id: int = 0, unit_id: int = 0,
                                agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create timeout event for any protocol with raw timeout code"""
    return {
        'pkt_type': PktType.TIMEOUT.value,
        'protocol': protocol.value,
        'event_code': timeout_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


def create_protocol_debug_event(protocol: ProtocolType, debug_code: int,
                            channel_id: int = 0, unit_id: int = 0,
                            agent_id: int = 0, data: int = 0) -> Dict[str, Any]:
    """Create debug event for any protocol with raw debug code"""
    return {
        'pkt_type': PktType.DEBUG.value,
        'protocol': protocol.value,
        'event_code': debug_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': validate_data_field(data)
    }


# =============================================================================
# BATCH EVENT CREATORS - UPDATED
# =============================================================================

def create_starvation_event_sequence(client_ids: list, timer_values: list,
                                    unit_id: int = 0, agent_id: int = 0) -> list:
    """Create sequence of starvation events for multiple clients"""
    events = []
    for client_id, timer_value in zip(client_ids, timer_values):
        events.append(create_arbiter_starvation_event(
            client_id=client_id,
            timer_value=timer_value,
            unit_id=unit_id,
            agent_id=agent_id
        ))
    return events


def create_threshold_violation_sequence(threshold_configs: list,
                                    unit_id: int = 0, agent_id: int = 0) -> list:
    """Create sequence of threshold violation events"""
    events = []
    for config in threshold_configs:
        protocol = config.get('protocol', ProtocolType.PROTOCOL_ARB)
        threshold_code = config['threshold_code']
        channel_id = config.get('channel_id', 0)
        data = config.get('data', 0)

        events.append(create_protocol_threshold_event(
            protocol=protocol,
            threshold_code=threshold_code,
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id,
            data=data
        ))
    return events


def create_performance_monitoring_sequence(perf_configs: list,
                                        unit_id: int = 0, agent_id: int = 0) -> list:
    """Create sequence of performance monitoring events"""
    events = []
    for config in perf_configs:
        protocol = config.get('protocol', ProtocolType.PROTOCOL_ARB)
        perf_code = config['perf_code']
        channel_id = config.get('channel_id', 0)
        data = config.get('data', 0)

        events.append(create_protocol_performance_event(
            protocol=protocol,
            perf_code=perf_code,
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id,
            data=data
        ))
    return events


def create_core_error_sequence(channel_ids: list, error_codes: list, error_data: list,
                            unit_id: int = 0, agent_id: int = 0) -> list:
    """Create sequence of CORE error events for multiple channels - NEW"""
    events = []
    for channel_id, error_code, data in zip(channel_ids, error_codes, error_data):
        events.append(create_core_error_event(
            error_code=error_code,
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id,
            data=data
        ))
    return events


def create_core_completion_sequence(channel_ids: list, completion_codes: list, completion_data: list,
                                unit_id: int = 0, agent_id: int = 0) -> list:
    """Create sequence of CORE completion events for multiple channels - NEW"""
    events = []
    for channel_id, completion_code, data in zip(channel_ids, completion_codes, completion_data):
        events.append(create_core_completion_event(
            completion_code=completion_code,
            channel_id=channel_id,
            unit_id=unit_id,
            agent_id=agent_id,
            data=data
        ))
    return events


def create_mixed_protocol_sequence(event_configs: list) -> list:
    """Create sequence of events across multiple protocols"""
    events = []
    for config in event_configs:
        protocol = config['protocol']
        pkt_type = config['pkt_type']
        event_code = config['event_code']
        channel_id = config.get('channel_id', 0)
        unit_id = config.get('unit_id', 0)
        agent_id = config.get('agent_id', 0)
        data = config.get('data', 0)

        if pkt_type == PktType.ERROR:
            events.append(create_protocol_error_event(
                protocol=protocol, error_code=event_code,
                channel_id=channel_id, unit_id=unit_id, agent_id=agent_id, data=data
            ))
        elif pkt_type == PktType.TIMEOUT:
            events.append(create_protocol_timeout_event(
                protocol=protocol, timeout_code=event_code,
                channel_id=channel_id, unit_id=unit_id, agent_id=agent_id, data=data
            ))
        elif pkt_type == PktType.COMPLETION:
            events.append(create_protocol_completion_event(
                protocol=protocol, completion_code=event_code,
                channel_id=channel_id, unit_id=unit_id, agent_id=agent_id, data=data
            ))
        elif pkt_type == PktType.THRESHOLD:
            events.append(create_protocol_threshold_event(
                protocol=protocol, threshold_code=event_code,
                channel_id=channel_id, unit_id=unit_id, agent_id=agent_id, data=data
            ))
        elif pkt_type == PktType.PERF:
            events.append(create_protocol_performance_event(
                protocol=protocol, perf_code=event_code,
                channel_id=channel_id, unit_id=unit_id, agent_id=agent_id, data=data
            ))
        elif pkt_type == PktType.DEBUG:
            events.append(create_protocol_debug_event(
                protocol=protocol, debug_code=event_code,
                channel_id=channel_id, unit_id=unit_id, agent_id=agent_id, data=data
            ))

    return events


# =============================================================================
# VALIDATION HELPERS - UPDATED
# =============================================================================

def validate_event_dict(event_dict: Dict[str, Any]) -> bool:
    """Validate that an event dictionary has all required fields"""
    required_fields = ['pkt_type', 'protocol', 'event_code',
                    'channel_id', 'unit_id', 'agent_id', 'data']

    for field in required_fields:
        if field not in event_dict:
            return False

    # Basic range validation - UPDATED
    if not (0 <= event_dict['pkt_type'] <= 0xF):
        return False
    if not (0 <= event_dict['protocol'] <= 0x7):  # ✅ CORRECTED: 3 bits = 0-7 range
        return False
    if not (0 <= event_dict['event_code'] <= 0xF):
        return False
    if not (0 <= event_dict['channel_id'] <= 0x3F):
        return False
    if not (0 <= event_dict['unit_id'] <= 0xF):
        return False
    if not (0 <= event_dict['agent_id'] <= 0xFF):
        return False
    if not (0 <= event_dict['data'] <= 0x7FFFFFFFF):  # ✅ CORRECTED: 35-bit max
        return False

    return True


def get_event_description(event_dict: Dict[str, Any]) -> str:
    """Get human-readable description of an event"""
    try:
        protocol = ProtocolType(event_dict['protocol'])
        packet_type = PktType(event_dict['pkt_type'])

        desc = f"{protocol.name}_{packet_type.name}"
        desc += f" code=0x{event_dict['event_code']:X}"
        desc += f" ch=0x{event_dict['channel_id']:02X}"
        desc += f" unit=0x{event_dict['unit_id']:X}"
        desc += f" agent=0x{event_dict['agent_id']:02X}"
        desc += f" data=0x{event_dict['data']:09X}"

        return desc
    except (ValueError, KeyError):
        return f"INVALID_EVENT: {event_dict}"


def get_protocol_event_count_by_type(events: list) -> Dict[str, Dict[str, int]]:
    """Get event count breakdown by protocol and packet type"""
    counts = {}
    
    for event in events:
        try:
            protocol = ProtocolType(event['protocol']).name
            pkt_type = PktType(event['pkt_type']).name
            
            if protocol not in counts:
                counts[protocol] = {}
            if pkt_type not in counts[protocol]:
                counts[protocol][pkt_type] = 0
                
            counts[protocol][pkt_type] += 1
        except (ValueError, KeyError):
            continue
            
    return counts


def create_test_event_suite() -> Dict[str, list]:
    """Create comprehensive test suite with events from all protocols - NEW"""
    suite = {
        'arb_events': [
            create_arbiter_starvation_event(0, 1000),
            create_arbiter_fairness_violation_event(1, 25),
            create_arbiter_latency_threshold_event(2, 500),
            create_arbiter_transaction_complete_event(0, 123),
            create_arbiter_throughput_performance_event(85),
        ],
        'core_events': [
            create_core_descriptor_malformed_event(0, 0x12345678),
            create_core_credit_underflow_event(1, 5),
            create_core_descriptor_fetch_timeout_event(2, 200),
            create_core_descriptor_loaded_completion_event(0, 0xABC),
            create_core_end_of_data_performance_event(1, 1024),
            create_core_fsm_state_change_debug_event(0, 2, 3),
        ],
        'axi_events': [
            create_axi_error_event(AXIErrorCode.RESP_SLVERR, 5, data=0x1000),
            create_axi_timeout_event(AXITimeoutCode.CMD, 3, data=100),
        ],
        'apb_events': [
            create_apb_error_event(APBErrorCode.PSLVERR, 1, data=0x8000),
        ],
        'axis_events': [
            create_axis_error_event(AXISErrorCode.AXIS_ERR_PROTOCOL, 7, data=0xFF00),
        ]
    }
    
    return suite


# =============================================================================
# USAGE EXAMPLES AND DOCUMENTATION
# =============================================================================

def demonstrate_usage():
    """Demonstrate usage of the event factories - NEW"""
    print("=== MonBus Event Factory Usage Examples ===\n")
    
    # ARB Events
    print("ARB Protocol Events:")
    arb_starvation = create_arbiter_starvation_event(client_id=2, timer_value=1500)
    print(f"  Starvation: {get_event_description(arb_starvation)}")
    
    arb_fairness = create_arbiter_fairness_violation_event(client_id=1, deviation_value=30)
    print(f"  Fairness: {get_event_description(arb_fairness)}")
    
    # CORE Events
    print("\nCORE Protocol Events:")
    core_desc = create_core_descriptor_malformed_event(channel_id=0, descriptor_addr=0x1000)
    print(f"  Descriptor Error: {get_event_description(core_desc)}")
    
    core_credit = create_core_credit_underflow_event(channel_id=1, credit_level=2)
    print(f"  Credit Error: {get_event_description(core_credit)}")
    
    core_completion = create_core_data_transfer_completion_event(channel_id=2, transfer_size=512)
    print(f"  Completion: {get_event_description(core_completion)}")
    
    # Mixed Protocol Sequence
    print("\nMixed Protocol Sequence:")
    mixed_events = create_mixed_protocol_sequence([
        {
            'protocol': ProtocolType.PROTOCOL_ARB,
            'pkt_type': PktType.ERROR,
            'event_code': ARBErrorCode.STARVATION.value,
            'channel_id': 0,
            'data': 2000
        },
        {
            'protocol': ProtocolType.PROTOCOL_CORE,
            'pkt_type': PktType.COMPLETION,
            'event_code': CORECompletionCode.DESCRIPTOR_LOADED.value,
            'channel_id': 1,
            'data': 0x555
        }
    ])
    
    for i, event in enumerate(mixed_events):
        print(f"  Event {i+1}: {get_event_description(event)}")
    
    # Validation
    print(f"\nValidation Results:")
    for i, event in enumerate([arb_starvation, core_desc, core_completion]):
        is_valid = validate_event_dict(event)
        print(f"  Event {i+1} valid: {is_valid}")


if __name__ == "__main__":
    demonstrate_usage()