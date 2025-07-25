"""
MonBus Package - Monitor Bus Components for SystemVerilog Testbenches

This package provides comprehensive Python support for MonBus (Monitor Bus)
packet handling and validation in CocoTB testbenches.

The package is organized into logical modules:
- monbus_types: Protocol and packet type enumerations
- monbus_packet: MonbusPacket class and field configuration
- monbus_slave: Enhanced MonbusSlave class for packet monitoring
- monbus_event_factories: Factory functions for creating expected events
- monbus_validators: Validation and analysis helper functions

Usage:
    from monbus import (
        MonbusPacket, MonbusSlave, ProtocolType, PktType,
        create_axi_error_event, validate_packet_fields
    )
"""

# Import all major classes and functions for convenient access
from .monbus_types import (
    # Core enums
    ProtocolType, PktType, MonbusProtocol, MonbusPktType,

    # AXI event codes
    AXIErrorCode, AXITimeoutCode, AXICompletionCode, AXIThresholdCode,
    AXIPerformanceCode, AXIAddrMatchCode, AXIDebugCode,

    # APB event codes
    APBErrorCode, APBTimeoutCode, APBCompletionCode, APBThresholdCode,
    APBPerformanceCode, APBDebugCode,

    # NOC event codes
    NOCErrorCode, NOCCreditCode,

    # State and utility types
    TransState,

    # Helper functions
    get_event_code_enum, get_event_code_name, is_valid_event_code
)

from .monbus_packet import (
    MonbusPacket, create_monbus_field_config
)

from .monbus_slave import (
    MonbusSlave
)

from .monbus_event_factories import (
    # AXI event factories
    create_axi_error_event, create_axi_completion_event, create_axi_timeout_event,
    create_axi_threshold_event, create_axi_performance_event, create_axi_addr_match_event,
    create_axi_debug_event,

    # APB event factories
    create_apb_error_event, create_apb_completion_event, create_apb_timeout_event,
    create_apb_threshold_event, create_apb_performance_event, create_apb_debug_event,

    # NOC event factories
    create_noc_error_event, create_noc_credit_event,

    # Arbiter-specific factories
    create_arbiter_starvation_event, create_arbiter_grant_latency_event,
    create_arbiter_active_count_event, create_arbiter_grant_efficiency_event,
    create_arbiter_fairness_event,

    # PWM-specific factories
    create_pwm_start_event, create_pwm_complete_event, create_pwm_block_event,

    # Generic and sequence factories
    create_generic_event, create_arbiter_test_sequence, create_pwm_test_sequence,

    # Legacy compatibility
    create_apb_timeout_event_legacy, create_apb_performance_event_legacy,
    create_apb_debug_event_legacy
)

from .monbus_validators import (
    # Validation functions
    validate_packet_fields, validate_packet_range, validate_packet_enum_fields,
    validate_packet_consistency, validate_packet_sequence, validate_state_machine_sequence,

    # Matcher functions
    create_packet_matcher, create_range_matcher, create_temporal_matcher,

    # Search and filter functions
    find_packets, find_packets_by_criteria, find_error_packets,
    find_packets_in_time_range, find_sequential_packets,

    # Analysis functions
    analyze_packet_distribution, analyze_timing_patterns, analyze_error_patterns,
    analyze_fairness, measure_latency_metrics, measure_throughput_metrics
)


# Package metadata
__version__ = "1.0.0"
__author__ = "MonBus Development Team"
__description__ = "Monitor Bus components for SystemVerilog testbenches"


# Convenience aliases for backward compatibility
def create_expected_apb_completion_event(**kwargs):
    """Legacy alias for create_apb_completion_event"""
    return create_apb_completion_event(**kwargs)

def create_expected_apb_error_event(**kwargs):
    """Legacy alias for create_apb_error_event"""
    return create_apb_error_event(**kwargs)


# Package-level utility functions
def get_supported_protocols():
    """Get list of supported protocol types"""
    return [protocol.name for protocol in ProtocolType]

def get_supported_packet_types():
    """Get list of supported packet types"""
    return [pkt_type.name for pkt_type in PktType]

def get_protocol_event_codes(protocol: ProtocolType, packet_type: PktType):
    """Get available event codes for a protocol/packet_type combination"""
    enum_class = get_event_code_enum(protocol, packet_type)
    if enum_class:
        return [code.name for code in enum_class]
    return []


# Example usage function
def example_usage():
    """Example showing how to use the MonBus package"""
    print("MonBus Package Example Usage:")
    print("=" * 40)

    # Create events using enum constants
    axi_error = create_axi_error_event(
        error_code=AXIErrorCode.ARBITER_STARVATION,
        channel_id=2,
        unit_id=0x5,
        agent_id=0x12,
        data=0x100
    )
    print(f"AXI Error Event: {axi_error}")

    apb_completion = create_apb_completion_event(
        completion_code=APBCompletionCode.READ_COMPLETE,
        unit_id=0x5,
        agent_id=0x12,
        data=0x2000
    )
    print(f"APB Completion Event: {apb_completion}")

    # Create a packet for validation
    packet = MonbusPacket(**axi_error)
    print(f"Created packet: {packet}")

    # Validate packet
    errors = validate_packet_consistency(packet)
    print(f"Validation errors: {errors}")

    # Show supported protocols and packet types
    print(f"Supported protocols: {get_supported_protocols()}")
    print(f"Supported packet types: {get_supported_packet_types()}")

    # Show event codes for AXI errors
    axi_error_codes = get_protocol_event_codes(ProtocolType.AXI, PktType.ERROR)
    print(f"AXI Error codes: {axi_error_codes}")


# Module-level constants for common configurations
DEFAULT_MONBUS_CONFIG = {
    'expected_unit_id': 0x0,
    'expected_agent_id': 0x00,
    'expected_protocol': ProtocolType.AXI,
    'timeout_cycles': 1000,
    'super_debug': False
}

ARBITER_MONBUS_CONFIG = {
    'expected_unit_id': 0x0,
    'expected_agent_id': 0x00,
    'expected_protocol': ProtocolType.AXI,
    'timeout_cycles': 2000,
    'super_debug': True
}

PWM_MONBUS_CONFIG = {
    'expected_unit_id': 0x0,
    'expected_agent_id': 0x00,
    'expected_protocol': ProtocolType.AXI,
    'timeout_cycles': 5000,
    'super_debug': False
}


# Export all important symbols
__all__ = [
    # Core classes
    'MonbusPacket', 'MonbusSlave',

    # Type enums
    'ProtocolType', 'PktType', 'MonbusProtocol', 'MonbusPktType',

    # AXI event codes
    'AXIErrorCode', 'AXITimeoutCode', 'AXICompletionCode', 'AXIThresholdCode',
    'AXIPerformanceCode', 'AXIAddrMatchCode', 'AXIDebugCode',

    # APB event codes
    'APBErrorCode', 'APBTimeoutCode', 'APBCompletionCode', 'APBThresholdCode',
    'APBPerformanceCode', 'APBDebugCode',

    # NOC event codes
    'NOCErrorCode', 'NOCCreditCode',

    # State types
    'TransState',

    # Event factory functions
    'create_axi_error_event', 'create_axi_completion_event', 'create_axi_timeout_event',
    'create_axi_threshold_event', 'create_axi_performance_event', 'create_axi_addr_match_event',
    'create_axi_debug_event', 'create_apb_error_event', 'create_apb_completion_event',
    'create_apb_timeout_event', 'create_apb_threshold_event', 'create_apb_performance_event',
    'create_apb_debug_event', 'create_noc_error_event', 'create_noc_credit_event',

    # Arbiter-specific factories
    'create_arbiter_starvation_event', 'create_arbiter_grant_latency_event',
    'create_arbiter_active_count_event', 'create_arbiter_grant_efficiency_event',
    'create_arbiter_fairness_event',

    # PWM-specific factories
    'create_pwm_start_event', 'create_pwm_complete_event', 'create_pwm_block_event',

    # Generic factories
    'create_generic_event', 'create_arbiter_test_sequence', 'create_pwm_test_sequence',

    # Validation functions
    'validate_packet_fields', 'validate_packet_range', 'validate_packet_enum_fields',
    'validate_packet_consistency', 'validate_packet_sequence',

    # Matcher functions
    'create_packet_matcher', 'create_range_matcher', 'create_temporal_matcher',

    # Search functions
    'find_packets', 'find_packets_by_criteria', 'find_error_packets',
    'find_packets_in_time_range', 'find_sequential_packets',

    # Analysis functions
    'analyze_packet_distribution', 'analyze_timing_patterns', 'analyze_error_patterns',
    'analyze_fairness', 'measure_latency_metrics', 'measure_throughput_metrics',

    # Utility functions
    'get_event_code_enum', 'get_event_code_name', 'is_valid_event_code',
    'create_monbus_field_config',

    # Package utilities
    'get_supported_protocols', 'get_supported_packet_types', 'get_protocol_event_codes',
    'example_usage',

    # Configuration constants
    'DEFAULT_MONBUS_CONFIG', 'ARBITER_MONBUS_CONFIG', 'PWM_MONBUS_CONFIG',

    # Legacy compatibility
    'create_expected_apb_completion_event', 'create_expected_apb_error_event',
    'create_apb_timeout_event_legacy', 'create_apb_performance_event_legacy',
    'create_apb_debug_event_legacy'
]


if __name__ == "__main__":
    example_usage()
