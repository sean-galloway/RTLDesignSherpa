#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestDefinition
# Purpose: Test Framework for Arbiter MonBus Testing - UPDATED FOR 3-BIT PROTOCOL
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test Framework for Arbiter MonBus Testing - UPDATED FOR 3-BIT PROTOCOL

This module provides the core test infrastructure for arbiter monitor testing,
specifically designed to integrate with the existing arbiter_monbus_common_tb.py.

This is a MINIMAL, CLEAN version that integrates with your existing testbench
without breaking any existing functionality.

File Location: CocoTBFramework/tbclasses/amba/arbiter_monbus/test_framework.py

Key Features:
- TestConfiguration class for automatic DUT parameter detection  
- TestFramework class that works with existing test classes
- Clean integration with existing arbiter_monbus_common_tb.py
- Updated for new 3-bit protocol and 35-bit data fields
"""

from dataclasses import dataclass
from typing import Dict, List, Tuple, Callable, Optional, Any

# Import the updated monbus types
from CocoTBFramework.tbclasses.monbus.monbus_types import ProtocolType, PktType


@dataclass
class TestDefinition:
    """Test definition with compatibility requirements"""
    name: str
    method_ref: Callable
    requires_ack: bool = False
    requires_weighted: bool = False
    min_clients: int = 1
    test_levels: List[str] = None

    def __post_init__(self):
        if self.test_levels is None:
            self.test_levels = ["basic", "medium", "full"]

    def is_compatible(self, config: 'TestConfiguration', test_level: str) -> Tuple[bool, str]:
        """Check if test is compatible with given configuration and test level"""
        
        # Check test level compatibility
        if test_level not in self.test_levels:
            return False, f"Not available for '{test_level}' level"
        
        # Check ACK requirement
        if self.requires_ack and not config.supports_ack:
            return False, "Requires ACK mode (WAIT_GNT_ACK=1)"
        
        # Check weighted arbiter requirement
        if self.requires_weighted and not config.supports_weighted_fairness:
            return False, "Requires weighted mode (WEIGHTED_MODE=1)"
        
        # Check minimum client requirement
        if config.clients < self.min_clients:
            return False, f"Requires at least {self.min_clients} clients (has {config.clients})"
        
        return True, ""


class TestConfiguration:
    """DUT configuration auto-detection - UPDATED"""
    
    def __init__(self, dut):
        self.clients = int(dut.CLIENTS.value)
        self.wait_gnt_ack = int(dut.WAIT_GNT_ACK.value)
        self.weighted_mode = int(dut.WEIGHTED_MODE.value)
        self.fifo_depth = int(dut.MON_FIFO_DEPTH.value)
        self.agent_id = int(dut.MON_AGENT_ID.value)
        self.unit_id = int(dut.MON_UNIT_ID.value)

        # Derived capabilities
        self.supports_ack = (self.wait_gnt_ack == 1)
        self.supports_weighted_fairness = (self.weighted_mode == 1)
        
        # Calculated parameters
        self.n = max(1, (self.clients - 1).bit_length())  # $clog2(CLIENTS)
        self.client_mask = (1 << self.clients) - 1

    def __str__(self):
        return (f"TestConfig(clients={self.clients}, ack={self.supports_ack}, "
                f"weighted={self.supports_weighted_fairness}, fifo={self.fifo_depth}, "
                f"agent=0x{self.agent_id:02X}, unit=0x{self.unit_id:X})")


class TestFramework:
    """
    Centralized test framework that integrates with existing testbench structure
    
    This framework works WITH your existing test classes, not INSTEAD of them.
    """

    def __init__(self, testbench):
        self.tb = testbench
        self.config = TestConfiguration(testbench.dut)
        self.tests = self._register_tests()

    def _register_tests(self) -> Dict[str, TestDefinition]:
        """Register all tests with their requirements - MATCHES EXISTING TESTS"""
        return {
            # Basic functionality tests
            'monitor_enable_disable': TestDefinition(
                name='monitor_enable_disable',
                method_ref=lambda: self.tb.basic_test.test_monitor_enable_disable(),
                test_levels=['basic', 'medium', 'full']
            ),
            'packet_generation': TestDefinition(
                name='packet_generation',
                method_ref=lambda: self.tb.basic_test.test_packet_generation(),
                test_levels=['basic', 'medium', 'full']
            ),
            'packet_filtering': TestDefinition(
                name='packet_filtering',
                method_ref=lambda: self.tb.basic_test.test_packet_type_filtering(),
                test_levels=['basic', 'medium', 'full']
            ),
            'protocol_filtering': TestDefinition(
                name='protocol_filtering',
                method_ref=lambda: self.tb.basic_test.test_protocol_filtering(),
                test_levels=['medium', 'full']
            ),

            # Threshold monitoring tests
            'latency_thresholds': TestDefinition(
                name='latency_thresholds',
                method_ref=lambda: self.tb.threshold_test.test_latency_thresholds(),
                test_levels=['basic', 'medium', 'full']
            ),
            'starvation_thresholds': TestDefinition(
                name='starvation_thresholds',
                method_ref=lambda: self.tb.threshold_test.test_starvation_thresholds(),
                test_levels=['basic', 'medium', 'full']
            ),
            'fairness_thresholds': TestDefinition(
                name='fairness_thresholds',
                method_ref=lambda: self.tb.threshold_test.test_fairness_thresholds(),
                requires_weighted=True,
                min_clients=3,
                test_levels=['medium', 'full']
            ),
            'active_thresholds': TestDefinition(
                name='active_thresholds',
                method_ref=lambda: self.tb.threshold_test.test_active_request_thresholds(),
                min_clients=2,
                test_levels=['basic', 'medium', 'full']
            ),
            'efficiency_thresholds': TestDefinition(
                name='efficiency_thresholds',
                method_ref=lambda: self.tb.threshold_test.test_efficiency_thresholds(),
                test_levels=['medium', 'full']
            ),
            'threshold_data': TestDefinition(
                name='threshold_data',
                method_ref=lambda: self.tb.threshold_test.test_threshold_packet_data(),
                test_levels=['full']
            ),

            # Error detection tests
            'starvation_errors': TestDefinition(
                name='starvation_errors',
                method_ref=lambda: self.tb.error_test.test_starvation_error_detection(),
                test_levels=['basic', 'medium', 'full']
            ),
            'ack_timeout': TestDefinition(
                name='ack_timeout',
                method_ref=lambda: self.tb.error_test.test_ack_timeout_detection(),
                requires_ack=True,
                test_levels=['basic', 'medium', 'full']
            ),
            'protocol_violations': TestDefinition(
                name='protocol_violations',
                method_ref=lambda: self.tb.error_test.test_protocol_violation_detection(),
                test_levels=['medium', 'full']
            ),
            'fairness_violations': TestDefinition(
                name='fairness_violations',
                method_ref=lambda: self.tb.error_test.test_fairness_violation_detection(),
                requires_weighted=True,
                min_clients=3,
                test_levels=['medium', 'full']
            ),
            'multiple_errors': TestDefinition(
                name='multiple_errors',
                method_ref=lambda: self.tb.error_test.test_multiple_error_types(),
                test_levels=['full']
            ),

            # Performance monitoring tests
            'performance_events': TestDefinition(
                name='performance_events',
                method_ref=lambda: self.tb.performance_test.test_performance_event_generation(),
                test_levels=['basic', 'medium', 'full']
            ),
            'grant_tracking': TestDefinition(
                name='grant_tracking',
                method_ref=lambda: self.tb.performance_test.test_grant_tracking(),
                test_levels=['basic', 'medium', 'full']
            ),
            'ack_tracking': TestDefinition(
                name='ack_tracking',
                method_ref=lambda: self.tb.performance_test.test_ack_tracking(),
                requires_ack=True,
                test_levels=['medium', 'full']
            ),

            # Corner case tests
            'fifo_exactly_full': TestDefinition(
                name='fifo_exactly_full',
                method_ref=lambda: self.tb.fifo_corner_test.test_fifo_exactly_full(),
                test_levels=['medium', 'full']
            ),
            'fifo_rapid_cycles': TestDefinition(
                name='fifo_rapid_cycles',
                method_ref=lambda: self.tb.fifo_corner_test.test_fifo_rapid_fill_drain(),
                test_levels=['full']
            ),
            'reset_during_op': TestDefinition(
                name='reset_during_op',
                method_ref=lambda: self.tb.reset_behavior_test.test_reset_during_operation(),
                test_levels=['medium', 'full']
            ),
            'minimal_thresholds': TestDefinition(
                name='minimal_thresholds',
                method_ref=lambda: self.tb.config_edge_test.test_minimal_threshold_values(),
                test_levels=['full']
            ),

            # Stress tests
            'fifo_stress': TestDefinition(
                name='fifo_stress',
                method_ref=lambda: self.tb.stress_test.test_fifo_overflow_handling(),
                test_levels=['full']
            ),
            'config_stability': TestDefinition(
                name='config_stability',
                method_ref=lambda: self.tb.stress_test.test_configuration_stability(),
                test_levels=['full']
            ),
            'extended_operation': TestDefinition(
                name='extended_operation',
                method_ref=lambda: self.tb.stress_test.test_extended_operation(),
                test_levels=['full']
            ),
        }

    def get_compatible_tests(self, test_level: str) -> Tuple[List[str], List[Tuple[str, str]]]:
        """
        Get tests compatible with current configuration and test level
        
        Returns:
            Tuple of (compatible_test_names, [(skipped_test_name, reason), ...])
        """
        compatible = []
        skipped = []
        
        for test_name, test_def in self.tests.items():
            is_compatible, reason = test_def.is_compatible(self.config, test_level)
            
            if is_compatible:
                compatible.append(test_name)
            else:
                skipped.append((test_name, reason))
        
        return compatible, skipped

    def get_test_method(self, test_name: str) -> Optional[Callable]:
        """Get the test method for a given test name"""
        if test_name in self.tests:
            return self.tests[test_name].method_ref
        return None

    def get_test_info(self, test_name: str) -> Optional[TestDefinition]:
        """Get full test definition for a test name"""
        return self.tests.get(test_name)

    def generate_test_summary(self, test_level: str) -> str:
        """Generate a summary of available tests for the given level"""
        compatible, skipped = self.get_compatible_tests(test_level)
        
        lines = [
            f"=== Test Summary for Level '{test_level}' ===",
            f"Configuration: {self.config}",
            f"Compatible Tests: {len(compatible)}",
            f"Skipped Tests: {len(skipped)}",
            "",
            "Available Tests:"
        ]
        
        # Group tests by category
        categories = {
            'Basic': [t for t in compatible if t.startswith(('monitor_', 'packet_'))],
            'Thresholds': [t for t in compatible if 'threshold' in t],
            'Errors': [t for t in compatible if t.endswith('_errors') or 'violation' in t or 'timeout' in t],
            'Performance': [t for t in compatible if 'performance' in t or 'tracking' in t],
            'Corner Cases': [t for t in compatible if 'fifo' in t or 'reset' in t or 'minimal' in t],
            'Stress': [t for t in compatible if 'stress' in t or 'extended' in t or 'config' in t]
        }
        
        for category, tests in categories.items():
            if tests:
                lines.append(f"  {category}: {', '.join(tests)}")
        
        if skipped:
            lines.extend([
                "",
                "Skipped Tests:"
            ])
            for test_name, reason in skipped:
                lines.append(f"  {test_name}: {reason}")
        
        return "\n".join(lines)


# =============================================================================
# HELPER FUNCTIONS FOR MONBUS TESTING - UPDATED FOR NEW FORMAT
# =============================================================================

def create_expected_arb_packet(packet_type: PktType, event_code: int, channel_id: int = 0,
                             unit_id: int = 0, agent_id: int = 0x10, data: int = 0) -> Dict[str, Any]:
    """Create expected ARB protocol packet - UPDATED for new format"""
    return {
        'pkt_type': packet_type.value,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'event_code': event_code,
        'channel_id': channel_id,
        'unit_id': unit_id,
        'agent_id': agent_id,
        'data': data & 0x7FFFFFFFF  # ✅ UPDATED: Clamp to 35 bits
    }


def validate_packet_format(packet_dict: Dict[str, Any]) -> List[str]:
    """Validate packet fields are within updated format ranges"""
    errors = []
    
    # Field range validations - UPDATED
    if packet_dict.get('pkt_type', 0) > 15:  # 4 bits
        errors.append(f"pkt_type {packet_dict['pkt_type']} exceeds 4-bit range")
    
    if packet_dict.get('protocol', 0) > 7:  # 3 bits ✅ UPDATED
        errors.append(f"protocol {packet_dict['protocol']} exceeds 3-bit range")
    
    if packet_dict.get('event_code', 0) > 15:  # 4 bits
        errors.append(f"event_code {packet_dict['event_code']} exceeds 4-bit range")
    
    if packet_dict.get('channel_id', 0) > 63:  # 6 bits
        errors.append(f"channel_id {packet_dict['channel_id']} exceeds 6-bit range")
    
    if packet_dict.get('unit_id', 0) > 15:  # 4 bits
        errors.append(f"unit_id {packet_dict['unit_id']} exceeds 4-bit range")
    
    if packet_dict.get('agent_id', 0) > 255:  # 8 bits
        errors.append(f"agent_id {packet_dict['agent_id']} exceeds 8-bit range")
    
    if packet_dict.get('data', 0) > 0x7FFFFFFFF:  # 35 bits ✅ UPDATED
        errors.append(f"data 0x{packet_dict['data']:X} exceeds 35-bit range")
    
    return errors


def get_test_level_description(test_level: str) -> str:
    """Get description of what each test level includes"""
    descriptions = {
        'basic': "Essential functionality tests - monitor enable/disable, basic packet generation, core error detection",
        'medium': "Comprehensive testing - all basic tests plus threshold monitoring, protocol validation, corner cases",
        'full': "Complete test suite - all tests including stress testing, edge cases, extended operation"
    }
    return descriptions.get(test_level, f"Unknown test level: {test_level}")


def verify_expected_packet(received_packet: Dict[str, Any], expected_packet: Dict[str, Any], tolerance: Dict[str, Any] = None) -> bool:
    """Verify that a received packet matches expected values with optional tolerance"""
    if tolerance is None:
        tolerance = {}

    # Check each field
    for field, expected_value in expected_packet.items():
        if field not in received_packet:
            return False

        received_value = received_packet[field]
        field_tolerance = tolerance.get(field, 0)

        if field_tolerance == 0:
            # Exact match required
            if received_value != expected_value:
                return False
        else:
            # Tolerance allowed
            if abs(received_value - expected_value) > field_tolerance:
                return False

    return True


def create_arb_test_config(clients: int = 4, wait_gnt_ack: int = 0, agent_id: int = 0x10, unit_id: int = 0) -> Dict[str, Any]:
    """Create a test configuration dictionary for ARB protocol testing"""
    return {
        'clients': clients,
        'wait_gnt_ack': wait_gnt_ack,
        'weighted_mode': 0,  # Default to simple round-robin
        'agent_id': agent_id,
        'unit_id': unit_id,
        'protocol': ProtocolType.PROTOCOL_ARB.value,
        'fifo_depth': 16,  # Default FIFO depth
        'n_bits': max(1, (clients - 1).bit_length()),  # $clog2(clients)
        'client_mask': (1 << clients) - 1,
    }


# =============================================================================
# INTEGRATION UTILITIES
# =============================================================================

class TestIntegration:
    """Utilities for integrating with existing testbench structure"""
    
    @staticmethod
    def verify_testbench_structure(testbench) -> List[str]:
        """Verify that testbench has all required test class instances"""
        required_attributes = [
            'basic_test', 'threshold_test', 'error_test', 'performance_test',
            'fifo_corner_test', 'reset_behavior_test', 'config_edge_test', 'stress_test'
        ]
        
        missing = []
        for attr in required_attributes:
            if not hasattr(testbench, attr) or getattr(testbench, attr) is None:
                missing.append(attr)
        
        return missing

    @staticmethod
    def get_framework_status(testbench) -> Dict[str, Any]:
        """Get status of test framework integration"""
        missing_attrs = TestIntegration.verify_testbench_structure(testbench)
        
        return {
            'testbench_ready': len(missing_attrs) == 0,
            'missing_attributes': missing_attrs,
            'has_framework': hasattr(testbench, 'test_framework') and testbench.test_framework is not None,
            'config_detected': hasattr(testbench, 'config') or hasattr(testbench, 'test_framework'),
            'dut_parameters': {
                'clients': getattr(testbench.dut, 'CLIENTS', 'N/A'),
                'wait_gnt_ack': getattr(testbench.dut, 'WAIT_GNT_ACK', 'N/A'),
                'weighted_mode': getattr(testbench.dut, 'WEIGHTED_MODE', 'N/A'),
                'fifo_depth': getattr(testbench.dut, 'MON_FIFO_DEPTH', 'N/A'),
            }
        }


# =============================================================================
# COMPATIBILITY LAYER
# =============================================================================

# Provide backwards compatibility aliases
TestConfig = TestConfiguration  # Alias for existing code

# Export key classes and functions
__all__ = [
    'TestDefinition', 'TestConfiguration', 'TestFramework',
    'create_expected_arb_packet', 'validate_packet_format',
    'get_test_level_description', 'TestIntegration',
    'verify_expected_packet', 'create_arb_test_config',
    'TestConfig'  # Backwards compatibility
]