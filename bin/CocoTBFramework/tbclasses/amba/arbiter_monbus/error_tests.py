# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ErrorDetectionTest
# Purpose: Error Detection Tests for Arbiter MonBus Common
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Error Detection Tests for Arbiter MonBus Common

This module contains tests for error detection including starvation, timeout,
protocol violations, and fairness violations.

Updated to use centralized MonitorConfig and TestResult from monitor_config.py
"""

from typing import Dict, List, Optional, Any

from CocoTBFramework.tbclasses.monbus.monbus_types import ProtocolType, PktType

# ✅ CENTRALIZED IMPORTS - Use synchronized types from monbus_types.py
from CocoTBFramework.tbclasses.monbus.monbus_types import (
    ProtocolType, PktType,
    ARBErrorCode, ARBThresholdCode, ARBTimeoutCode, ARBCompletionCode,
    ARBPerformanceCode, ARBDebugCode
)
from CocoTBFramework.tbclasses.amba.arbiter_monbus.monitor_config import (
    MonitorConfig,
    TestResult,
    ConfigUtils
)


class ErrorDetectionTest:
    """Tests error detection functionality"""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def test_starvation_error_detection(self) -> TestResult:
        """Test starvation error detection"""
        self.log.info(f"=== Testing starvation error detection...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for starvation detection
            config = MonitorConfig.for_starvation_detection()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and create starvation conditions
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "starvation")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze error packets
            error_packets = [p for p in packets if p.pkt_type == PktType.PktTypeError.value]
            starvation_errors = [p for p in error_packets if p.event_code == ARBErrorCode.ARB_ERR_STARVATION]

            details = f"Total: {len(packets)}, Errors: {len(error_packets)}, Starvation: {len(starvation_errors)}"

            success = len(starvation_errors) > 0
            return TestResult(
                passed=success,
                name="starvation_error_detection",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "error_packets": len(error_packets),
                    "starvation_error_packets": len(starvation_errors),
                    "config_used": config.__dict__
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_starvation_error_detection: {str(e)}")
            return TestResult(
                passed=False,
                name="starvation_error_detection",
                details="Exception during starvation error detection test",
                error_msg=str(e)
            )

    async def test_ack_timeout_detection(self) -> TestResult:
        """Test ACK timeout error detection"""
        self.log.info(f"=== Testing ACK timeout detection...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for timeout detection
            config = MonitorConfig.for_timeout_detection()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and create timeout conditions
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(80, "ack_timeout")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=120)

            # Analyze timeout packets
            timeout_packets = [p for p in packets if p.pkt_type == PktType.PktTypeTimeout.value]
            ack_timeouts = [p for p in timeout_packets if p.event_code == ARBTimeoutCode.ARB_TIMEOUT_GRANT_ACK]

            details = f"Total: {len(packets)}, Timeouts: {len(timeout_packets)}, ACK Timeouts: {len(ack_timeouts)}"

            success = len(ack_timeouts) > 0
            return TestResult(
                passed=success,
                name="ack_timeout_detection",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "timeout_packets": len(timeout_packets),
                    "ack_timeout_packets": len(ack_timeouts)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_ack_timeout_detection: {str(e)}")
            return TestResult(
                passed=False,
                name="ack_timeout_detection",
                details="Exception during ACK timeout detection test",
                error_msg=str(e)
            )

    async def test_protocol_violation_detection(self) -> TestResult:
        """Test protocol violation detection"""
        self.log.info(f"=== Testing protocol violation detection...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for protocol monitoring
            config = MonitorConfig.for_protocol_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and create protocol violations
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(80, "protocol_violation")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=120)

            # Analyze error packets for protocol violations
            error_packets = [p for p in packets if p.pkt_type == PktType.PktTypeError.value]
            protocol_errors = [p for p in error_packets if p.event_code == ARBErrorCode.ARB_ERR_PROTOCOL_VIOLATION]

            details = f"Total: {len(packets)}, Errors: {len(error_packets)}, Protocol: {len(protocol_errors)}"

            success = len(protocol_errors) > 0
            return TestResult(
                passed=success,
                name="protocol_violation_detection",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "error_packets": len(error_packets),
                    "protocol_error_packets": len(protocol_errors)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_protocol_violation_detection: {str(e)}")
            return TestResult(
                passed=False,
                name="protocol_violation_detection",
                details="Exception during protocol violation detection test",
                error_msg=str(e)
            )

    async def test_fairness_violation_detection(self) -> TestResult:
        """Test fairness violation detection"""
        self.log.info(f"=== Testing fairness violation detection...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for fairness monitoring
            config = MonitorConfig.for_fairness_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and create fairness violations
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(120, "unfair")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=180)

            # Analyze error packets for fairness violations
            error_packets = [p for p in packets if p.pkt_type == PktType.PktTypeError.value]
            fairness_errors = [p for p in error_packets if p.event_code == ARBErrorCode.ARB_ERR_FAIRNESS_VIOLATION]

            details = f"Total: {len(packets)}, Errors: {len(error_packets)}, Fairness: {len(fairness_errors)}"

            success = len(fairness_errors) > 0
            return TestResult(
                passed=success,
                name="fairness_violation_detection",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "error_packets": len(error_packets),
                    "fairness_error_packets": len(fairness_errors)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_fairness_violation_detection: {str(e)}")
            return TestResult(
                passed=False,
                name="fairness_violation_detection",
                details="Exception during fairness violation detection test",
                error_msg=str(e)
            )

    async def test_multiple_error_types(self) -> TestResult:
        """Test detection of multiple error types simultaneously"""
        self.log.info(f"=== Testing multiple error type detection...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for comprehensive error monitoring
            config = MonitorConfig.for_comprehensive_error_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and create mixed error conditions
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(150, "mixed_errors")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=200)

            # Analyze different error types
            error_packets = [p for p in packets if p.pkt_type == PktType.PktTypeError.value]
            timeout_packets = [p for p in packets if p.pkt_type == PktType.PktTypeTimeout.value]

            # Count specific error types
            starvation_errors = [p for p in error_packets if p.event_code == ARBErrorCode.ARB_ERR_STARVATION]
            protocol_errors = [p for p in error_packets if p.event_code == ARBErrorCode.ARB_ERR_PROTOCOL_VIOLATION]
            fairness_errors = [p for p in error_packets if p.event_code == ARBErrorCode.ARB_ERR_FAIRNESS_VIOLATION]
            ack_timeouts = [p for p in timeout_packets if p.event_code == ARBTimeoutCode.ARB_TIMEOUT_GRANT_ACK]

            error_types_detected = sum([
                len(starvation_errors) > 0,
                len(protocol_errors) > 0,
                len(fairness_errors) > 0,
                len(ack_timeouts) > 0
            ])

            details = f"Total: {len(packets)}, Error types detected: {error_types_detected}/4 (S:{len(starvation_errors)}, P:{len(protocol_errors)}, F:{len(fairness_errors)}, A:{len(ack_timeouts)})"

            success = error_types_detected >= 2  # Should detect at least 2 different error types
            return TestResult(
                passed=success,
                name="multiple_error_types",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "error_packets": len(error_packets),
                    "timeout_packets": len(timeout_packets),
                    "error_types_detected": error_types_detected,
                    "starvation_errors": len(starvation_errors),
                    "protocol_errors": len(protocol_errors),
                    "fairness_errors": len(fairness_errors),
                    "ack_timeouts": len(ack_timeouts)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_multiple_error_types: {str(e)}")
            return TestResult(
                passed=False,
                name="multiple_error_types",
                details="Exception during multiple error types test",
                error_msg=str(e)
            )

    async def test_error_packet_data_integrity(self) -> TestResult:
        """Test error packet data integrity and structure"""
        self.log.info(f"=== Testing error packet data integrity...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for comprehensive error monitoring
            config = MonitorConfig.comprehensive()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate controlled errors
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "controlled_errors")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze packet data integrity
            error_packets = [p for p in packets if p.pkt_type == PktType.PktTypeError.value]
            timeout_packets = [p for p in packets if p.pkt_type == PktType.PktTypeTimeout.value]

            # Validate packet structure
            valid_packets = 0
            total_error_related = len(error_packets) + len(timeout_packets)

            for packet in error_packets + timeout_packets:
                if (hasattr(packet, 'event_code') and
                    hasattr(packet, 'data') and
                    packet.protocol == ProtocolType.PROTOCOL_ARB.value):
                    valid_packets += 1

            data_integrity = (valid_packets / total_error_related) * 100 if total_error_related else 0
            details = f"Total error-related packets: {total_error_related}, Valid: {valid_packets}, Integrity: {data_integrity:.1f}%"

            success = total_error_related > 0 and data_integrity >= 95
            return TestResult(
                passed=success,
                name="error_packet_data_integrity",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "error_packets": len(error_packets),
                    "timeout_packets": len(timeout_packets),
                    "total_error_related": total_error_related,
                    "valid_packets": valid_packets,
                    "data_integrity_percent": data_integrity
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_error_packet_data_integrity: {str(e)}")
            return TestResult(
                passed=False,
                name="error_packet_data_integrity",
                details="Exception during error packet data integrity test",
                error_msg=str(e)
            )
