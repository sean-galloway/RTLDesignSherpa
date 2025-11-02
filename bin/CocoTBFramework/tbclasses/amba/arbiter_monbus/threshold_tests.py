# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ThresholdMonitoringTest
# Purpose: Threshold Monitoring Tests for Arbiter MonBus Common
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Threshold Monitoring Tests for Arbiter MonBus Common

This module contains tests for threshold monitoring including latency, starvation,
fairness, active request, and efficiency thresholds.

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


class ThresholdMonitoringTest:
    """Tests threshold monitoring functionality"""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def test_latency_thresholds(self) -> TestResult:
        """Test latency threshold monitoring"""
        self.log.info(f"=== Testing latency thresholds...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for latency threshold detection
            config = MonitorConfig.for_latency_stress()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate stress activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "latency_stress")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=200)

            # Analyze threshold packets
            threshold_packets = [p for p in packets if p.pkt_type == PktType.PktTypeThreshold.value]
            latency_packets = [p for p in threshold_packets if p.event_code == ARBThresholdCode.ARB_THRESH_REQUEST_LATENCY]

            details = f"Total: {len(packets)}, Threshold: {len(threshold_packets)}, Latency: {len(latency_packets)}"

            # Should generate some latency threshold packets under stress
            success = len(latency_packets) > 0
            return TestResult(
                passed=success,
                name="latency_thresholds",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "threshold_packets": len(threshold_packets),
                    "latency_threshold_packets": len(latency_packets),
                    "config_used": config.__dict__
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_latency_thresholds: {str(e)}")
            return TestResult(
                passed=False,
                name="latency_thresholds",
                details="Exception during latency threshold test",
                error_msg=str(e)
            )

    async def test_starvation_thresholds(self) -> TestResult:
        """Test starvation threshold monitoring"""
        self.log.info(f"=== Testing starvation thresholds...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for starvation detection
            config = MonitorConfig.for_starvation_detection()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate starvation activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "starvation")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze error packets for starvation
            error_packets = [p for p in packets if p.pkt_type == PktType.PktTypeError.value]
            starvation_errors = [p for p in error_packets if p.event_code == ARBErrorCode.ARB_ERR_STARVATION]

            details = f"Total: {len(packets)}, Errors: {len(error_packets)}, Starvation: {len(starvation_errors)}"

            success = len(starvation_errors) > 0
            return TestResult(
                passed=success,
                name="starvation_thresholds",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "error_packets": len(error_packets),
                    "starvation_error_packets": len(starvation_errors)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_starvation_thresholds: {str(e)}")
            return TestResult(
                passed=False,
                name="starvation_thresholds",
                details="Exception during starvation threshold test",
                error_msg=str(e)
            )

    async def test_fairness_thresholds(self) -> TestResult:
        """Test fairness threshold monitoring"""
        self.log.info(f"=== Testing fairness thresholds...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for fairness monitoring
            config = MonitorConfig.for_fairness_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate unfair activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(150, "unfair")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=200)

            # Analyze threshold packets for fairness
            threshold_packets = [p for p in packets if p.pkt_type == PktType.PktTypeThreshold.value]
            fairness_packets = [p for p in threshold_packets if p.event_code == ARBThresholdCode.ARB_THRESH_FAIRNESS_DEV]

            details = f"Total: {len(packets)}, Threshold: {len(threshold_packets)}, Fairness: {len(fairness_packets)}"

            success = len(fairness_packets) > 0
            return TestResult(
                passed=success,
                name="fairness_thresholds",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "threshold_packets": len(threshold_packets),
                    "fairness_threshold_packets": len(fairness_packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_fairness_thresholds: {str(e)}")
            return TestResult(
                passed=False,
                name="fairness_thresholds",
                details="Exception during fairness threshold test",
                error_msg=str(e)
            )

    async def test_active_request_thresholds(self) -> TestResult:
        """Test active request threshold monitoring"""
        self.log.info(f"=== Testing active request thresholds...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for active request monitoring
            config = MonitorConfig.for_active_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate high activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "all_active")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze threshold packets for active requests
            threshold_packets = [p for p in packets if p.pkt_type == PktType.PktTypeThreshold.value]
            active_packets = [p for p in threshold_packets if p.event_code == ARBThresholdCode.ARB_THRESH_ACTIVE_REQUESTS]

            details = f"Total: {len(packets)}, Threshold: {len(threshold_packets)}, Active: {len(active_packets)}"

            success = len(active_packets) > 0
            return TestResult(
                passed=success,
                name="active_request_thresholds",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "threshold_packets": len(threshold_packets),
                    "active_threshold_packets": len(active_packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_active_request_thresholds: {str(e)}")
            return TestResult(
                passed=False,
                name="active_request_thresholds",
                details="Exception during active request threshold test",
                error_msg=str(e)
            )

    async def test_efficiency_thresholds(self) -> TestResult:
        """Test efficiency threshold monitoring"""
        self.log.info(f"=== Testing efficiency thresholds...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for efficiency monitoring
            config = MonitorConfig.for_efficiency_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate inefficient activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "inefficient")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze threshold packets for efficiency
            threshold_packets = [p for p in packets if p.pkt_type == PktType.PktTypeThreshold.value]
            efficiency_packets = [p for p in threshold_packets if p.event_code == ARBThresholdCode.ARB_THRESH_EFFICIENCY]

            details = f"Total: {len(packets)}, Threshold: {len(threshold_packets)}, Efficiency: {len(efficiency_packets)}"

            success = len(efficiency_packets) > 0
            return TestResult(
                passed=success,
                name="efficiency_thresholds",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "threshold_packets": len(threshold_packets),
                    "efficiency_threshold_packets": len(efficiency_packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_efficiency_thresholds: {str(e)}")
            return TestResult(
                passed=False,
                name="efficiency_thresholds",
                details="Exception during efficiency threshold test",
                error_msg=str(e)
            )

    async def test_threshold_packet_data(self) -> TestResult:
        """Test threshold packet data accuracy"""
        self.log.info(f"=== Testing threshold packet data accuracy...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for comprehensive threshold monitoring
            config = MonitorConfig.comprehensive()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate controlled activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(80, "controlled")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=120)

            # Analyze threshold packet data quality
            threshold_packets = [p for p in packets if p.pkt_type == PktType.PktTypeThreshold.value]

            # Validate packet structure and data
            valid_packets = 0
            for packet in threshold_packets:
                if (hasattr(packet, 'event_code') and
                    hasattr(packet, 'data') and
                    packet.protocol == ProtocolType.PROTOCOL_ARB.value):
                    valid_packets += 1

            data_accuracy = (valid_packets / len(threshold_packets)) * 100 if threshold_packets else 0
            details = f"Total threshold packets: {len(threshold_packets)}, Valid: {valid_packets}, Accuracy: {data_accuracy:.1f}%"

            success = len(threshold_packets) > 0 and data_accuracy >= 90
            return TestResult(
                passed=success,
                name="threshold_packet_data",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "threshold_packets": len(threshold_packets),
                    "valid_packets": valid_packets,
                    "data_accuracy_percent": data_accuracy
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_threshold_packet_data: {str(e)}")
            return TestResult(
                passed=False,
                name="threshold_packet_data",
                details="Exception during threshold packet data test",
                error_msg=str(e)
            )
