# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PerformanceMonitoringTest
# Purpose: Performance Monitoring Tests for Arbiter MonBus Common
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Performance Monitoring Tests for Arbiter MonBus Common

This module contains tests for performance monitoring including grant tracking,
ACK tracking, and performance event generation.

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


class PerformanceMonitoringTest:
    """Tests performance monitoring functionality"""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def test_performance_event_generation(self) -> TestResult:
        """Test basic performance event generation"""
        self.log.info(f"=== Testing performance event generation...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for performance monitoring
            config = MonitorConfig.for_performance_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate performance activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "performance")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze performance packets
            perf_packets = [p for p in packets if p.pkt_type == PktType.PktTypePerf.value]
            completion_packets = [p for p in packets if p.pkt_type == PktType.PktTypeCompletion.value]

            details = f"Total: {len(packets)}, Performance: {len(perf_packets)}, Completion: {len(completion_packets)}"

            success = len(perf_packets) > 0 or len(completion_packets) > 0
            return TestResult(
                passed=success,
                name="performance_event_generation",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "performance_packets": len(perf_packets),
                    "completion_packets": len(completion_packets),
                    "config_used": config.__dict__
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_performance_event_generation: {str(e)}")
            return TestResult(
                passed=False,
                name="performance_event_generation",
                details="Exception during performance event generation test",
                error_msg=str(e)
            )

    async def test_grant_tracking(self) -> TestResult:
        """Test grant event tracking and monitoring"""
        self.log.info(f"=== Testing grant tracking...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for grant tracking
            config = MonitorConfig.for_grant_tracking()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate grant activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(80, "grant_focused")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=120)

            # Analyze completion packets for grant events
            completion_packets = [p for p in packets if p.pkt_type == PktType.PktTypeCompletion.value]
            grant_events = [p for p in completion_packets if p.event_code == ARBCompletionCode.ARB_COMPL_GRANT_ISSUED]

            details = f"Total: {len(packets)}, Completion: {len(completion_packets)}, Grant events: {len(grant_events)}"

            success = len(grant_events) > 0
            return TestResult(
                passed=success,
                name="grant_tracking",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "completion_packets": len(completion_packets),
                    "grant_event_packets": len(grant_events)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_grant_tracking: {str(e)}")
            return TestResult(
                passed=False,
                name="grant_tracking",
                details="Exception during grant tracking test",
                error_msg=str(e)
            )

    async def test_ack_tracking(self) -> TestResult:
        """Test ACK event tracking and monitoring"""
        self.log.info(f"=== Testing ACK tracking...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for ACK tracking
            config = MonitorConfig.for_ack_tracking()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate ACK activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(80, "ack_focused")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=120)

            # Analyze completion packets for ACK events
            completion_packets = [p for p in packets if p.pkt_type == PktType.PktTypeCompletion.value]
            ack_events = [p for p in completion_packets if p.event_code == ARBCompletionCode.ARB_COMPL_ACK_RECEIVED]

            details = f"Total: {len(packets)}, Completion: {len(completion_packets)}, ACK events: {len(ack_events)}"

            success = len(ack_events) > 0
            return TestResult(
                passed=success,
                name="ack_tracking",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "completion_packets": len(completion_packets),
                    "ack_event_packets": len(ack_events)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_ack_tracking: {str(e)}")
            return TestResult(
                passed=False,
                name="ack_tracking",
                details="Exception during ACK tracking test",
                error_msg=str(e)
            )

    async def test_performance_metrics_accuracy(self) -> TestResult:
        """Test accuracy of performance metrics"""
        self.log.info(f"=== Testing performance metrics accuracy...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for comprehensive performance monitoring
            config = MonitorConfig.for_performance_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate controlled activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "controlled_performance")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze performance packet data quality
            perf_packets = [p for p in packets if p.pkt_type == PktType.PktTypePerf.value]

            # Validate performance metrics
            valid_metrics = 0
            for packet in perf_packets:
                if (hasattr(packet, 'event_code') and
                    hasattr(packet, 'data') and
                    packet.protocol == ProtocolType.PROTOCOL_ARB.value):
                    # Check if data looks reasonable (non-zero, within expected ranges)
                    if hasattr(packet, 'data') and packet.data != 0:
                        valid_metrics += 1

            metrics_accuracy = (valid_metrics / len(perf_packets)) * 100 if perf_packets else 0
            details = f"Performance packets: {len(perf_packets)}, Valid metrics: {valid_metrics}, Accuracy: {metrics_accuracy:.1f}%"

            success = len(perf_packets) > 0 and metrics_accuracy >= 80
            return TestResult(
                passed=success,
                name="performance_metrics_accuracy",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "performance_packets": len(perf_packets),
                    "valid_metrics": valid_metrics,
                    "metrics_accuracy_percent": metrics_accuracy
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_performance_metrics_accuracy: {str(e)}")
            return TestResult(
                passed=False,
                name="performance_metrics_accuracy",
                details="Exception during performance metrics accuracy test",
                error_msg=str(e)
            )

    async def test_throughput_monitoring(self) -> TestResult:
        """Test throughput monitoring capabilities"""
        self.log.info(f"=== Testing throughput monitoring...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for throughput monitoring
            config = MonitorConfig.for_throughput_monitoring()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate high-throughput activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(120, "high_throughput")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=180)

            # Analyze throughput-related packets
            perf_packets = [p for p in packets if p.pkt_type == PktType.PktTypePerf.value]
            throughput_events = [p for p in perf_packets if p.event_code == ARBPerformanceCode.ARB_PERF_THROUGHPUT]

            details = f"Total: {len(packets)}, Performance: {len(perf_packets)}, Throughput: {len(throughput_events)}"

            success = len(throughput_events) > 0
            return TestResult(
                passed=success,
                name="throughput_monitoring",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "performance_packets": len(perf_packets),
                    "throughput_event_packets": len(throughput_events)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_throughput_monitoring: {str(e)}")
            return TestResult(
                passed=False,
                name="throughput_monitoring",
                details="Exception during throughput monitoring test",
                error_msg=str(e)
            )

    async def test_latency_performance_tracking(self) -> TestResult:
        """Test latency performance tracking"""
        self.log.info(f"=== Testing latency performance tracking...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for latency performance monitoring
            config = MonitorConfig.for_latency_performance()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate latency-focused activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "latency_focused")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Analyze latency performance packets
            perf_packets = [p for p in packets if p.pkt_type == PktType.PktTypePerf.value]
            latency_events = [p for p in perf_packets if p.event_code == ARBPerformanceCode.ARB_PERF_LATENCY]

            details = f"Total: {len(packets)}, Performance: {len(perf_packets)}, Latency: {len(latency_events)}"

            success = len(latency_events) > 0
            return TestResult(
                passed=success,
                name="latency_performance_tracking",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "performance_packets": len(perf_packets),
                    "latency_event_packets": len(latency_events)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_latency_performance_tracking: {str(e)}")
            return TestResult(
                passed=False,
                name="latency_performance_tracking",
                details="Exception during latency performance tracking test",
                error_msg=str(e)
            )
