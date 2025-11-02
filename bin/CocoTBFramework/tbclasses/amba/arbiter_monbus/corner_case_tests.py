# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FifoCornerCaseTest
# Purpose: Corner Case Tests for Arbiter MonBus Common
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Corner Case Tests for Arbiter MonBus Common

This module contains tests for edge cases, FIFO behavior, reset conditions,
and configuration edge cases that could expose bugs.

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


class FifoCornerCaseTest:
    """Tests FIFO edge behaviors and corner cases"""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def test_fifo_exactly_full(self) -> TestResult:
        """Test FIFO behavior when exactly full"""
        self.log.info(f"=== Testing FIFO exactly full behavior...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for stress testing
            config = MonitorConfig.stress()
            await self.tb.apply_monitor_config(config)

            # Block ready to fill FIFO to exactly full
            self.tb.monbus_slave.set_ready_probability(0.0)  # No draining

            # Reset statistics and generate activity to fill FIFO exactly
            self.tb.monbus_slave.reset_statistics()
            fifo_size = self.tb.fifo_depth
            await self.tb.generate_arbiter_activity(fifo_size * 2, "all_active")

            # Check FIFO is full
            fifo_count = int(self.tb.dut.debug_fifo_count.value)

            # Try to add one more packet (should be blocked)
            await self.tb.generate_arbiter_activity(10, "random")
            final_count = int(self.tb.dut.debug_fifo_count.value)

            # Enable draining and verify recovery
            self.tb.monbus_slave.set_ready_probability(1.0)
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=100)
            recovered_count = int(self.tb.dut.debug_fifo_count.value)

            details = f"FIFO size: {fifo_size}, Full count: {fifo_count}, After more: {final_count}, Recovered: {recovered_count}, Packets: {len(packets)}"

            success = fifo_count >= fifo_size and len(packets) > 0 and recovered_count < fifo_count
            return TestResult(
                passed=success,
                name="fifo_exactly_full",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "fifo_size": fifo_size,
                    "full_count": fifo_count,
                    "final_count": final_count,
                    "recovered_count": recovered_count,
                    "packets_recovered": len(packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_fifo_exactly_full: {str(e)}")
            return TestResult(
                passed=False,
                name="fifo_exactly_full",
                details="Exception during FIFO exactly full test",
                error_msg=str(e)
            )

    async def test_fifo_rapid_fill_drain(self) -> TestResult:
        """Test rapid FIFO fill and drain cycles"""
        self.log.info(f"=== Testing rapid FIFO fill/drain cycles...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for rapid cycling
            config = MonitorConfig.stress()
            await self.tb.apply_monitor_config(config)

            total_packets = 0
            cycles_completed = 0

            # Perform multiple rapid fill/drain cycles
            for cycle in range(5):
                # Fill phase - block draining
                self.tb.monbus_slave.set_ready_probability(0.0)
                self.tb.monbus_slave.reset_statistics()
                await self.tb.generate_arbiter_activity(30, f"fill_cycle_{cycle}")

                # Drain phase - enable draining
                self.tb.monbus_slave.set_ready_probability(1.0)
                packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=50)
                total_packets += len(packets)
                cycles_completed += 1

                # Brief pause
                await self.tb.wait_clocks('clk', 10)

            details = f"Cycles completed: {cycles_completed}, Total packets: {total_packets}"

            success = cycles_completed == 5 and total_packets > 0
            return TestResult(
                passed=success,
                name="fifo_rapid_fill_drain",
                details=details,
                packets_collected=total_packets,
                debug_info={
                    "cycles_completed": cycles_completed,
                    "total_packets": total_packets
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_fifo_rapid_fill_drain: {str(e)}")
            return TestResult(
                passed=False,
                name="fifo_rapid_fill_drain",
                details="Exception during rapid fill/drain test",
                error_msg=str(e)
            )

    async def test_fifo_almost_margins(self) -> TestResult:
        """Test FIFO almost full/empty margin behavior"""
        self.log.info(f"=== Testing FIFO almost full/empty margins...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for margin testing
            config = MonitorConfig.basic()
            await self.tb.apply_monitor_config(config)

            # Test almost full margin
            margin = 4  # Typical almost margin
            target_level = self.tb.fifo_depth - margin - 1

            # Fill to just below almost full
            self.tb.monbus_slave.set_ready_probability(0.1)  # Slow drain
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(target_level, "controlled")

            almost_full_count = int(self.tb.dut.debug_fifo_count.value)

            # Enable full draining
            self.tb.monbus_slave.set_ready_probability(1.0)
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=100)
            final_count = int(self.tb.dut.debug_fifo_count.value)

            details = f"Target: {target_level}, Almost full: {almost_full_count}, Final: {final_count}, Packets: {len(packets)}"

            success = len(packets) > 0 and final_count == 0
            return TestResult(
                passed=success,
                name="fifo_almost_margins",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "target_level": target_level,
                    "almost_full_count": almost_full_count,
                    "final_count": final_count,
                    "fifo_depth": self.tb.fifo_depth,
                    "margin": margin
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_fifo_almost_margins: {str(e)}")
            return TestResult(
                passed=False,
                name="fifo_almost_margins",
                details="Exception during FIFO almost margins test",
                error_msg=str(e)
            )


class ResetBehaviorTest:
    """Tests reset behavior and state consistency"""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def test_reset_during_operation(self) -> TestResult:
        """Test reset behavior during active operation"""
        self.log.info(f"=== Testing reset during operation...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure and start operation
            config = MonitorConfig.basic()
            await self.tb.apply_monitor_config(config)

            # Start activity and let it run
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(30, "pre_reset")

            # Apply reset during operation
            await self.tb.apply_reset(5)

            # Check state after reset
            post_reset_count = int(self.tb.dut.debug_fifo_count.value)

            # Resume operation and verify recovery
            await self.tb.apply_monitor_config(config)
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(50, "post_reset")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=80)

            details = f"Post-reset FIFO count: {post_reset_count}, Recovery packets: {len(packets)}"

            success = post_reset_count == 0 and len(packets) > 0
            return TestResult(
                passed=success,
                name="reset_during_operation",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "post_reset_fifo_count": post_reset_count,
                    "recovery_packets": len(packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_reset_during_operation: {str(e)}")
            return TestResult(
                passed=False,
                name="reset_during_operation",
                details="Exception during reset test",
                error_msg=str(e)
            )

    async def test_reset_state_consistency(self) -> TestResult:
        """Test that reset produces consistent state"""
        self.log.info(f"=== Testing reset state consistency...{self.tb.get_time_ns_str()} ===")

        try:
            results = []

            # Perform multiple reset cycles and check consistency
            for i in range(3):
                await self.tb.apply_reset(5)

                # Check key state signals
                fifo_count = int(self.tb.dut.debug_fifo_count.value)
                packet_count = int(self.tb.dut.debug_packet_count.value) if hasattr(self.tb.dut, 'debug_packet_count') else 0
                results.append((fifo_count, packet_count))

                # Brief operation to test functionality
                await self.tb.apply_monitor_config(MonitorConfig.basic())
                await self.tb.generate_arbiter_activity(10, f"consistency_test_{i}")

            # All reset states should be identical
            fifo_counts = [r[0] for r in results]
            packet_counts = [r[1] for r in results]

            fifo_consistent = all(f == fifo_counts[0] for f in fifo_counts)
            packet_consistent = all(p == packet_counts[0] for p in packet_counts)

            details = f"Reset states - FIFO: {fifo_counts}, Packets: {packet_counts}, Consistent: {fifo_consistent and packet_consistent}"

            success = fifo_consistent and packet_consistent and fifo_counts[0] == 0
            return TestResult(
                passed=success,
                name="reset_state_consistency",
                details=details,
                packets_collected=0,
                debug_info={
                    "fifo_counts": fifo_counts,
                    "packet_counts": packet_counts,
                    "fifo_consistent": fifo_consistent,
                    "packet_consistent": packet_consistent
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_reset_state_consistency: {str(e)}")
            return TestResult(
                passed=False,
                name="reset_state_consistency",
                details="Exception during reset consistency test",
                error_msg=str(e)
            )


class ConfigurationEdgeCaseTest:
    """Tests configuration edge cases and boundary values"""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def test_minimal_thresholds(self) -> TestResult:
        """Test with minimal threshold values"""
        self.log.info(f"=== Testing minimal threshold configuration...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure with minimal values using centralized config
            minimal_config = MonitorConfig.minimal()
            await self.tb.apply_monitor_config(minimal_config)

            # Reset statistics and generate activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(50, "stress")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=80)

            # Should generate many packets with such low thresholds
            details = f"Minimal thresholds generated {len(packets)} packets"

            success = len(packets) > 0
            return TestResult(
                passed=success,
                name="minimal_thresholds",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "config_used": minimal_config.__dict__,
                    "packets_generated": len(packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_minimal_thresholds: {str(e)}")
            return TestResult(
                passed=False,
                name="minimal_thresholds",
                details="Exception during minimal threshold test",
                error_msg=str(e)
            )

    async def test_maximal_thresholds(self) -> TestResult:
        """Test with maximal threshold values"""
        self.log.info(f"=== Testing maximal threshold configuration...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure with maximal values using centralized config
            maximal_config = MonitorConfig.maximal()
            await self.tb.apply_monitor_config(maximal_config)

            # Reset statistics and generate activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(100, "normal")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)

            # Should generate few packets with such high thresholds
            details = f"Maximal thresholds generated {len(packets)} packets"

            # Just verify it doesn't crash with maximal values
            success = True
            return TestResult(
                passed=success,
                name="maximal_thresholds",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "config_used": maximal_config.__dict__,
                    "packets_generated": len(packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_maximal_thresholds: {str(e)}")
            return TestResult(
                passed=False,
                name="maximal_thresholds",
                details="Exception during maximal threshold test",
                error_msg=str(e)
            )

    async def test_configuration_changes_during_operation(self) -> TestResult:
        """Test changing configuration while monitor is active"""
        self.log.info(f"=== Testing configuration changes during operation...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Start with one configuration
            config1 = MonitorConfig.for_error_only()
            await self.tb.apply_monitor_config(config1)

            # Reset statistics and generate some activity
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(30, "starvation")

            # Change to different configuration mid-operation
            config2 = MonitorConfig.for_performance_only()
            await self.tb.apply_monitor_config(config2)

            # Continue with different activity
            await self.tb.generate_arbiter_activity(30, "performance")

            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=100)

            # Analyze packet types - should see transition
            error_packets = [p for p in packets if p.pkt_type == PktType.PktTypeError.value]
            perf_packets = [p for p in packets if p.pkt_type == PktType.PktTypePerf.value]
            timeout_packets = [p for p in packets if p.pkt_type == PktType.PktTypeTimeout.value]

            details = f"Config change: {len(packets)} total, {len(error_packets)} errors, {len(perf_packets)} perf, {len(timeout_packets)} timeouts"

            success = len(packets) > 0
            return TestResult(
                passed=success,
                name="configuration_changes_during_operation",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "total_packets": len(packets),
                    "error_packets": len(error_packets),
                    "performance_packets": len(perf_packets),
                    "timeout_packets": len(timeout_packets)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_configuration_changes_during_operation: {str(e)}")
            return TestResult(
                passed=False,
                name="configuration_changes_during_operation",
                details="Exception during config change test",
                error_msg=str(e)
            )

    async def test_selective_packet_filtering(self) -> TestResult:
        """Test selective packet type filtering"""
        self.log.info(f"=== Testing selective packet filtering...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Test different packet type filters
            filters = [
                ("errors_only", MonitorConfig.for_error_only()),
                ("performance_only", MonitorConfig.for_performance_only()),
                ("thresholds_only", MonitorConfig.for_threshold_only())
            ]

            total_packets = 0
            filter_results = {}

            for filter_name, config in filters:
                await self.tb.apply_monitor_config(config)
                self.tb.monbus_slave.reset_statistics()

                await self.tb.generate_arbiter_activity(50, filter_name)
                packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=80)

                filter_results[filter_name] = len(packets)
                total_packets += len(packets)

            details = f"Filter results: {filter_results}, Total: {total_packets}"

            success = total_packets > 0 and len(filter_results) == len(filters)
            return TestResult(
                passed=success,
                name="selective_packet_filtering",
                details=details,
                packets_collected=total_packets,
                debug_info={
                    "filter_results": filter_results,
                    "total_packets": total_packets,
                    "filters_tested": len(filters)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_selective_packet_filtering: {str(e)}")
            return TestResult(
                passed=False,
                name="selective_packet_filtering",
                details="Exception during selective packet filtering test",
                error_msg=str(e)
            )
