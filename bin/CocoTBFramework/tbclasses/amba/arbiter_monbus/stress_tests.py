# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: StressAndReliabilityTest
# Purpose: Stress and Reliability Tests for Arbiter MonBus Common
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Stress and Reliability Tests for Arbiter MonBus Common

This module contains high-stress and reliability tests including
FIFO overflow handling, configuration stability, and extended operation tests.

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


class StressAndReliabilityTest:
    """Tests stress conditions and reliability"""

    def __init__(self, tb):
        self.tb = tb
        self.log = tb.log

    async def test_fifo_overflow_handling(self) -> TestResult:
        """Test FIFO overflow handling under extreme stress"""
        self.log.info(f"=== Testing FIFO overflow handling...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for maximum packet generation
            config = MonitorConfig.stress()
            await self.tb.apply_monitor_config(config)

            # Block MonBus slave to force FIFO overflow
            self.tb.monbus_slave.set_ready_probability(0.0)

            # Reset statistics and generate intensive activity to force overflow
            self.tb.monbus_slave.reset_statistics()
            await self.tb.generate_arbiter_activity(self.tb.fifo_depth * 3, "all_active")

            # Check FIFO status under overflow conditions
            initial_fifo_count = int(self.tb.dut.debug_fifo_count.value)

            # Enable draining and verify recovery
            self.tb.monbus_slave.set_ready_probability(1.0)
            await self.tb.wait_clocks('clk', 50)

            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=100)
            final_fifo_count = int(self.tb.dut.debug_fifo_count.value)

            details = f"Initial FIFO: {initial_fifo_count}, Final: {final_fifo_count}, Recovered packets: {len(packets)}"

            # Should handle overflow gracefully and recover
            success = len(packets) > 0 and final_fifo_count < initial_fifo_count
            return TestResult(
                passed=success,
                name="fifo_overflow_handling",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "initial_fifo_count": initial_fifo_count,
                    "final_fifo_count": final_fifo_count,
                    "recovered_packets": len(packets),
                    "fifo_depth": self.tb.fifo_depth
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_fifo_overflow_handling: {str(e)}")
            return TestResult(
                passed=False,
                name="fifo_overflow_handling",
                details="Exception during FIFO overflow handling test",
                error_msg=str(e)
            )

    async def test_configuration_stability(self) -> TestResult:
        """Test configuration stability under stress"""
        self.log.info(f"=== Testing configuration stability...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            total_packets = 0
            config_changes = 0

            # Test multiple configuration changes under stress
            configs = [
                MonitorConfig.basic(),
                MonitorConfig.stress(),
                MonitorConfig.comprehensive(),
                MonitorConfig.minimal()
            ]

            for i, config in enumerate(configs):
                await self.tb.apply_monitor_config(config)
                config_changes += 1

                # Generate activity with each configuration
                self.tb.monbus_slave.reset_statistics()
                await self.tb.generate_arbiter_activity(50, f"config_test_{i}")
                packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=80)
                total_packets += len(packets)

            details = f"Config changes: {config_changes}, Total packets: {total_packets}"

            # Should maintain stability across configuration changes
            success = total_packets > 0 and config_changes == len(configs)
            return TestResult(
                passed=success,
                name="configuration_stability",
                details=details,
                packets_collected=total_packets,
                debug_info={
                    "configuration_changes": config_changes,
                    "total_packets": total_packets,
                    "configurations_tested": len(configs)
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_configuration_stability: {str(e)}")
            return TestResult(
                passed=False,
                name="configuration_stability",
                details="Exception during configuration stability test",
                error_msg=str(e)
            )

    async def test_extended_operation(self) -> TestResult:
        """Test extended operation over long duration"""
        self.log.info(f"=== Testing extended operation...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for extended monitoring
            config = MonitorConfig.for_extended_operation()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and run extended operation
            self.tb.monbus_slave.reset_statistics()
            total_packets = 0
            cycles_completed = 0

            # Run multiple cycles of activity
            for cycle in range(5):
                await self.tb.generate_arbiter_activity(100, f"extended_cycle_{cycle}")
                packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=150)
                total_packets += len(packets)
                cycles_completed += 1

                # Brief pause between cycles
                await self.tb.wait_clocks('clk', 20)

            details = f"Cycles completed: {cycles_completed}, Total packets: {total_packets}"

            # Should maintain operation across extended duration
            success = cycles_completed == 5 and total_packets > 0
            return TestResult(
                passed=success,
                name="extended_operation",
                details=details,
                packets_collected=total_packets,
                debug_info={
                    "cycles_completed": cycles_completed,
                    "total_packets": total_packets,
                    "average_packets_per_cycle": total_packets / cycles_completed if cycles_completed > 0 else 0
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_extended_operation: {str(e)}")
            return TestResult(
                passed=False,
                name="extended_operation",
                details="Exception during extended operation test",
                error_msg=str(e)
            )

    async def test_rapid_enable_disable_cycles(self) -> TestResult:
        """Test rapid enable/disable cycles"""
        self.log.info(f"=== Testing rapid enable/disable cycles...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            total_packets = 0
            cycles_completed = 0

            # Perform rapid enable/disable cycles
            for cycle in range(10):
                # Enable monitor
                config = MonitorConfig.basic()
                await self.tb.apply_monitor_config(config)

                # Brief activity
                self.tb.monbus_slave.reset_statistics()
                await self.tb.generate_arbiter_activity(20, "rapid_cycle")
                packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=30)
                total_packets += len(packets)

                # Disable monitor
                disabled_config = MonitorConfig.disabled()
                await self.tb.apply_monitor_config(disabled_config)

                # Brief disabled period
                await self.tb.wait_clocks('clk', 10)
                cycles_completed += 1

            details = f"Rapid cycles completed: {cycles_completed}, Total packets: {total_packets}"

            # Should handle rapid switching gracefully
            success = cycles_completed == 10 and total_packets > 0
            return TestResult(
                passed=success,
                name="rapid_enable_disable_cycles",
                details=details,
                packets_collected=total_packets,
                debug_info={
                    "cycles_completed": cycles_completed,
                    "total_packets": total_packets
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_rapid_enable_disable_cycles: {str(e)}")
            return TestResult(
                passed=False,
                name="rapid_enable_disable_cycles",
                details="Exception during rapid enable/disable cycles test",
                error_msg=str(e)
            )

    async def test_maximum_packet_rate(self) -> TestResult:
        """Test maximum packet generation rate"""
        self.log.info(f"=== Testing maximum packet rate...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for maximum packet generation
            config = MonitorConfig.maximum_rate()
            await self.tb.apply_monitor_config(config)

            # Reset statistics and generate maximum activity
            self.tb.monbus_slave.reset_statistics()
            start_time = self.tb.get_time_ns()
            await self.tb.generate_arbiter_activity(200, "maximum_rate")
            packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=300)
            end_time = self.tb.get_time_ns()

            # Calculate packet rate
            duration_ns = end_time - start_time
            packet_rate = (len(packets) * 1e9) / duration_ns if duration_ns > 0 else 0

            details = f"Packets: {len(packets)}, Duration: {duration_ns:.0f}ns, Rate: {packet_rate:.1f} pkt/s"

            # Should generate packets at reasonable rate
            success = len(packets) > 0 and packet_rate > 0
            return TestResult(
                passed=success,
                name="maximum_packet_rate",
                details=details,
                packets_collected=len(packets),
                debug_info={
                    "packets_generated": len(packets),
                    "duration_ns": duration_ns,
                    "packet_rate_per_second": packet_rate
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_maximum_packet_rate: {str(e)}")
            return TestResult(
                passed=False,
                name="maximum_packet_rate",
                details="Exception during maximum packet rate test",
                error_msg=str(e)
            )

    async def test_backpressure_handling(self) -> TestResult:
        """Test backpressure handling capabilities"""
        self.log.info(f"=== Testing backpressure handling...{self.tb.get_time_ns_str()} ===")

        try:
            # Prepare clean test state
            await self.tb.prepare_clean_test_state()

            # Configure for stress testing
            config = MonitorConfig.stress()
            await self.tb.apply_monitor_config(config)

            # Apply varying backpressure levels
            backpressure_levels = [0.0, 0.25, 0.5, 0.75, 1.0]
            total_packets = 0

            for i, backpressure in enumerate(backpressure_levels):
                self.tb.monbus_slave.set_ready_probability(1.0 - backpressure)
                self.tb.monbus_slave.reset_statistics()

                await self.tb.generate_arbiter_activity(50, f"backpressure_{i}")
                packets = await self.tb.monbus_slave.get_received_packets(timeout_cycles=80)
                total_packets += len(packets)

                # Allow system to stabilize
                await self.tb.wait_clocks('clk', 20)

            # Restore normal operation
            self.tb.monbus_slave.set_ready_probability(1.0)

            details = f"Backpressure levels tested: {len(backpressure_levels)}, Total packets: {total_packets}"

            # Should handle backpressure gracefully
            success = total_packets > 0
            return TestResult(
                passed=success,
                name="backpressure_handling",
                details=details,
                packets_collected=total_packets,
                debug_info={
                    "backpressure_levels_tested": len(backpressure_levels),
                    "total_packets": total_packets
                }
            )

        except Exception as e:
            self.log.error(f"Exception in test_backpressure_handling: {str(e)}")
            return TestResult(
                passed=False,
                name="backpressure_handling",
                details="Exception during backpressure handling test",
                error_msg=str(e)
            )
