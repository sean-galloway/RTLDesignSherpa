# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestSinkDatapathIntegration
# Purpose: RAPIDS Sink Data Path Integration Test - v1.0
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Sink Data Path Integration Test - v1.0

Integration test that leverages the existing SnkDatapathTB from the framework
to provide comprehensive sink data path validation following the user's guidance:

- Uses SnkDatapathTB from bin/CocoTBFramework/tbclasses/rapids/sink_datapath_tb.py
- Leverages real AXI4/Network component integration
- Validates 32-channel fixed configuration for scalability
- Tests Network receive to AXI write pipeline
- Provides superset testing capability at unit level

This provides comprehensive testing of the sink data path macro block.
"""

import pytest
import asyncio
import os
import sys
from pathlib import Path

# Add framework to path
framework_path = Path(__file__).parent.parent.parent.parent / "bin"
sys.path.insert(0, str(framework_path))

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

# Import the existing TB class from framework
from tbclasses.sink_datapath_tb import SnkDatapathTB


class TestSinkDatapathIntegration:
    """Integration test using SnkDatapathTB for comprehensive validation."""

    @pytest.mark.miop
    @pytest.mark.sink_datapath
    @pytest.mark.integration
    @pytest.mark.parametrize("test_level", ["basic", "medium", "full"])
    async def test_sink_datapath_comprehensive(self, dut, test_level):
        """Comprehensive sink data path test using framework TB class."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")  # 100MHz
        cocotb.start_soon(clock.start())

        # Initialize TB using framework class
        tb = SnkDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)

        # Initialize test environment
        await tb.initialize_test()

        # Reset sequence
        await tb.reset_sequence()

        # Test configuration based on level
        test_configs = {
            "basic": {
                "network_receptions": 32,
                "axi_writes": 32,
                "scheduler_notifications": 32,
                "multi_channel_ops": 16,
                "timing_profile": "fast"
            },
            "medium": {
                "network_receptions": 64,
                "axi_writes": 64,
                "scheduler_notifications": 64,
                "multi_channel_ops": 32,
                "timing_profile": "normal"
            },
            "full": {
                "network_receptions": 128,
                "axi_writes": 128,
                "scheduler_notifications": 128,
                "multi_channel_ops": 64,
                "timing_profile": "stress"
            }
        }

        config = test_configs[test_level]

        # Set timing profile based on test level
        tb.set_timing_profile(config["timing_profile"])

        # Test 1: Network packet reception across all 32 channels
        tb.log.info(f"=== Test 1: Network Reception ({config['network_receptions']} packets across 32 channels) ===")
        success, stats = await tb.test_mnoc_reception(count=config['network_receptions'])
        assert success, f"Network reception test failed: {stats}"
        tb.log.info(f"✅ Network reception: {stats['success_rate']:.1%} success rate, {stats['channels_tested']} channels tested")

        # Test 2: AXI write operations
        tb.log.info(f"=== Test 2: AXI Write Operations ({config['axi_writes']} writes) ===")
        success, stats = await tb.test_axi_write_operations(count=config['axi_writes'])
        assert success, f"AXI write operations failed: {stats}"
        tb.log.info(f"✅ AXI writes: {stats['success_rate']:.1%} success rate, avg latency: {stats['average_latency']:.1f}")

        # Test 3: Scheduler notification interface
        tb.log.info(f"=== Test 3: Scheduler Notifications ({config['scheduler_notifications']} notifications) ===")
        success, stats = await tb.test_scheduler_notification(count=config['scheduler_notifications'])
        assert success, f"Scheduler notification failed: {stats}"
        tb.log.info(f"✅ Scheduler notifications: {stats['success_rate']:.1%} success rate")

        # Test 4: Channel isolation (32-channel capability)
        tb.log.info(f"=== Test 4: Channel Isolation (32 channels) ===")
        success, stats = await tb.test_channel_isolation(count=32)
        assert success, f"Channel isolation failed: {stats}"
        tb.log.info(f"✅ Channel isolation: {stats['channels_tested']} channels tested, {stats['success_rate']:.1%} success rate")

        # Test 5: Multi-channel operations
        tb.log.info(f"=== Test 5: Multi-Channel Operations ({config['multi_channel_ops']} operations) ===")
        success, stats = await tb.test_multi_channel_operations(channels=16, count=config['multi_channel_ops'])
        assert success, f"Multi-channel operations failed: {stats}"
        tb.log.info(f"✅ Multi-channel: {stats['active_channels']} active channels, {stats['success_rate']:.1%} success rate")

        # Test 6: Stream boundary processing (EOS-only)
        tb.log.info(f"=== Test 6: Stream Boundary Processing (EOS) ===")
        success, stats = await tb.test_stream_boundary_processing()
        assert success, f"Stream boundary processing failed: {stats}"
        tb.log.info(f"✅ EOS processing: {stats['success_rate']:.1%} success rate")

        # Test 7: Credit return mechanism
        tb.log.info(f"=== Test 7: Credit Return Mechanism ===")
        success, stats = await tb.test_credit_return_mechanism()
        assert success, f"Credit return mechanism failed: {stats}"
        tb.log.info(f"✅ Credit return: {stats['success_rate']:.1%} success rate")

        # Test 8: Stress test (if full level)
        if test_level == "full":
            tb.log.info(f"=== Test 8: Stress Test (100 mixed operations) ===")
            success, stats = await tb.stress_test(count=100)
            # Stress test allows some failures
            assert stats['success_rate'] > 0.9, f"Stress test failed: {stats['success_rate']:.1%} success rate too low"
            tb.log.info(f"✅ Stress test: {stats['success_rate']:.1%} success rate")

        # Finalize test and get comprehensive statistics
        tb.finalize_test()
        final_stats = tb.get_test_stats()

        # Validate overall test performance
        assert final_stats['summary']['successful_operations'] > 0, "No successful operations recorded"
        assert final_stats['summary']['operations_per_second'] > 0, "Zero operations per second"

        # Log comprehensive results
        tb.log.info("=== COMPREHENSIVE SINK DATAPATH TEST RESULTS ===")
        tb.log.info(f"Test Level: {test_level}")
        tb.log.info(f"Total Operations: {final_stats['summary']['total_operations']}")
        tb.log.info(f"Successful Operations: {final_stats['summary']['successful_operations']}")
        tb.log.info(f"Failed Operations: {final_stats['summary']['failed_operations']}")
        tb.log.info(f"Test Duration: {final_stats['summary']['test_duration']:.2f}s")
        tb.log.info(f"Operations/Second: {final_stats['summary']['operations_per_second']:.1f}")

        # Channel utilization
        channels = final_stats['channels']
        tb.log.info(f"Total Channels Used: {channels['total_channels_used']}")
        tb.log.info(f"Most Used Channel: {channels['most_used_channel']}")
        tb.log.info(f"Least Used Channel: {channels['least_used_channel']}")

        # Operation breakdown
        operations = final_stats['operations']
        tb.log.info(f"Network Receptions: {operations['network_receptions']}")
        tb.log.info(f"AXI Writes: {operations['axi_writes']}")
        tb.log.info(f"Scheduler Notifications: {operations['scheduler_notifications']}")
        tb.log.info(f"Credit Returns: {operations['credit_returns']}")

        # Performance metrics
        performance = final_stats['performance']
        tb.log.info(f"Average Latency: {performance['average_latency']:.1f}")
        tb.log.info(f"Peak Channels Active: {performance['peak_channels_active']}")
        tb.log.info(f"Packets/Second: {performance['packets_per_second']:.1f}")

        tb.log.info("✅ SINK DATAPATH INTEGRATION TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.sink_datapath
    @pytest.mark.scalability
    async def test_32_channel_buffer_management(self, dut):
        """Test 32-channel buffer management and SRAM control."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = SnkDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)
        await tb.initialize_test()
        await tb.reset_sequence()

        # Verify 32-channel configuration
        assert tb.TEST_CHANNELS == 32, f"Expected 32 channels, got {tb.TEST_CHANNELS}"

        # Test buffer management for all 32 channels
        tb.log.info("=== Testing 32-Channel Buffer Management ===")

        # Test SRAM buffer allocation and management
        success, stats = await tb.test_sram_buffer_management(count=64)  # 2 operations per channel
        assert success, f"Buffer management test failed: {stats}"
        assert stats['channels_tested'] == 32, f"Expected 32 channels tested, got {stats['channels_tested']}"

        # Test credit management across all channels
        success, stats = await tb.test_credit_management_all_channels()
        assert success, f"Credit management test failed: {stats}"

        tb.log.info("✅ 32-CHANNEL BUFFER MANAGEMENT TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.sink_datapath
    @pytest.mark.framework
    async def test_framework_component_integration(self, dut):
        """Test proper integration with framework AXI4 and Network components."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = SnkDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)
        await tb.initialize_test()
        await tb.reset_sequence()

        # Verify framework component interfaces are properly created
        assert tb.axi_slave is not None, "AXI slave not created"
        assert tb.network_master is not None, "Network master not created"
        assert tb.memory_model is not None, "Memory model not created"

        # Verify Network compliance checker if enabled
        if tb.test_config['enable_compliance_check']:
            assert tb.network_compliance_checker is not None, "Network compliance checker not created"

        # Test framework component functionality
        tb.log.info("=== Testing Framework Component Integration ===")

        # Test AXI4 component integration
        success, stats = await tb.test_axi_write_operations(count=16)
        assert success, f"Framework AXI4 integration failed: {stats}"

        # Test Network component integration
        success, stats = await tb.test_mnoc_reception(count=16)
        assert success, f"Framework Network integration failed: {stats}"

        tb.log.info("✅ FRAMEWORK COMPONENT INTEGRATION TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.sink_datapath
    @pytest.mark.eos_flow
    async def test_eos_completion_flow(self, dut):
        """Test EOS completion flow from SRAM to scheduler."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = SnkDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)
        await tb.initialize_test()
        await tb.reset_sequence()

        tb.log.info("=== Testing EOS Completion Flow ===")

        # Test packet-level EOS from SRAM control
        success, stats = await tb.test_packet_level_eos(count=16)
        assert success, f"Packet-level EOS test failed: {stats}"

        # Test descriptor-level EOS to scheduler
        success, stats = await tb.test_descriptor_level_eos(count=16)
        assert success, f"Descriptor-level EOS test failed: {stats}"

        # Test EOS coordination between SRAM and scheduler
        success, stats = await tb.test_eos_coordination(count=16)
        assert success, f"EOS coordination test failed: {stats}"

        tb.log.info("✅ EOS COMPLETION FLOW TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.sink_datapath
    @pytest.mark.performance
    async def test_data_flow_performance(self, dut):
        """Test end-to-end data flow performance."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = SnkDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)
        await tb.initialize_test()
        await tb.reset_sequence()

        # Set fast timing for performance test
        tb.set_timing_profile("fast")

        tb.log.info("=== Testing Data Flow Performance ===")

        # Run performance test sequence
        operations_per_test = 32

        # Measure Network reception performance
        success, mnoc_stats = await tb.test_mnoc_reception(count=operations_per_test)
        assert success, "Network performance test failed"

        # Measure AXI write performance
        success, axi_stats = await tb.test_axi_write_operations(count=operations_per_test)
        assert success, "AXI performance test failed"

        # Measure scheduler notification performance
        success, scheduler_stats = await tb.test_scheduler_notification(count=operations_per_test)
        assert success, "Scheduler performance test failed"

        # Get final performance statistics
        tb.finalize_test()
        final_stats = tb.get_test_stats()

        # Validate performance metrics
        assert final_stats['summary']['operations_per_second'] > 1000, f"Performance too low: {final_stats['summary']['operations_per_second']:.1f} ops/sec"

        tb.log.info(f"✅ Performance Test: {final_stats['summary']['operations_per_second']:.1f} operations/second")
        tb.log.info("✅ DATA FLOW PERFORMANCE TEST PASSED")


# Pytest fixtures for test configuration
@pytest.fixture
def dut():
    """Mock DUT fixture - in real testing this would be the actual DUT."""
    # This is a placeholder - in actual testing, cocotb provides the DUT
    pass


if __name__ == "__main__":
    # For direct execution during development
    print("RAPIDS Sink Data Path Integration Test")
    print("This test uses SnkDatapathTB from the framework")
    print("Run with: pytest val/rapids/integration_tests/test_sink_datapath_integration.py -v")