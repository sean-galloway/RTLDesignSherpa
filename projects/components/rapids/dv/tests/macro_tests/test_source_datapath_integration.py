# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestSourceDatapathIntegration
# Purpose: RAPIDS Source Data Path Integration Test - v1.0
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Source Data Path Integration Test - v1.0

Integration test that leverages the existing SrcDatapathTB from the framework
to provide comprehensive source data path validation following the user's guidance:

- Uses SrcDatapathTB from bin/CocoTBFramework/tbclasses/rapids/source_datapath_tb.py
- Leverages real AXI4/Network component integration
- Validates 32-channel fixed configuration for scalability
- Tests AXI read to Network transmit pipeline
- Provides superset testing capability at unit level

This provides comprehensive testing of the source data path macro block.
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
from tbclasses.source_datapath_tb import SrcDatapathTB


class TestSourceDatapathIntegration:
    """Integration test using SrcDatapathTB for comprehensive validation."""

    @pytest.mark.miop
    @pytest.mark.source_datapath
    @pytest.mark.integration
    @pytest.mark.parametrize("test_level", ["basic", "medium", "full"])
    async def test_source_datapath_comprehensive(self, dut, test_level):
        """Comprehensive source data path test using framework TB class."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")  # 100MHz
        cocotb.start_soon(clock.start())

        # Initialize TB using framework class
        tb = SrcDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)

        # Initialize test environment
        await tb.initialize_test()

        # Reset sequence
        await tb.reset_sequence()

        # Test configuration based on level
        test_configs = {
            "basic": {
                "scheduler_requests": 32,
                "axi_reads": 32,
                "network_transmissions": 32,
                "multi_channel_ops": 16,
                "timing_profile": "fast"
            },
            "medium": {
                "scheduler_requests": 64,
                "axi_reads": 64,
                "network_transmissions": 64,
                "multi_channel_ops": 32,
                "timing_profile": "normal"
            },
            "full": {
                "scheduler_requests": 128,
                "axi_reads": 128,
                "network_transmissions": 128,
                "multi_channel_ops": 64,
                "timing_profile": "stress"
            }
        }

        config = test_configs[test_level]

        # Set timing profile based on test level
        tb.set_timing_profile(config["timing_profile"])

        # Test 1: Scheduler interface functionality across all 32 channels
        tb.log.info(f"=== Test 1: Scheduler Interface ({config['scheduler_requests']} requests across 32 channels) ===")
        success, stats = await tb.test_scheduler_interface(count=config['scheduler_requests'])
        assert success, f"Scheduler interface test failed: {stats}"
        tb.log.info(f"✅ Scheduler interface: {stats['success_rate']:.1%} success rate, {stats['channels_tested']} channels tested")

        # Test 2: AXI read operations
        tb.log.info(f"=== Test 2: AXI Read Operations ({config['axi_reads']} reads) ===")
        success, stats = await tb.test_axi_read_operations(count=config['axi_reads'])
        assert success, f"AXI read operations failed: {stats}"
        tb.log.info(f"✅ AXI reads: {stats['success_rate']:.1%} success rate, avg latency: {stats['average_latency']:.1f}")

        # Test 3: Network packet transmission
        tb.log.info(f"=== Test 3: Network Transmission ({config['network_transmissions']} packets) ===")
        success, stats = await tb.test_mnoc_transmission(count=config['network_transmissions'])
        assert success, f"Network transmission failed: {stats}"
        tb.log.info(f"✅ Network transmission: {stats['success_rate']:.1%} success rate, {stats['packets_received']} packets received")

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

        # Test 7: Stress test (if full level)
        if test_level == "full":
            tb.log.info(f"=== Test 7: Stress Test (100 mixed operations) ===")
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
        tb.log.info("=== COMPREHENSIVE SOURCE DATAPATH TEST RESULTS ===")
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
        tb.log.info(f"Scheduler Requests: {operations['scheduler_requests']}")
        tb.log.info(f"AXI Reads: {operations['axi_reads']}")
        tb.log.info(f"Network Transmissions: {operations['network_transmissions']}")

        # Performance metrics
        performance = final_stats['performance']
        tb.log.info(f"Average Latency: {performance['average_latency']:.1f}")
        tb.log.info(f"Peak Channels Active: {performance['peak_channels_active']}")
        tb.log.info(f"Requests/Second: {performance['requests_per_second']:.1f}")

        tb.log.info("✅ SOURCE DATAPATH INTEGRATION TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.source_datapath
    @pytest.mark.scalability
    async def test_32_channel_memory_layout(self, dut):
        """Test 32-channel memory layout and addressing."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = SrcDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)
        await tb.initialize_test()
        await tb.reset_sequence()

        # Verify 32-channel configuration
        assert tb.TEST_CHANNELS == 32, f"Expected 32 channels, got {tb.TEST_CHANNELS}"

        # Test memory layout for all 32 channels
        tb.log.info("=== Testing 32-Channel Memory Layout ===")

        for channel in range(32):
            base_addr = tb._get_channel_base_address(channel)
            expected_addr = tb.BASE_ADDRESS + (channel * tb.CHANNEL_OFFSET)
            assert base_addr == expected_addr, f"Channel {channel} address mismatch: got 0x{base_addr:08x}, expected 0x{expected_addr:08x}"

        # Test memory access patterns across all channels
        success, stats = await tb.test_scheduler_interface(count=64)  # 2 operations per channel
        assert success, f"Memory layout test failed: {stats}"
        assert stats['channels_tested'] == 32, f"Expected 32 channels tested, got {stats['channels_tested']}"

        tb.log.info("✅ 32-CHANNEL MEMORY LAYOUT TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.source_datapath
    @pytest.mark.framework
    async def test_framework_component_integration(self, dut):
        """Test proper integration with framework AXI4 and Network components."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = SrcDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)
        await tb.initialize_test()
        await tb.reset_sequence()

        # Verify framework component interfaces are properly created
        assert tb.axi_slave is not None, "AXI slave not created"
        assert tb.network_slave is not None, "Network slave not created"
        assert tb.memory_model is not None, "Memory model not created"

        # Verify Network compliance checker if enabled
        if tb.test_config['enable_compliance_check']:
            assert tb.network_compliance_checker is not None, "Network compliance checker not created"

        # Test framework component functionality
        tb.log.info("=== Testing Framework Component Integration ===")

        # Test AXI4 component integration
        success, stats = await tb.test_axi_read_operations(count=16)
        assert success, f"Framework AXI4 integration failed: {stats}"

        # Test Network component integration
        success, stats = await tb.test_mnoc_transmission(count=16)
        assert success, f"Framework Network integration failed: {stats}"

        tb.log.info("✅ FRAMEWORK COMPONENT INTEGRATION TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.source_datapath
    @pytest.mark.performance
    async def test_data_flow_performance(self, dut):
        """Test end-to-end data flow performance."""

        # Setup clock
        clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = SrcDatapathTB(dut, clk=dut.clk, rst_n=dut.rst_n)
        await tb.initialize_test()
        await tb.reset_sequence()

        # Set fast timing for performance test
        tb.set_timing_profile("fast")

        tb.log.info("=== Testing Data Flow Performance ===")

        # Run performance test sequence
        operations_per_test = 32

        # Measure scheduler interface performance
        success, scheduler_stats = await tb.test_scheduler_interface(count=operations_per_test)
        assert success, "Scheduler performance test failed"

        # Measure AXI read performance
        success, axi_stats = await tb.test_axi_read_operations(count=operations_per_test)
        assert success, "AXI performance test failed"

        # Measure Network transmission performance
        success, mnoc_stats = await tb.test_mnoc_transmission(count=operations_per_test)
        assert success, "Network performance test failed"

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
    print("RAPIDS Source Data Path Integration Test")
    print("This test uses SrcDatapathTB from the framework")
    print("Run with: pytest val/rapids/integration_tests/test_source_datapath_integration.py -v")