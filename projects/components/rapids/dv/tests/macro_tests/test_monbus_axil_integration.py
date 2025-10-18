# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TestMonbusAxilIntegration
# Purpose: RAPIDS MonBus AXI-Lite Group Integration Test - v1.0
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS MonBus AXI-Lite Group Integration Test - v1.0

Integration test that leverages the existing MonbusAxilGroupTB from the framework
to provide comprehensive monitor bus aggregation and AXI-Lite interface validation
following the user's guidance:

- Uses MonbusAxilGroupTB from bin/CocoTBFramework/tbclasses/rapids/monbus_axil_group_tb.py
- Leverages real AXIL4/GAXI/MonBus component integration
- Tests monitor bus packet filtering and routing
- Tests AXI-Lite slave/master interface functionality
- Provides superset testing capability at unit level

This provides comprehensive testing of the monitor bus aggregation macro block.
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
from tbclasses.monbus_axil_group_tb import MonbusAxilGroupTB


class TestMonbusAxilIntegration:
    """Integration test using MonbusAxilGroupTB for comprehensive validation."""

    @pytest.mark.miop
    @pytest.mark.monbus
    @pytest.mark.integration
    @pytest.mark.parametrize("test_level", ["basic", "medium", "full"])
    async def test_monbus_axil_comprehensive(self, dut, test_level):
        """Comprehensive MonBus AXI-Lite test using framework TB class."""

        # Setup clock
        clock = Clock(dut.axi_aclk, 10, units="ns")  # 100MHz
        cocotb.start_soon(clock.start())

        # Initialize TB using framework class
        tb = MonbusAxilGroupTB(dut, axi_aclk=dut.axi_aclk, axi_aresetn=dut.axi_aresetn)

        # Initialize test environment
        await tb.initialize_test()

        # Reset sequence
        dut.axi_aresetn.value = 0
        await RisingEdge(dut.axi_aclk)
        await Timer(50, units="ns")
        dut.axi_aresetn.value = 1
        await Timer(50, units="ns")

        # Test configuration based on level
        test_configs = {
            "basic": {
                "source_packets": 32,
                "sink_packets": 32,
                "protocol_tests": 16,
                "fifo_operations": 16,
                "config_operations": 8,
                "timing_profile": "fast"
            },
            "medium": {
                "source_packets": 64,
                "sink_packets": 64,
                "protocol_tests": 32,
                "fifo_operations": 32,
                "config_operations": 16,
                "timing_profile": "normal"
            },
            "full": {
                "source_packets": 128,
                "sink_packets": 128,
                "protocol_tests": 64,
                "fifo_operations": 64,
                "config_operations": 32,
                "timing_profile": "stress"
            }
        }

        config = test_configs[test_level]

        # Set timing profile based on test level
        tb.set_timing_profile(config["timing_profile"])

        # Test 1: Source monitor bus packet injection
        tb.log.info(f"=== Test 1: Source Monitor Bus Packets ({config['source_packets']} packets) ===")
        success, stats = await tb.test_source_monitor_packets(count=config['source_packets'])
        assert success, f"Source monitor packet test failed: {stats}"
        tb.log.info(f"✅ Source packets: {stats['success_rate']:.1%} success rate, {stats['packets_filtered']} filtered")

        # Test 2: Sink monitor bus packet injection
        tb.log.info(f"=== Test 2: Sink Monitor Bus Packets ({config['sink_packets']} packets) ===")
        success, stats = await tb.test_sink_monitor_packets(count=config['sink_packets'])
        assert success, f"Sink monitor packet test failed: {stats}"
        tb.log.info(f"✅ Sink packets: {stats['success_rate']:.1%} success rate, {stats['packets_filtered']} filtered")

        # Test 3: Protocol-specific filtering (AXI, Network, ARB)
        tb.log.info(f"=== Test 3: Protocol Filtering ({config['protocol_tests']} per protocol) ===")
        success, stats = await tb.test_protocol_filtering(count=config['protocol_tests'])
        assert success, f"Protocol filtering test failed: {stats}"
        tb.log.info(f"✅ Protocol filtering: AXI={stats['axi_filtered']}, Network={stats['network_filtered']}, ARB={stats['arb_filtered']}")

        # Test 4: Error/Interrupt FIFO operations (AXI-Lite slave read)
        tb.log.info(f"=== Test 4: Error/Interrupt FIFO ({config['fifo_operations']} operations) ===")
        success, stats = await tb.test_error_interrupt_fifo(count=config['fifo_operations'])
        assert success, f"Error/Interrupt FIFO test failed: {stats}"
        tb.log.info(f"✅ Error FIFO: {stats['reads_completed']} reads, {stats['interrupts_processed']} interrupts")

        # Test 5: Master write FIFO operations (AXI-Lite master write)
        tb.log.info(f"=== Test 5: Master Write FIFO ({config['fifo_operations']} operations) ===")
        success, stats = await tb.test_master_write_fifo(count=config['fifo_operations'])
        assert success, f"Master write FIFO test failed: {stats}"
        tb.log.info(f"✅ Master FIFO: {stats['writes_completed']} writes, {stats['master_transactions']} transactions")

        # Test 6: Configuration register operations
        tb.log.info(f"=== Test 6: Configuration Registers ({config['config_operations']} operations) ===")
        success, stats = await tb.test_configuration_registers(count=config['config_operations'])
        assert success, f"Configuration register test failed: {stats}"
        tb.log.info(f"✅ Config registers: {stats['reads']} reads, {stats['writes']} writes")

        # Test 7: Multi-protocol packet arbitration
        tb.log.info(f"=== Test 7: Multi-Protocol Arbitration ===")
        success, stats = await tb.test_multi_protocol_arbitration()
        assert success, f"Multi-protocol arbitration failed: {stats}"
        tb.log.info(f"✅ Arbitration: {stats['total_protocols_tested']} protocols, {stats['arbitration_fairness']:.1%} fairness")

        # Test 8: Stress test (if full level)
        if test_level == "full":
            tb.log.info(f"=== Test 8: Stress Test (concurrent operations) ===")
            success, stats = await tb.stress_test(count=100)
            # Stress test allows some failures
            assert stats['success_rate'] > 0.9, f"Stress test failed: {stats['success_rate']:.1%} success rate too low"
            tb.log.info(f"✅ Stress test: {stats['success_rate']:.1%} success rate")

        # Finalize test and get comprehensive statistics
        tb.finalize_test()
        final_stats = tb.get_test_stats()

        # Validate overall test performance
        assert final_stats['summary']['total_operations'] > 0, "No operations recorded"
        assert final_stats['summary']['successful_operations'] > 0, "No successful operations recorded"

        # Log comprehensive results
        tb.log.info("=== COMPREHENSIVE MONBUS AXIL TEST RESULTS ===")
        tb.log.info(f"Test Level: {test_level}")
        tb.log.info(f"Total Operations: {final_stats['summary']['total_operations']}")
        tb.log.info(f"Successful Operations: {final_stats['summary']['successful_operations']}")
        tb.log.info(f"Failed Operations: {final_stats['summary']['failed_operations']}")
        tb.log.info(f"Test Duration: {final_stats['summary']['test_duration']:.2f}s")

        # Packet statistics
        packets = final_stats['packets']
        tb.log.info(f"Source Packets Sent: {packets['source_sent']}")
        tb.log.info(f"Sink Packets Sent: {packets['sink_sent']}")
        tb.log.info(f"Packets Filtered: {packets['filtered_total']}")
        tb.log.info(f"Error FIFO Packets: {packets['to_err_fifo']}")
        tb.log.info(f"Write FIFO Packets: {packets['to_write_fifo']}")

        # Protocol breakdown
        protocols = final_stats['protocols']
        tb.log.info(f"AXI Protocol Packets: {protocols['axi']}")
        tb.log.info(f"Network Protocol Packets: {protocols['mnoc']}")
        tb.log.info(f"ARB Protocol Packets: {protocols['arb']}")

        # AXI-Lite interface statistics
        axil = final_stats['axil_interfaces']
        tb.log.info(f"Error FIFO Reads: {axil['error_fifo_reads']}")
        tb.log.info(f"Master Writes: {axil['master_writes']}")
        tb.log.info(f"Config Operations: {axil['config_operations']}")

        tb.log.info("✅ MONBUS AXIL INTEGRATION TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.monbus
    @pytest.mark.filtering
    async def test_packet_filtering_validation(self, dut):
        """Test comprehensive packet filtering and routing validation."""

        # Setup clock
        clock = Clock(dut.axi_aclk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = MonbusAxilGroupTB(dut, axi_aclk=dut.axi_aclk, axi_aresetn=dut.axi_aresetn)
        await tb.initialize_test()

        # Reset sequence
        dut.axi_aresetn.value = 0
        await RisingEdge(dut.axi_aclk)
        await Timer(50, units="ns")
        dut.axi_aresetn.value = 1
        await Timer(50, units="ns")

        tb.log.info("=== Testing Packet Filtering Validation ===")

        # Test specific protocol filtering rules
        protocols_to_test = ["AXI", "Network", "ARB"]

        for protocol in protocols_to_test:
            tb.log.info(f"--- Testing {protocol} Protocol Filtering ---")
            success, stats = await tb.test_specific_protocol_filtering(protocol, count=32)
            assert success, f"{protocol} filtering test failed: {stats}"
            tb.log.info(f"✅ {protocol}: {stats['filtered_correctly']} correctly filtered, {stats['error_packets']} error packets")

        # Test packet type routing
        success, stats = await tb.test_packet_type_routing()
        assert success, f"Packet type routing failed: {stats}"

        # Test filter configuration
        success, stats = await tb.test_filter_configuration()
        assert success, f"Filter configuration failed: {stats}"

        tb.log.info("✅ PACKET FILTERING VALIDATION TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.monbus
    @pytest.mark.framework
    async def test_framework_component_integration(self, dut):
        """Test proper integration with framework AXIL4 and GAXI components."""

        # Setup clock
        clock = Clock(dut.axi_aclk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = MonbusAxilGroupTB(dut, axi_aclk=dut.axi_aclk, axi_aresetn=dut.axi_aresetn)
        await tb.initialize_test()

        # Reset sequence
        dut.axi_aresetn.value = 0
        await RisingEdge(dut.axi_aclk)
        await Timer(50, units="ns")
        dut.axi_aresetn.value = 1
        await Timer(50, units="ns")

        # Verify framework component interfaces are properly created
        assert tb.axil_slave_rd is not None, "AXI-Lite slave read not created"
        assert tb.axil_master_wr is not None, "AXI-Lite master write not created"
        assert tb.monitor_source_master is not None, "Monitor source master not created"
        assert tb.monitor_sink_master is not None, "Monitor sink master not created"

        # Verify compliance checkers if enabled
        if tb.test_config['enable_compliance_check']:
            assert tb.axil_compliance_checker is not None, "AXIL compliance checker not created"
            assert tb.monbus_compliance_checker is not None, "MonBus compliance checker not created"

        # Test framework component functionality
        tb.log.info("=== Testing Framework Component Integration ===")

        # Test AXIL4 component integration
        success, stats = await tb.test_axil_framework_integration(count=16)
        assert success, f"Framework AXIL4 integration failed: {stats}"

        # Test GAXI component integration for monitor bus
        success, stats = await tb.test_gaxi_framework_integration(count=16)
        assert success, f"Framework GAXI integration failed: {stats}"

        # Test MonBus component integration
        success, stats = await tb.test_monbus_framework_integration(count=16)
        assert success, f"Framework MonBus integration failed: {stats}"

        tb.log.info("✅ FRAMEWORK COMPONENT INTEGRATION TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.monbus
    @pytest.mark.performance
    async def test_monitor_aggregation_performance(self, dut):
        """Test monitor bus aggregation performance with concurrent streams."""

        # Setup clock
        clock = Clock(dut.axi_aclk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = MonbusAxilGroupTB(dut, axi_aclk=dut.axi_aclk, axi_aresetn=dut.axi_aresetn)
        await tb.initialize_test()

        # Reset sequence
        dut.axi_aresetn.value = 0
        await RisingEdge(dut.axi_aclk)
        await Timer(50, units="ns")
        dut.axi_aresetn.value = 1
        await Timer(50, units="ns")

        # Set fast timing for performance test
        tb.set_timing_profile("fast")

        tb.log.info("=== Testing Monitor Aggregation Performance ===")

        # Test concurrent source and sink packet streams
        success, stats = await tb.test_concurrent_packet_streams(
            source_count=64, sink_count=64, concurrent_streams=4
        )
        assert success, f"Concurrent streams test failed: {stats}"

        # Test packet throughput
        success, stats = await tb.test_packet_throughput(packets_per_second_target=10000)
        assert success, f"Packet throughput test failed: {stats}"

        # Test FIFO performance under load
        success, stats = await tb.test_fifo_performance_under_load()
        assert success, f"FIFO performance test failed: {stats}"

        # Get final performance statistics
        tb.finalize_test()
        final_stats = tb.get_test_stats()

        # Validate performance metrics
        assert final_stats['performance']['packets_per_second'] > 5000, f"Performance too low: {final_stats['performance']['packets_per_second']:.1f} packets/sec"

        tb.log.info(f"✅ Performance Test: {final_stats['performance']['packets_per_second']:.1f} packets/second")
        tb.log.info("✅ MONITOR AGGREGATION PERFORMANCE TEST PASSED")

    @pytest.mark.miop
    @pytest.mark.monbus
    @pytest.mark.error_handling
    async def test_error_injection_and_handling(self, dut):
        """Test error injection and handling capabilities."""

        # Setup clock
        clock = Clock(dut.axi_aclk, 10, units="ns")
        cocotb.start_soon(clock.start())

        # Initialize TB
        tb = MonbusAxilGroupTB(dut, axi_aclk=dut.axi_aclk, axi_aresetn=dut.axi_aresetn)
        await tb.initialize_test()

        # Reset sequence
        dut.axi_aresetn.value = 0
        await RisingEdge(dut.axi_aclk)
        await Timer(50, units="ns")
        dut.axi_aresetn.value = 1
        await Timer(50, units="ns")

        tb.log.info("=== Testing Error Injection and Handling ===")

        # Test invalid packet injection
        success, stats = await tb.test_invalid_packet_handling()
        assert success, f"Invalid packet handling failed: {stats}"

        # Test FIFO overflow scenarios
        success, stats = await tb.test_fifo_overflow_handling()
        assert success, f"FIFO overflow handling failed: {stats}"

        # Test AXI-Lite error responses
        success, stats = await tb.test_axil_error_responses()
        assert success, f"AXIL error response handling failed: {stats}"

        # Test protocol violation handling
        success, stats = await tb.test_protocol_violation_handling()
        assert success, f"Protocol violation handling failed: {stats}"

        tb.log.info("✅ ERROR INJECTION AND HANDLING TEST PASSED")


# Pytest fixtures for test configuration
@pytest.fixture
def dut():
    """Mock DUT fixture - in real testing this would be the actual DUT."""
    # This is a placeholder - in actual testing, cocotb provides the DUT
    pass


if __name__ == "__main__":
    # For direct execution during development
    print("RAPIDS MonBus AXI-Lite Group Integration Test")
    print("This test uses MonbusAxilGroupTB from the framework")
    print("Run with: pytest val/rapids/integration_tests/test_monbus_axil_integration.py -v")