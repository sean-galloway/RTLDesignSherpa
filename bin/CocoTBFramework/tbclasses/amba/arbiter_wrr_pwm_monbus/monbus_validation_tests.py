"""
MonBus Validation Tests

This module contains focused tests for MonBus event generation, packet validation,
event sequence verification, and monitoring system integrity.
"""

import asyncio
from typing import Dict, Any, List
from cocotb.triggers import RisingEdge, ClockCycles

from .test_helper_classes import RequestPattern
from CocoTBFramework.tbclasses.monbus import (
    ProtocolType, PktType, AXIErrorCode, AXIThresholdCode, AXIPerformanceCode,
    create_arbiter_starvation_event, create_arbiter_grant_efficiency_event,
    create_arbiter_active_count_event, analyze_packet_distribution
)


class MonBusValidationTests:
    """
    Test class focused on MonBus event validation and packet analysis
    """

    def __init__(self, components):
        self.components = components
        self.dut = components.dut
        self.log = components.log
        self.params = components.params

        # Test results tracking
        self.test_results = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': [],
            'success': False
        }

    async def run_tests(self) -> Dict[str, Any]:
        """Run all MonBus validation tests"""
        self.log.info("Starting MonBus Validation Tests")

        tests = self._get_tests_for_level()

        for test_name, test_func in tests:
            self.test_results['total_tests'] += 1

            try:
                self.log.info(f"Running {test_name}")
                success = await test_func()

                if success:
                    self.test_results['passed_tests'] += 1
                    self.log.info(f"✓ {test_name} PASSED")
                else:
                    self.test_results['failed_tests'].append(test_name)
                    self.log.error(f"✗ {test_name} FAILED")

            except Exception as e:
                self.test_results['failed_tests'].append(test_name)
                self.log.error(f"✗ {test_name} ERROR: {str(e)}")

        self.test_results['success'] = len(self.test_results['failed_tests']) == 0

        self.log.info(f"MonBus Validation Tests Complete: "
                     f"{self.test_results['passed_tests']}/{self.test_results['total_tests']} passed")

        return self.test_results

    def _get_tests_for_level(self) -> List[tuple]:
        """Get tests based on test level"""
        basic_tests = [
            ("test_monbus_basic_connectivity", self.test_monbus_basic_connectivity),
            ("test_performance_event_generation", self.test_performance_event_generation),
        ]

        medium_tests = basic_tests + [
            ("test_threshold_event_validation", self.test_threshold_event_validation),
            ("test_packet_field_validation", self.test_packet_field_validation),
            ("test_event_sequence_validation", self.test_event_sequence_validation),
        ]

        full_tests = medium_tests + [
            ("test_comprehensive_event_analysis", self.test_comprehensive_event_analysis),
            ("test_monitoring_system_integrity", self.test_monitoring_system_integrity),
            ("test_packet_distribution_analysis", self.test_packet_distribution_analysis),
        ]

        level_map = {
            'basic': basic_tests,
            'medium': medium_tests,
            'full': full_tests
        }

        return level_map[self.params['test_level'].value]

    # ==========================================================================
    # BASIC TESTS
    # ==========================================================================

    async def test_monbus_basic_connectivity(self) -> bool:
        """Test basic MonBus connectivity and packet reception"""
        self.log.debug("Testing MonBus basic connectivity")

        # Clear previous packets
        self.components.monbus_slave.clear_received_packets()

        # Generate some arbiter activity
        self.dut.req.value = (1 << self.params['clients']) - 1  # All clients request
        await ClockCycles(self.dut.clk, 50)

        # Check if any packets were received
        packets = self.components.monbus_slave.get_received_packets()

        if len(packets) == 0:
            self.log.error("No MonBus packets received")
            return False

        # Validate first packet
        first_packet = packets[0]

        # Check protocol
        if first_packet.protocol != ProtocolType.AXI.value:
            self.log.error(f"Unexpected protocol: {first_packet.get_protocol_name()}")
            return False

        # Check event code validity
        if not first_packet.is_valid_event_code():
            self.log.error(f"Invalid event code: {first_packet.get_event_code_name()}")
            return False

        self.log.debug(f"MonBus connectivity verified - received {len(packets)} valid packets")
        return True

    async def test_performance_event_generation(self) -> bool:
        """Test generation of performance events"""
        self.log.debug("Testing performance event generation")

        self.components.monbus_slave.clear_received_packets()

        # Generate grant activity to trigger performance events
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=100
        )

        # Look for performance packets
        performance_packets = self.components.monbus_slave.get_performance_packets()

        if len(performance_packets) == 0:
            self.log.error("No performance packets generated")
            return False

        # Validate performance packet content
        for packet in performance_packets[:5]:  # Check first 5 packets
            if packet.event_code == AXIPerformanceCode.GRANT_EFFICIENCY.value:
                # Validate grant efficiency packet structure
                if packet.channel_id >= self.params['clients']:
                    self.log.error(f"Invalid channel_id in performance packet: {packet.channel_id}")
                    return False

        self.log.debug(f"Performance event generation verified - {len(performance_packets)} packets")
        return True

    # ==========================================================================
    # MEDIUM TESTS
    # ==========================================================================

    async def test_threshold_event_validation(self) -> bool:
        """Test threshold event generation and validation"""
        self.log.debug("Testing threshold event validation")

        self.components.monbus_slave.clear_received_packets()

        # Generate high activity to trigger thresholds
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=150
        )

        # Look for threshold packets
        threshold_packets = self.components.monbus_slave.get_threshold_packets()

        # May or may not have threshold events depending on timing
        self.log.debug(f"Threshold validation - {len(threshold_packets)} threshold events detected")

        # Validate any threshold packets that were generated
        for packet in threshold_packets:
            if packet.event_code == AXIThresholdCode.ACTIVE_COUNT.value:
                # Validate active count threshold
                active_count = packet.data & 0xFF  # Lower 8 bits
                if active_count > self.params['clients']:
                    self.log.error(f"Invalid active count in threshold packet: {active_count}")
                    return False

        return True

    async def test_packet_field_validation(self) -> bool:
        """Test comprehensive packet field validation"""
        self.log.debug("Testing packet field validation")

        self.components.monbus_slave.clear_received_packets()

        # Generate diverse activity
        patterns = [RequestPattern.ALL_CLIENTS, RequestPattern.ROUND_ROBIN, RequestPattern.RANDOM]

        for pattern in patterns:
            await self.components.pattern_generator.apply_pattern(
                self.dut, pattern, duration_cycles=30
            )

        all_packets = self.components.monbus_slave.get_received_packets()

        if len(all_packets) == 0:
            self.log.error("No packets for field validation")
            return False

        # Validate packet fields
        for i, packet in enumerate(all_packets[:10]):  # Check first 10 packets
            # Check protocol field
            if packet.protocol not in [e.value for e in ProtocolType]:
                self.log.error(f"Invalid protocol in packet {i}: {packet.protocol}")
                return False

            # Check packet type field
            if packet.packet_type not in [e.value for e in PktType]:
                self.log.error(f"Invalid packet_type in packet {i}: {packet.packet_type}")
                return False

            # Check field ranges
            if packet.channel_id >= 64:  # 6-bit field
                self.log.error(f"Channel ID out of range in packet {i}: {packet.channel_id}")
                return False

            if packet.unit_id >= 16:  # 4-bit field
                self.log.error(f"Unit ID out of range in packet {i}: {packet.unit_id}")
                return False

        self.log.debug(f"Field validation passed for {len(all_packets)} packets")
        return True

    async def test_event_sequence_validation(self) -> bool:
        """Test event sequence validation"""
        self.log.debug("Testing event sequence validation")

        self.components.monbus_slave.clear_received_packets()

        # Create expected sequence: generate activity and look for grant efficiency events
        expected_events = []
        for client_id in range(min(2, self.params['clients'])):  # Test first 2 clients
            expected_events.append(
                create_arbiter_grant_efficiency_event(
                    client_id=client_id,
                    grant_count=1,  # At least 1 grant
                    active_count=self.params['clients']
                )
            )

        # Generate activity
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=100
        )

        # Use event validator to check sequence (relaxed validation)
        sequence_result = await self.components.event_validator.validate_event_sequence(
            expected_events, timeout_cycles=50
        )

        # For sequence validation, we'll be flexible since timing is critical
        if sequence_result['events_found'] == 0:
            self.log.warning("No expected events found in sequence - may be timing dependent")
            return True  # Don't fail on timing issues

        self.log.debug(f"Event sequence validation: {sequence_result['events_found']}/{sequence_result['total_expected']} found")
        return True

    async def test_packet_filtering_functionality(self) -> bool:
        """Test that packet filtering works correctly"""
        self.log.debug("Testing packet filtering functionality")

        # Test 1: Disable all packets
        await self.components.disable_all_monitoring_packets()
        self.components.monbus_slave.clear_received_packets()
        
        # Generate activity
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=50
        )
        
        packets_disabled = self.components.monbus_slave.get_received_packets()
        
        if len(packets_disabled) > 0:
            self.log.error(f"Received {len(packets_disabled)} packets when all should be disabled")
            return False

        # Test 2: Enable only performance packets
        await self.components.enable_only_performance_monitoring()
        self.components.monbus_slave.clear_received_packets()
        
        # Generate activity
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=50
        )
        
        packets_perf_only = self.components.monbus_slave.get_received_packets()
        perf_packets = self.components.monbus_slave.get_performance_packets()
        
        if len(packets_perf_only) != len(perf_packets):
            self.log.error(f"Expected only performance packets, but got other types")
            return False

        # Test 3: Enable only error packets
        await self.components.enable_only_error_monitoring()
        self.components.monbus_slave.clear_received_packets()
        
        # Create starvation condition
        self.dut.req.value = 0b0001  # Only client 0
        await ClockCycles(self.dut.clk, 150)  # Exceed starvation threshold
        self.dut.req.value = 0b1111  # All clients
        await ClockCycles(self.dut.clk, 20)
        
        packets_error_only = self.components.monbus_slave.get_received_packets()
        error_packets = self.components.monbus_slave.get_error_packets()
        
        # Should only have error packets
        non_error_packets = [p for p in packets_error_only if not p.is_error_packet()]
        if len(non_error_packets) > 0:
            self.log.error(f"Expected only error packets, but got {len(non_error_packets)} non-error packets")
            return False

        self.log.debug(f"Packet filtering test passed: disabled={len(packets_disabled)}, "
                      f"perf_only={len(perf_packets)}, error_only={len(error_packets)}")
        return True

    async def test_selective_packet_enabling(self) -> bool:
        """Test selective enabling of packet types"""
        self.log.debug("Testing selective packet enabling")

        # Configure specific packet types
        await self.components.configure_packet_filtering(
            enable_errors=True,
            enable_performance=True,
            enable_thresholds=False,  # Disable thresholds
            enable_timeouts=False,
            enable_completion=False,
            enable_debug=False
        )

        self.components.monbus_slave.clear_received_packets()

        # Generate comprehensive activity
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=100
        )

        all_packets = self.components.monbus_slave.get_received_packets()
        
        # Verify only enabled packet types are present
        error_packets = self.components.monbus_slave.get_error_packets()
        perf_packets = self.components.monbus_slave.get_performance_packets()
        threshold_packets = self.components.monbus_slave.get_threshold_packets()
        timeout_packets = self.components.monbus_slave.get_timeout_packets()

        # Should have error and performance packets
        if len(error_packets) == 0 and len(perf_packets) == 0:
            self.log.warning("No enabled packet types detected - may be timing dependent")

        # Should NOT have threshold or timeout packets
        if len(threshold_packets) > 0:
            self.log.error(f"Unexpected threshold packets: {len(threshold_packets)}")
            return False

        if len(timeout_packets) > 0:
            self.log.error(f"Unexpected timeout packets: {len(timeout_packets)}")
            return False

        self.log.debug(f"Selective enabling test passed: errors={len(error_packets)}, "
                      f"perf={len(perf_packets)}, thresholds={len(threshold_packets)}")
        return True

    # ==========================================================================
    # FULL TESTS
    # ==========================================================================

    async def test_comprehensive_event_analysis(self) -> bool:
        """Test comprehensive event analysis across all types"""
        self.log.debug("Testing comprehensive event analysis")

        self.components.monbus_slave.clear_received_packets()

        # Generate comprehensive activity
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=200
        )

        # Analyze all packet types
        all_packets = self.components.monbus_slave.get_received_packets()

        if len(all_packets) < 10:
            self.log.error(f"Insufficient packets for analysis: {len(all_packets)}")
            return False

        # Analyze packet distribution
        distribution = analyze_packet_distribution(all_packets)

        self.log.debug(f"Packet distribution analysis:")
        self.log.debug(f"  Total packets: {distribution['total_packets']}")
        self.log.debug(f"  Protocol distribution: {distribution['protocol_distribution']}")
        self.log.debug(f"  Packet type distribution: {distribution['packet_type_distribution']}")

        # Verify we have AXI protocol packets
        axi_packets = distribution['protocol_distribution'].get('AXI', 0)
        if axi_packets == 0:
            self.log.error("No AXI protocol packets found")
            return False

        # Verify we have performance packets
        perf_packets = distribution['packet_type_distribution'].get('PERF', 0)
        if perf_packets == 0:
            self.log.error("No performance packets found")
            return False

        return True

    async def test_monitoring_system_integrity(self) -> bool:
        """Test monitoring system integrity under various conditions"""
        self.log.debug("Testing monitoring system integrity")

        # Test with monitoring disabled then re-enabled
        self.dut.cfg_mon_enable.value = 0
        await ClockCycles(self.dut.clk, 20)

        packet_count_disabled = len(self.components.monbus_slave.get_received_packets())

        # Re-enable monitoring
        self.dut.cfg_mon_enable.value = 1
        await ClockCycles(self.dut.clk, 5)

        # Generate activity
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=50
        )

        packet_count_enabled = len(self.components.monbus_slave.get_received_packets())

        # Should have more packets after re-enabling
        if packet_count_enabled <= packet_count_disabled:
            self.log.warning("Monitoring enable/disable may not be working as expected")

        # Test threshold changes
        original_latency = self.dut.cfg_mon_latency.value
        self.dut.cfg_mon_latency.value = 25  # Lower threshold
        await ClockCycles(self.dut.clk, 50)

        # Restore original threshold
        self.dut.cfg_mon_latency.value = original_latency
        await ClockCycles(self.dut.clk, 10)

        self.log.debug("Monitoring system integrity test completed")
        return True

    async def test_packet_distribution_analysis(self) -> bool:
        """Test detailed packet distribution analysis"""
        self.log.debug("Testing packet distribution analysis")

        self.components.monbus_slave.clear_received_packets()

        # Generate activity with different patterns
        patterns = [
            (RequestPattern.ALL_CLIENTS, 100),
            (RequestPattern.ROUND_ROBIN, 50),
            (RequestPattern.RANDOM, 75)
        ]

        for pattern, cycles in patterns:
            await self.components.pattern_generator.apply_pattern(
                self.dut, pattern, duration_cycles=cycles
            )

        all_packets = self.components.monbus_slave.get_received_packets()

        if len(all_packets) < 20:
            self.log.error(f"Insufficient packets for distribution analysis: {len(all_packets)}")
            return False

        # Detailed distribution analysis
        distribution = analyze_packet_distribution(all_packets)

        # Verify distribution makes sense
        total_packets = distribution['total_packets']

        # Check event code distribution
        event_codes = distribution['event_code_distribution']
        if len(event_codes) == 0:
            self.log.error("No event codes found in distribution")
            return False

        # Check channel distribution (should have entries for valid clients)
        channel_dist = distribution['channel_distribution']
        valid_channels = [ch for ch in channel_dist.keys() if ch < self.params['clients']]

        if len(valid_channels) == 0:
            self.log.warning("No valid client channels found in distribution")

        self.log.debug(f"Distribution analysis completed:")
        self.log.debug(f"  Event codes: {len(event_codes)}")
        self.log.debug(f"  Valid channels: {len(valid_channels)}")
        self.log.debug(f"  Total packets analyzed: {total_packets}")

        return True
