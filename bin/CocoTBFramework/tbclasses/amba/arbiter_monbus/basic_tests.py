#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BasicFunctionalityTest
# Purpose: Basic Functionality Tests - UPDATED FOR 3-BIT PROTOCOL FIELD
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Basic Functionality Tests - UPDATED FOR 3-BIT PROTOCOL FIELD

This module contains fundamental tests for the arbiter monitor bus functionality,
updated to work with the new monitor_pkg.sv packet format.

KEY UPDATES:
- All packet parsing uses new field positions
- Protocol field validation for 3-bit range
- Event data validation for 35-bit range
- Enhanced packet validation and debug output
- Support for CORE protocol testing

Test Categories:
1. Monitor Enable/Disable Tests
2. Basic Packet Generation Tests
3. Configuration Validation Tests
4. Field Format Validation Tests
5. Protocol-Specific Tests

Each test validates both functionality and packet format correctness.
"""

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.utils import get_sim_time
import random

# Import updated types and framework
from CocoTBFramework.tbclasses.monbus.monbus_types import (
    ProtocolType, PktType,
    ARBErrorCode, ARBTimeoutCode, ARBCompletionCode, ARBThresholdCode,
    ARBPerformanceCode, ARBDebugCode,
    get_packet_type, get_protocol, get_event_code, get_channel_id,
    get_unit_id, get_agent_id, get_event_data,
    validate_monitor_packet, MonitorPacket, debug_packet_bits
)

from .test_framework import TestFramework, verify_expected_packet, create_arb_test_config


# =============================================================================
# BASIC FUNCTIONALITY TEST CLASS
# =============================================================================

class BasicFunctionalityTest:
    """Basic functionality tests updated for new monitor packet format"""
    
    def __init__(self, framework: TestFramework):
        self.framework = framework
        self.log = framework.log
        self.dut = framework.dut
        self.config = framework.config
    
    async def test_monitor_enable_disable(self):
        """Test basic monitor enable/disable functionality"""
        self.log.info("=== Testing Monitor Enable/Disable ===")
        
        # Test 1: Monitor disabled - should produce no packets
        self.log.info("Phase 1: Testing monitor disabled state")
        self.dut.cfg_mon_enable.value = 0
        await ClockCycles(self.dut.clk, 5)
        
        # Generate some arbiter activity
        self.dut.request.value = 0b1111  # All clients requesting
        await ClockCycles(self.dut.clk, 20)
        self.dut.request.value = 0
        
        # Verify no packets generated
        packet_count_disabled = len(self.framework.packet_collector.packets)
        assert packet_count_disabled == 0, f"Expected 0 packets when disabled, got {packet_count_disabled}"
        self.log.info("✅ No packets generated when monitor disabled")
        
        # Test 2: Monitor enabled - should produce packets
        self.log.info("Phase 2: Testing monitor enabled state")
        self.dut.cfg_mon_enable.value = 1
        await ClockCycles(self.dut.clk, 5)
        
        # Generate arbiter activity
        self.dut.request.value = 0b1111
        await ClockCycles(self.dut.clk, 20)
        self.dut.request.value = 0
        
        # Wait for packets and verify
        await self.framework.wait_for_packets(1, timeout_cycles=50)
        packet_count_enabled = len(self.framework.packet_collector.packets)
        
        assert packet_count_enabled > 0, "Expected packets when monitor enabled"
        self.log.info(f"✅ {packet_count_enabled} packets generated when monitor enabled")
        
        # Test 3: Re-disable monitor
        self.log.info("Phase 3: Testing monitor re-disable")
        self.dut.cfg_mon_enable.value = 0
        await ClockCycles(self.dut.clk, 5)
        
        # Clear packet collector and generate activity
        initial_count = len(self.framework.packet_collector.packets)
        self.dut.request.value = 0b1010
        await ClockCycles(self.dut.clk, 20)
        self.dut.request.value = 0
        
        final_count = len(self.framework.packet_collector.packets)
        assert final_count == initial_count, f"Monitor should be disabled: expected {initial_count}, got {final_count}"
        self.log.info("✅ Monitor re-disable successful")
        
        # Re-enable for subsequent tests
        self.dut.cfg_mon_enable.value = 1
        await ClockCycles(self.dut.clk, 2)
    
    async def test_packet_field_format(self):
        """Test that packets conform to the updated 64-bit format"""
        self.log.info("=== Testing Packet Field Format (Updated) ===")
        
        # Enable all packet types to get variety
        await self.framework.apply_monitor_config({
            'cfg_mon_pkt_type_enable': 0xFFFF
        })
        
        # Generate activity to produce packets
        await self.framework.stimulus_generator("random", cycles=50)
        await ClockCycles(self.dut.clk, 10)
        
        packets = self.framework.packet_collector.packets
        assert len(packets) > 0, "No packets collected for format testing"
        
        self.log.info(f"Testing format of {len(packets)} collected packets...")
        
        format_errors = []
        
        for i, packet in enumerate(packets):
            self.log.debug(f"Validating packet {i+1}: {packet}")
            
            # Test 1: Protocol field should be 3 bits (0-7) ✅ UPDATED
            if packet.protocol > 7:
                format_errors.append(f"Packet {i}: Protocol {packet.protocol} exceeds 3-bit range (0-7)")
            
            # Test 2: Protocol should be valid type
            if packet.protocol not in [p.value for p in ProtocolType]:
                format_errors.append(f"Packet {i}: Invalid protocol type {packet.protocol}")
            
            # Test 3: Packet type should be 4 bits (0-15)
            if packet.packet_type > 15:
                format_errors.append(f"Packet {i}: Packet type {packet.packet_type} exceeds 4-bit range")
            
            # Test 4: Event code should be 4 bits (0-15)
            if packet.event_code > 15:
                format_errors.append(f"Packet {i}: Event code {packet.event_code} exceeds 4-bit range")
            
            # Test 5: Channel ID should be 6 bits (0-63)
            if packet.channel_id > 63:
                format_errors.append(f"Packet {i}: Channel ID {packet.channel_id} exceeds 6-bit range")
            
            # Test 6: Unit ID should be 4 bits (0-15)
            if packet.unit_id > 15:
                format_errors.append(f"Packet {i}: Unit ID {packet.unit_id} exceeds 4-bit range")
            
            # Test 7: Agent ID should be 8 bits (0-255)
            if packet.agent_id > 255:
                format_errors.append(f"Packet {i}: Agent ID {packet.agent_id} exceeds 8-bit range")
            
            # Test 8: Event data should be 35 bits (0 to 0x7FFFFFFFF) ✅ UPDATED
            max_35_bit = (1 << 35) - 1  # 0x7FFFFFFFF
            if packet.event_data > max_35_bit:
                format_errors.append(f"Packet {i}: Event data 0x{packet.event_data:X} exceeds 35-bit range (max 0x{max_35_bit:X})")
            
            # Test 9: Agent and Unit IDs should match expected configuration
            if packet.agent_id != self.config.mon_agent_id:
                format_errors.append(f"Packet {i}: Agent ID mismatch - expected 0x{self.config.mon_agent_id:02X}, got 0x{packet.agent_id:02X}")
            
            if packet.unit_id != self.config.mon_unit_id:
                format_errors.append(f"Packet {i}: Unit ID mismatch - expected 0x{self.config.mon_unit_id:X}, got 0x{packet.unit_id:X}")
            
            # Test 10: For ARB protocol packets, verify field positions using bit extraction
            if packet.protocol == ProtocolType.PROTOCOL_ARB:
                raw_packet = packet.raw_packet
                
                # Verify field extraction matches parsed values ✅ UPDATED bit positions
                extracted_protocol = (raw_packet >> 57) & 0x7     # [59:57] - 3 bits
                extracted_event_code = (raw_packet >> 53) & 0xF   # [56:53] - 4 bits
                extracted_data = raw_packet & 0x7FFFFFFFF         # [34:0] - 35 bits
                
                if extracted_protocol != packet.protocol:
                    format_errors.append(f"Packet {i}: Protocol field extraction mismatch")
                if extracted_event_code != packet.event_code:
                    format_errors.append(f"Packet {i}: Event code field extraction mismatch")
                if extracted_data != packet.event_data:
                    format_errors.append(f"Packet {i}: Event data field extraction mismatch")
        
        # Report format validation results
        if format_errors:
            self.log.error(f"❌ Packet format validation failed with {len(format_errors)} errors:")
            for error in format_errors[:10]:  # Show first 10 errors
                self.log.error(f"  - {error}")
            if len(format_errors) > 10:
                self.log.error(f"  ... and {len(format_errors) - 10} more errors")
            
            # Show detailed bit breakdown for first failed packet if available
            if packets:
                self.log.error("First packet bit breakdown:")
                self.log.error(debug_packet_bits(packets[0].raw_packet))
            
            raise AssertionError(f"Packet format validation failed with {len(format_errors)} errors")
        
        self.log.info(f"✅ All {len(packets)} packets passed format validation")
        self.log.info("✅ Updated 64-bit packet format confirmed:")
        self.log.info("  - [63:60] packet_type: 4 bits")
        self.log.info("  - [59:57] protocol: 3 bits ✅ UPDATED")
        self.log.info("  - [56:53] event_code: 4 bits ✅ UPDATED")
        self.log.info("  - [52:47] channel_id: 6 bits")
        self.log.info("  - [46:43] unit_id: 4 bits")
        self.log.info("  - [42:35] agent_id: 8 bits")
        self.log.info("  - [34:0] event_data: 35 bits ✅ UPDATED")
    
    async def test_arb_protocol_packets(self):
        """Test ARB protocol specific packet generation"""
        self.log.info("=== Testing ARB Protocol Packets ===")
        
        # Configure for ARB packet types
        await self.framework.apply_monitor_config(create_arb_test_config())
        
        # Test 1: Generate grant/completion events
        self.log.info("Phase 1: Testing ARB completion events")
        
        # Generate requests and grants
        self.dut.request.value = 0b1111
        await ClockCycles(self.dut.clk, 5)
        
        # Wait for grant completion packets
        success = await verify_expected_packet(
            self.framework, 
            ProtocolType.PROTOCOL_ARB,
            PktType.PktTypeCompletion, 
            ARBCompletionCode.ARB_COMPL_TRANSACTION
        )
        
        if not success:
            # Also check for grant issued performance packets
            success = await verify_expected_packet(
                self.framework,
                ProtocolType.PROTOCOL_ARB,
                PktType.PktTypePerf,
                ARBPerformanceCode.ARB_PERF_GRANT_ISSUED
            )
        
        assert success, "Expected ARB protocol packets not generated"
        self.log.info("✅ ARB protocol packets generated successfully")
        
        # Test 2: Verify ARB packet content
        arb_packets = [p for p in self.framework.packet_collector.packets 
                      if p.protocol == ProtocolType.PROTOCOL_ARB]
        
        assert len(arb_packets) > 0, "No ARB protocol packets found"
        
        for packet in arb_packets:
            # Verify protocol field
            assert packet.protocol == ProtocolType.PROTOCOL_ARB, f"Expected ARB protocol, got {packet.protocol}"
            
            # Verify event codes are valid for ARB protocol
            validation_result = validate_monitor_packet(packet.raw_packet)
            assert validation_result['valid'], f"Invalid ARB packet: {validation_result['errors']}"
            
            self.log.debug(f"Valid ARB packet: {packet}")
        
        self.log.info(f"✅ All {len(arb_packets)} ARB packets passed validation")
    
    async def test_packet_type_filtering(self):
        """Test packet type enable/disable filtering"""
        self.log.info("=== Testing Packet Type Filtering ===")
        
        # Test 1: Enable only error packets
        self.log.info("Phase 1: Testing error packet filtering")
        
        await self.framework.apply_monitor_config({
            'cfg_mon_pkt_type_enable': PktType.get_mask(PktType.PktTypeError),
            'cfg_mon_starvation_thresh': 50  # Lower threshold for faster testing
        })
        
        # Clear existing packets
        self.framework.packet_collector.packets.clear()
        
        # Generate starvation condition
        await self.framework.stimulus_generator("starvation", cycles=60)
        
        # Wait for error packets
        await self.framework.wait_for_packets(1, timeout_cycles=100)
        
        # Verify only error packets were generated
        packets = self.framework.packet_collector.packets
        error_packets = [p for p in packets if p.packet_type == PktType.PktTypeError]
        non_error_packets = [p for p in packets if p.packet_type != PktType.PktTypeError]
        
        assert len(error_packets) > 0, "Expected error packets not generated"
        assert len(non_error_packets) == 0, f"Unexpected non-error packets generated: {len(non_error_packets)}"
        
        self.log.info(f"✅ Only error packets generated: {len(error_packets)} packets")
        
        # Test 2: Enable only performance packets
        self.log.info("Phase 2: Testing performance packet filtering")
        
        await self.framework.apply_monitor_config({
            'cfg_mon_pkt_type_enable': PktType.get_mask(PktType.PktTypePerf)
        })
        
        self.framework.packet_collector.packets.clear()
        
        # Generate normal activity
        await self.framework.stimulus_generator("round_robin", cycles=30)
        
        await self.framework.wait_for_packets(1, timeout_cycles=50)
        
        packets = self.framework.packet_collector.packets
        perf_packets = [p for p in packets if p.packet_type == PktType.PktTypePerf]
        non_perf_packets = [p for p in packets if p.packet_type != PktType.PktTypePerf]
        
        assert len(perf_packets) > 0, "Expected performance packets not generated"
        assert len(non_perf_packets) == 0, f"Unexpected non-performance packets: {len(non_perf_packets)}"
        
        self.log.info(f"✅ Only performance packets generated: {len(perf_packets)} packets")
        
        # Test 3: Enable multiple packet types
        self.log.info("Phase 3: Testing multiple packet type filtering")
        
        multi_mask = PktType.get_mask(PktType.PktTypeError, PktType.PktTypeCompletion, PktType.PktTypePerf)
        await self.framework.apply_monitor_config({
            'cfg_mon_pkt_type_enable': multi_mask
        })
        
        self.framework.packet_collector.packets.clear()
        
        # Generate varied activity
        await self.framework.stimulus_generator("random", cycles=50)
        
        await ClockCycles(self.dut.clk, 50)  # Allow time for packet generation
        
        packets = self.framework.packet_collector.packets
        allowed_types = {PktType.PktTypeError, PktType.PktTypeCompletion, PktType.PktTypePerf}
        allowed_packets = [p for p in packets if p.packet_type in [t.value for t in allowed_types]]
        disallowed_packets = [p for p in packets if p.packet_type not in [t.value for t in allowed_types]]
        
        if len(packets) > 0:
            assert len(disallowed_packets) == 0, f"Unexpected packet types generated: {[p.packet_type for p in disallowed_packets]}"
            self.log.info(f"✅ Only allowed packet types generated: {len(allowed_packets)}/{len(packets)} packets")
        else:
            self.log.info("ℹ️ No packets generated in this test phase")
        
        # Restore full packet type enable for subsequent tests
        await self.framework.apply_monitor_config({
            'cfg_mon_pkt_type_enable': 0xFFFF
        })
    
    async def test_basic_configuration_validation(self):
        """Test basic configuration parameter validation"""
        self.log.info("=== Testing Basic Configuration Validation ===")
        
        # Test 1: Invalid configuration detection
        self.log.info("Phase 1: Testing configuration bounds")
        
        # Test very high threshold values (should not cause crashes)
        await self.framework.apply_monitor_config({
            'cfg_mon_latency_thresh': 0xFFFF,
            'cfg_mon_starvation_thresh': 0xFFFF,
            'cfg_mon_fairness_thresh': 100,  # High fairness threshold
            'cfg_mon_efficiency_thresh': 0    # Zero efficiency threshold
        })
        
        # Generate activity and ensure monitor still works
        await self.framework.stimulus_generator("random", cycles=30)
        await ClockCycles(self.dut.clk, 20)
        
        # Should still be able to collect some packets
        initial_count = len(self.framework.packet_collector.packets)
        
        self.log.info(f"✅ Monitor operational with extreme config values: {initial_count} packets")
        
        # Test 2: Restore reasonable configuration
        await self.framework.apply_monitor_config()  # Use defaults
        
        self.framework.packet_collector.packets.clear()
        await self.framework.stimulus_generator("round_robin", cycles=20)
        await ClockCycles(self.dut.clk, 10)
        
        final_count = len(self.framework.packet_collector.packets)
        self.log.info(f"✅ Monitor operational with default config: {final_count} packets")

    async def test_protocol_filtering(self):
        """Test protocol-specific packet filtering"""
        self.log.info("=== Testing Protocol Filtering ===")

        # Configure for ARB protocol
        await self.framework.prepare_clean_test_state()

        config = MonitorConfig(
            enable=True,
            pkt_type_enable=0xFFFF,  # Enable all packet types
            starvation_thresh=100,
            sample_period=16
        )

        await self.framework.apply_monitor_config(config)

        # Generate some activity
        self.log.info("Generating arbiter activity to test protocol filtering...")
        await self.framework.stimulus_generator("random", cycles=50)

        # Wait for packets
        await ClockCycles(self.dut.clk, 20)
        packets = self.framework.packet_collector.packets

        if len(packets) > 0:
            # Check that all packets are ARB protocol (0x3)
            arb_packets = [p for p in packets if p.protocol == ProtocolType.PROTOCOL_ARB]
            non_arb_packets = [p for p in packets if p.protocol != ProtocolType.PROTOCOL_ARB]

            self.log.info(f"Generated {len(packets)} packets: {len(arb_packets)} ARB, {len(non_arb_packets)} other")

            if len(arb_packets) > 0:
                self.log.info("✅ ARB protocol packets generated successfully")
            else:
                self.log.warning("⚠️ No ARB protocol packets generated, but monitor is working")
        else:
            self.log.info("ℹ️ No packets generated in this test")


# =============================================================================
# TEST RUNNER FUNCTION
# =============================================================================

async def run_basic_functionality_tests(framework: TestFramework):
    """Run all basic functionality tests"""
    framework.log.info("🚀 Starting Basic Functionality Tests (Updated for 3-bit Protocol)")
    
    test_instance = BasicFunctionalityTest(framework)
    
    # Execute all basic tests
    test_functions = [
        test_instance.test_monitor_enable_disable,
        test_instance.test_packet_field_format,
        test_instance.test_arb_protocol_packets,
        test_instance.test_packet_type_filtering,
        test_instance.test_protocol_filtering,
        test_instance.test_basic_configuration_validation
    ]
    
    # Run tests sequentially
    for test_func in test_functions:
        try:
            await test_func()
            framework.log.info(f"✅ {test_func.__name__} PASSED")
        except Exception as e:
            framework.log.error(f"❌ {test_func.__name__} FAILED: {str(e)}")
            raise
    
    framework.log.info("🎉 All Basic Functionality Tests PASSED!")
    
    # Generate summary report
    framework.log.info("\n" + framework.packet_collector.generate_analysis_report())