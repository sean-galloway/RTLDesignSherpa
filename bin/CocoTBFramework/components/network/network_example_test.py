# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MNOCExampleTest
# Purpose: Network Example Test
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Network Example Test

Demonstrates usage of the Network master and slave collateral following
the same patterns as AXIL4 examples. Shows how to create interfaces,
send various packet types, and validate compliance.

This example shows:
- Creating Network master and slave interfaces
- Sending different packet types (CONFIG, TS, RDA, RAW)
- Using v2.0 chunk_enables features
- EOS (End of Stream) handling
- Credit management and flow control
- Compliance checking and reporting
- Complete system testing

Usage:
    # Run with compliance checking enabled
    export NETWORK_COMPLIANCE_CHECK=1
    python -m pytest network_example_test.py -v
"""

import random
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock

# Import Network framework components
from CocoTBFramework.components.network.network_factories import (
    create_network_master, create_network_slave, create_network_system,
    create_network_test_environment, send_packet_sequence, validate_network_packet
)
from CocoTBFramework.components.network.network_interfaces import NETWORK_PKT_TYPES, NETWORK_ACK_TYPES
from CocoTBFramework.components.network.network_packet import MNOCPacket
from CocoTBFramework.components.network.network_field_configs import MNOCFieldConfigHelper


class MNOCExampleTest:
    """
    Example testbench showing Network master/slave usage patterns.

    Demonstrates the complete Network collateral API following the same
    patterns established by AXIL4 example tests.
    """

    def __init__(self, dut):
        """Initialize test environment."""
        self.dut = dut
        self.log = cocotb.logging.getLogger("network_test")

        # Clock setup
        self.clock_period = 10  # 100MHz
        cocotb.start_soon(Clock(dut.clk, self.clock_period, units="ns").start())

        # Test configuration
        self.config = {
            'data_width': 512,
            'addr_width': 8,
            'num_channels': 32,
            'initial_credits': 4,
            'timeout_cycles': 1000,
            'auto_ack': True,
        }

        # Create Network system
        self.network_system = None
        self.test_packets = []
        self.received_packets = []

    async def setup(self):
        """Setup test environment."""
        self.log.info("Setting up Network test environment...")

        # Reset DUT
        self.dut.rst_n.value = 0
        await RisingEdge(self.dut.clk)
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)

        # Create Network test environment
        self.network_system = create_network_test_environment(
            self.dut, self.dut.clk, log=self.log, **self.config
        )

        self.log.info("Network test environment ready")

    async def test_basic_packet_transmission(self):
        """Test basic packet transmission across all types."""
        self.log.info("=== Testing Basic Packet Transmission ===")

        # Test CONFIG packet
        await self._test_config_packet()

        # Test TruStream packet
        await self._test_ts_packet()

        # Test RDA packet
        await self._test_rda_packet()

        # Test RAW packet
        await self._test_raw_packet()

    async def _test_config_packet(self):
        """Test CONFIG packet transmission."""
        self.log.info("Testing CONFIG packet...")

        # Create CONFIG packet data
        config_data = [0x12345678, 0xABCDEF00, 0x55555555]
        channel = 1
        chunk_enables = 0x0007  # Only first 3 chunks valid

        # Send CONFIG packet
        await self.network_system['send_config'](channel, config_data, chunk_enables)

        # Wait for reception
        packet = await self.network_system['receive_packet'](timeout_cycles=100)

        # Validate received packet
        assert packet.get_payload_type() == NETWORK_PKT_TYPES.CONFIG_PKT
        assert packet.get_channel() == channel
        assert packet.get_chunk_enables() == chunk_enables

        # Validate data fields
        received_data = packet.get_data_fields()[:3]  # First 3 fields
        assert received_data == config_data

        self.log.info("CONFIG packet test passed")

    async def _test_ts_packet(self):
        """Test TruStream packet transmission."""
        self.log.info("Testing TruStream packet...")

        # Create TS packet with EOS
        ts_data = list(range(10))  # 10 data values
        channel = 5
        chunk_enables = 0x03FF  # First 10 chunks valid
        eos = True

        # Send TS packet with EOS
        await self.network_system['send_ts'](channel, ts_data, chunk_enables, eos)

        # Wait for reception
        packet = await self.network_system['receive_packet'](timeout_cycles=100)

        # Validate received packet
        assert packet.get_payload_type() == NETWORK_PKT_TYPES.TS_PKT
        assert packet.get_channel() == channel
        assert packet.get_chunk_enables() == chunk_enables
        assert packet.get_eos() == eos

        # Validate data fields
        received_data = packet.get_data_fields()[:10]
        assert received_data == ts_data

        self.log.info("TruStream packet test passed")

    async def _test_rda_packet(self):
        """Test RDA packet transmission."""
        self.log.info("Testing RDA packet...")

        # Create RDA packet for memory access
        rda_data = [0xDEADBEEF, 0x12345678, 0xABCDEF00, 0x55AA55AA, 0xFF00FF00]
        channel = 10
        chunk_enables = 0x001F  # First 5 chunks valid

        # Send RDA packet
        await self.network_system['send_rda'](channel, rda_data, chunk_enables)

        # Wait for reception
        packet = await self.network_system['receive_packet'](timeout_cycles=100)

        # Validate received packet
        assert packet.get_payload_type() == NETWORK_PKT_TYPES.RDA_PKT
        assert packet.get_channel() == channel
        assert packet.get_chunk_enables() == chunk_enables

        # Validate data fields
        received_data = packet.get_data_fields()[:5]
        assert received_data == rda_data

        self.log.info("RDA packet test passed")

    async def _test_raw_packet(self):
        """Test RAW packet transmission."""
        self.log.info("Testing RAW packet...")

        # Create RAW packet with full 512-bit data
        raw_data = 0x123456789ABCDEF0FEDCBA0987654321DEADBEEFCAFEBABE55AA55AAFF00FF00
        channel = 15

        # Send RAW packet
        await self.network_system['send_raw'](channel, raw_data)

        # Wait for reception
        packet = await self.network_system['receive_packet'](timeout_cycles=100)

        # Validate received packet
        assert packet.get_payload_type() == NETWORK_PKT_TYPES.RAW_PKT
        assert packet.get_channel() == channel

        # For RAW packets, data is in raw_data field
        received_data = getattr(packet, 'raw_data', 0)
        assert received_data == raw_data

        self.log.info("RAW packet test passed")

    async def test_chunk_enables_patterns(self):
        """Test various chunk_enables patterns."""
        self.log.info("=== Testing Chunk Enables Patterns ===")

        # Test sparse chunk patterns
        test_patterns = [
            0x0001,  # Only chunk 0
            0x8000,  # Only chunk 15 (should generate warning for structured packets)
            0x5555,  # Alternating chunks
            0xAAAA,  # Other alternating pattern
            0x00FF,  # First 8 chunks
            0xFF00,  # Last 8 chunks
            0x0F0F,  # Pattern chunks
        ]

        for i, chunk_pattern in enumerate(test_patterns):
            channel = i
            data = [0x1000 + i] * 5  # Simple test data

            self.log.info(f"Testing chunk pattern 0x{chunk_pattern:04X}")

            # Send TS packet with specific chunk pattern
            await self.network_system['send_ts'](channel, data, chunk_pattern)

            # Receive and validate
            packet = await self.network_system['receive_packet'](timeout_cycles=100)
            assert packet.get_chunk_enables() == chunk_pattern

            # Validate chunk count
            expected_count = bin(chunk_pattern).count('1')
            assert packet.get_chunk_count() == expected_count

            # Validate valid chunks list
            expected_chunks = [j for j in range(16) if chunk_pattern & (1 << j)]
            assert packet.get_valid_chunks() == expected_chunks

    async def test_packet_sequence(self):
        """Test sending a sequence of packets."""
        self.log.info("=== Testing Packet Sequence ===")

        # Create packet sequence
        sequence_configs = [
            {'channel': 0, 'data': [0x1111], 'packet_type': NETWORK_PKT_TYPES.CONFIG_PKT},
            {'channel': 1, 'data': [0x2222], 'packet_type': NETWORK_PKT_TYPES.TS_PKT},
            {'channel': 2, 'data': [0x3333], 'packet_type': NETWORK_PKT_TYPES.RDA_PKT},
            {'channel': 3, 'data': 0x44444444, 'packet_type': NETWORK_PKT_TYPES.RAW_PKT},
            {'channel': 0, 'data': [0x5555], 'packet_type': NETWORK_PKT_TYPES.TS_PKT, 'eos': True},
        ]

        # Send sequence
        await send_packet_sequence(
            self.network_system['master']['interface'],
            sequence_configs,
            inter_packet_delay=5
        )

        # Receive and validate sequence
        received_packets = []
        for expected_config in sequence_configs:
            packet = await self.network_system['receive_packet'](timeout_cycles=200)
            received_packets.append(packet)

            # Validate each packet
            assert validate_network_packet(packet, expected_config)

        # Validate EOS was received correctly
        last_packet = received_packets[-1]
        assert last_packet.get_eos() == True

        self.log.info(f"Packet sequence test passed - sent/received {len(sequence_configs)} packets")

    async def test_credit_management(self):
        """Test credit-based flow control."""
        self.log.info("=== Testing Credit Management ===")

        # Check initial credit state
        initial_credits = self.network_system['get_master_credits']()
        self.log.info(f"Initial credits: {initial_credits}")

        # Send packets up to credit limit
        channel = 7
        packets_to_send = self.config['initial_credits']

        for i in range(packets_to_send):
            data = [0x7000 + i]
            await self.network_system['send_ts'](channel, data)

            # Check remaining credits
            credits = self.network_system['get_master_credits']()
            remaining = credits[channel]['remaining']
            self.log.info(f"Packet {i+1} sent, remaining credits: {remaining}")

        # At this point, should be at credit limit
        final_credits = self.network_system['get_master_credits']()[channel]
        assert final_credits['remaining'] == 0

        self.log.info("Credit management test passed")

    async def test_eos_handling(self):
        """Test End of Stream handling."""
        self.log.info("=== Testing EOS Handling ===")

        # Send multiple packets, last with EOS
        channel = 20

        # Regular packets
        for i in range(3):
            data = [0x2000 + i]
            await self.network_system['send_ts'](channel, data, eos=False)

        # Final packet with EOS
        final_data = [0x2FFF]
        await self.network_system['send_ts'](channel, final_data, eos=True)

        # Receive all packets
        packets = []
        for i in range(4):
            packet = await self.network_system['receive_packet'](timeout_cycles=100)
            packets.append(packet)

        # Validate EOS only on last packet
        for i, packet in enumerate(packets):
            expected_eos = (i == 3)  # Only last packet should have EOS
            assert packet.get_eos() == expected_eos
            self.log.info(f"Packet {i}: EOS={packet.get_eos()}")

        self.log.info("EOS handling test passed")

    async def test_compliance_checking(self):
        """Test compliance checking features."""
        self.log.info("=== Testing Compliance Checking ===")

        # Get compliance status
        master_checker = self.network_system['master_compliance_checker']
        slave_checker = self.network_system['slave_compliance_checker']

        if master_checker:
            master_report = master_checker.get_compliance_report()
            self.log.info(f"Master compliance: {master_report['compliance_status']}")
            self.log.info(f"Master violations: {master_report['total_violations']}")

        if slave_checker:
            slave_report = slave_checker.get_compliance_report()
            self.log.info(f"Slave compliance: {slave_report['compliance_status']}")
            self.log.info(f"Slave violations: {slave_report['total_violations']}")

        # Test system compliance check
        from CocoTBFramework.components.network.network_factories import check_system_compliance
        system_compliant = check_system_compliance(self.network_system)
        self.log.info(f"System compliance: {'PASS' if system_compliant else 'FAIL'}")

    async def test_packet_validation(self):
        """Test packet validation features."""
        self.log.info("=== Testing Packet Validation ===")

        # Create test packets with various configurations
        field_config = MNOCFieldConfigHelper.create_packet_field_config()

        # Valid packet
        valid_packet = MNOCPacket.create_ts_packet(
            channel=5,
            ts_data=[0x1234, 0x5678],
            chunk_enables=0x0003,
            field_config=field_config
        )

        validation = valid_packet.validate_packet()
        assert validation['valid'] == True
        self.log.info(f"Valid packet validation: {validation}")

        # Test invalid chunk_enables (zero)
        try:
            invalid_packet = MNOCPacket.create_ts_packet(
                channel=5,
                ts_data=[0x1234],
                chunk_enables=0x0000,  # Invalid: no chunks enabled
                field_config=field_config
            )
            # This should raise an exception or fail validation
            validation = invalid_packet.validate_packet()
            assert validation['valid'] == False
            self.log.info("Invalid chunk_enables correctly detected")
        except ValueError as e:
            self.log.info(f"Invalid chunk_enables correctly rejected: {e}")

        self.log.info("Packet validation test passed")

    async def test_system_status(self):
        """Test system status reporting."""
        self.log.info("=== Testing System Status ===")

        # Get comprehensive system status
        status = self.network_system['system_status']()

        self.log.info("System Status Report:")
        self.log.info(f"Master Credits: {status['master_credits']}")
        self.log.info(f"Slave Stats: {status['slave_stats']}")

        if status['compliance_master']:
            self.log.info(f"Master Compliance: {status['compliance_master']['compliance_status']}")

        if status['compliance_slave']:
            self.log.info(f"Slave Compliance: {status['compliance_slave']['compliance_status']}")

    async def cleanup(self):
        """Cleanup test environment."""
        self.log.info("Cleaning up test environment...")

        # Reset packet history
        if self.network_system:
            self.network_system['reset_system']()

        # Print final compliance reports
        if self.network_system:
            from CocoTBFramework.components.network.network_factories import print_unified_compliance_reports
            print_unified_compliance_reports(self.network_system, self.log)

    async def run_all_tests(self):
        """Run complete test suite."""
        try:
            await self.setup()

            await self.test_basic_packet_transmission()
            await self.test_chunk_enables_patterns()
            await self.test_packet_sequence()
            await self.test_credit_management()
            await self.test_eos_handling()
            await self.test_compliance_checking()
            await self.test_packet_validation()
            await self.test_system_status()

            self.log.info("=== ALL TESTS PASSED ===")

        except Exception as e:
            self.log.error(f"Test failed: {e}")
            raise
        finally:
            await self.cleanup()


# Cocotb test entry points
@cocotb.test()
async def network_basic_test(dut):
    """Basic Network functionality test."""
    test = MNOCExampleTest(dut)
    await test.setup()
    await test.test_basic_packet_transmission()
    await test.cleanup()


@cocotb.test()
async def network_chunk_enables_test(dut):
    """Test v2.0 chunk_enables features."""
    test = MNOCExampleTest(dut)
    await test.setup()
    await test.test_chunk_enables_patterns()
    await test.cleanup()


@cocotb.test()
async def network_comprehensive_test(dut):
    """Comprehensive Network test suite."""
    test = MNOCExampleTest(dut)
    await test.run_all_tests()


@cocotb.test()
async def network_compliance_test(dut):
    """Focus on compliance checking features."""
    test = MNOCExampleTest(dut)
    await test.setup()
    await test.test_compliance_checking()
    await test.cleanup()


# Standalone test runner for development
if __name__ == "__main__":
    import sys
    print("Network Example Test")
    print("This file demonstrates the Network collateral API")
    print("Run with cocotb: python -m pytest network_example_test.py -v")
    print("Enable compliance: export NETWORK_COMPLIANCE_CHECK=1")
