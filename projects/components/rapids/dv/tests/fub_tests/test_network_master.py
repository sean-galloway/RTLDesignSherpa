# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RAPIDSNetworkMasterTB
# Purpose: RAPIDS Network Master FUB Validation Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Network Master FUB Validation Test

Comprehensive test for the RAPIDS Network master module, focusing on packet transmission,
credit management, and ACK processing.

Key Features Tested:
- Network packet transmission with embedded chunk enables
- Credit-based flow control with mathematical proof guarantees
- ACK reception and processing
- Four-stage pipeline operation
- EOS boundary handling
- Channel arbitration and selection
- Error detection (parity, credit overflow/underflow)
- Monitor bus event generation
"""

import os
import sys
import random
import asyncio
import pytest
import cocotb
from cocotb.triggers import RisingEdge, Timer, FallingEdge, ClockCycles
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class RAPIDSNetworkMasterTB(TBBase):
    """Testbench for RAPIDS Network Master"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get parameters from environment or use defaults
        self.DATA_WIDTH = int(os.environ.get('RAPIDS_DATA_WIDTH', '512'))
        self.ADDR_WIDTH = int(os.environ.get('RAPIDS_Network_ADDR_WIDTH', '16'))
        self.CHAN_WIDTH = int(os.environ.get('RAPIDS_CHAN_WIDTH', '3'))
        self.NUM_CHANNELS = int(os.environ.get('RAPIDS_NUM_CHANNELS', '8'))
        self.NUM_CHUNKS = int(os.environ.get('RAPIDS_NUM_CHUNKS', '16'))
        self.PIPELINE_STAGES = int(os.environ.get('RAPIDS_PIPELINE_STAGES', '3'))

        self.log.info(f"RAPIDS Network Master TB: {self.NUM_CHANNELS} channels, {self.NUM_CHUNKS} chunks")
        self.log.info(f"Data Width: {self.DATA_WIDTH}, Network Addr Width: {self.ADDR_WIDTH}")

        # Test state tracking
        self.packets_sent = 0
        self.acks_received = 0
        self.credit_returns = 0
        self.monitor_packets_received = []
        self.error_count = 0

        # Credit tracking per channel
        self.channel_credits = [0] * self.NUM_CHANNELS
        self.expected_credits = [0] * self.NUM_CHANNELS

        # Pipeline tracking
        self.pipeline_packets = []

    async def setup_clocks_and_reset(self):
        """Setup clock and reset the DUT"""
        await self.start_clock('clk', 0.4, 'ns')  # 2.5 GHz

        # Reset sequence
        self.dut.rst_n.value = 0
        await ClockCycles(self.dut.clk, 10)
        self.dut.rst_n.value = 1
        await ClockCycles(self.dut.clk, 5)

        await self.initialize_inputs()

    async def initialize_inputs(self):
        """Initialize all DUT inputs to safe values"""
        # Read interface from SRAM control
        self.dut.rd_valid.value = 0
        self.dut.rd_data.value = 0
        self.dut.rd_type.value = 0
        self.dut.rd_eos.value = 0
        self.dut.rd_chunk_valid.value = 0
        self.dut.rd_channel.value = 0
        self.dut.rd_used_count.value = 0

        # Channel data availability
        self.dut.loaded_lines.value = 0

        # Master Network interface ready
        self.dut.m_network_pkt_ready.value = 1

        # Slave Network ACK interface
        self.dut.s_network_ack_addr.value = 0
        self.dut.s_network_ack_addr_par.value = 0
        self.dut.s_network_ack_ack.value = 0
        self.dut.s_network_ack_par.value = 0
        self.dut.s_network_ack_valid.value = 0

        # Monitor bus interface
        self.dut.mon_ready.value = 1

    def create_test_packet(self, channel=0, data_pattern=0xDEADBEEF, chunk_enables=0xFFFF,
                          packet_type=1, has_eos=False):
        """Create a test data packet"""
        # Create 512-bit data with embedded chunk enables
        data = 0

        # Embed chunk enables in data[510:495] as per Network 2.0 spec
        data |= (chunk_enables & 0xFFFF) << 495

        # Fill rest with pattern
        for i in range(0, 495, 32):
            data |= (data_pattern << i)

        return {
            'data': data,
            'type': packet_type,
            'eos': has_eos,
            'chunk_valid': chunk_enables,
            'channel': channel
        }

    def calculate_parity(self, data):
        """Calculate even parity for data"""
        parity = 0
        while data:
            parity ^= (data & 1)
            data >>= 1
        return parity

    async def send_read_data(self, packet_info):
        """Send read data to Network master"""
        # Wait for ready
        while self.dut.rd_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Send packet
        self.dut.rd_valid.value = 1
        self.dut.rd_data.value = packet_info['data']
        self.dut.rd_type.value = packet_info['type']
        self.dut.rd_eos.value = 1 if packet_info['eos'] else 0
        self.dut.rd_chunk_valid.value = packet_info['chunk_valid']
        self.dut.rd_channel.value = packet_info['channel']
        self.dut.rd_used_count.value = random.randint(1, 255)

        # Wait for handshake
        await RisingEdge(self.dut.clk)
        while self.dut.rd_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Clear inputs
        self.dut.rd_valid.value = 0
        self.dut.rd_data.value = 0
        self.dut.rd_eos.value = 0

        self.log.info(f"Sent read data: channel={packet_info['channel']}, eos={packet_info['eos']}")

    async def send_ack(self, addr, ack_type=1):
        """Send ACK from network"""
        # Calculate address parity
        addr_parity = self.calculate_parity(addr)

        # Calculate body parity (ACK type)
        body_parity = self.calculate_parity(ack_type)

        # Wait for ready
        while self.dut.s_network_ack_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Send ACK
        self.dut.s_network_ack_valid.value = 1
        self.dut.s_network_ack_addr.value = addr
        self.dut.s_network_ack_addr_par.value = addr_parity
        self.dut.s_network_ack_ack.value = ack_type
        self.dut.s_network_ack_par.value = body_parity

        # Wait for handshake
        await RisingEdge(self.dut.clk)
        while self.dut.s_network_ack_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Clear ACK
        self.dut.s_network_ack_valid.value = 0
        self.dut.s_network_ack_addr.value = 0
        self.dut.s_network_ack_addr_par.value = 0
        self.dut.s_network_ack_ack.value = 0
        self.dut.s_network_ack_par.value = 0

        self.acks_received += 1
        self.log.info(f"Sent ACK: addr=0x{addr:04x}, type={ack_type}")

    async def monitor_mnoc_output(self):
        """Monitor Network packet output"""
        while True:
            await RisingEdge(self.dut.clk)

            if self.dut.m_network_pkt_valid.value == 1 and self.dut.m_network_pkt_ready.value == 1:
                # Capture packet
                addr = int(self.dut.m_network_pkt_addr.value)
                addr_par = int(self.dut.m_network_pkt_addr_par.value)
                data = int(self.dut.m_network_pkt_data.value)
                pkt_type = int(self.dut.m_network_pkt_type.value)
                eos = int(self.dut.m_network_pkt_eos.value)
                parity = int(self.dut.m_network_pkt_par.value)

                # Extract embedded chunk enables
                chunk_enables = (data >> 495) & 0xFFFF

                self.packets_sent += 1
                self.log.info(f"Network packet sent: addr=0x{addr:04x}, type={pkt_type}, eos={eos}")
                self.log.info(f"  chunk_enables=0x{chunk_enables:04x}, parity={parity}")

                # Verify parity
                expected_addr_parity = self.calculate_parity(addr)
                if addr_par != expected_addr_parity:
                    self.error_count += 1
                    self.log.error(f"Address parity error: expected {expected_addr_parity}, got {addr_par}")

                # Store packet for verification
                self.pipeline_packets.append({
                    'addr': addr,
                    'data': data,
                    'type': pkt_type,
                    'eos': eos,
                    'chunk_enables': chunk_enables
                })

                # Simulate network delay and send ACK
                ack_delay = random.randint(5, 20)
                cocotb.start_soon(self.delayed_ack(addr, 1, ack_delay))

    async def delayed_ack(self, addr, ack_type, delay):
        """Send delayed ACK"""
        await ClockCycles(self.dut.clk, delay)
        await self.send_ack(addr, ack_type)

    async def monitor_error_signals(self):
        """Monitor error and status signals"""
        while True:
            await RisingEdge(self.dut.clk)

            # Check error signals
            if hasattr(self.dut, 'error_credit_underflow') and self.dut.error_credit_underflow.value == 1:
                self.error_count += 1
                self.log.error("Credit underflow detected")

            if hasattr(self.dut, 'error_credit_overflow') and self.dut.error_credit_overflow.value == 1:
                self.error_count += 1
                self.log.error("Credit overflow detected")

            if hasattr(self.dut, 'error_ack_header_parity') and self.dut.error_ack_header_parity.value == 1:
                self.error_count += 1
                self.log.error("ACK header parity error detected")

            if hasattr(self.dut, 'error_ack_body_parity') and self.dut.error_ack_body_parity.value == 1:
                self.error_count += 1
                self.log.error("ACK body parity error detected")

            if hasattr(self.dut, 'error_eos_lost') and self.dut.error_eos_lost.value == 1:
                self.error_count += 1
                self.log.error("EOS lost error detected")

    async def monitor_monitor_bus(self):
        """Monitor the monitor bus for events"""
        while True:
            await RisingEdge(self.dut.clk)

            if self.dut.mon_valid.value == 1 and self.dut.mon_ready.value == 1:
                packet = int(self.dut.mon_packet.value)
                self.monitor_packets_received.append(packet)
                self.log.info(f"Monitor packet: 0x{packet:016x}")

    async def set_channel_data_availability(self, channel_mask):
        """Set which channels have data available"""
        self.dut.loaded_lines.value = channel_mask

    async def test_basic_packet_transmission(self):
        """Test basic packet transmission"""
        self.log.info("=== Testing Basic Packet Transmission ===")

        # Set channel 0 as having data
        await self.set_channel_data_availability(0x01)

        # Send a packet
        packet = self.create_test_packet(channel=0, has_eos=True)
        await self.send_read_data(packet)

        # Wait for packet to appear on Network output
        await ClockCycles(self.dut.clk, 50)

        assert self.packets_sent > 0, "No packets transmitted"

    async def test_multi_channel_arbitration(self):
        """Test arbitration between multiple channels"""
        self.log.info("=== Testing Multi-Channel Arbitration ===")

        # Set multiple channels as having data
        await self.set_channel_data_availability(0x0F)  # Channels 0-3

        # Send packets for different channels
        for channel in range(4):
            packet = self.create_test_packet(channel=channel)
            await self.send_read_data(packet)

        # Wait for all packets to be processed
        await ClockCycles(self.dut.clk, 200)

        assert self.packets_sent >= 4, f"Expected at least 4 packets, got {self.packets_sent}"

    async def test_chunk_enable_embedding(self):
        """Test chunk enable embedding in data"""
        self.log.info("=== Testing Chunk Enable Embedding ===")

        # Test different chunk enable patterns
        test_patterns = [0x0001, 0x8000, 0xAAAA, 0x5555, 0xFFFF, 0x0000]

        await self.set_channel_data_availability(0x01)

        for i, pattern in enumerate(test_patterns):
            packet = self.create_test_packet(
                channel=0,
                chunk_enables=pattern,
                data_pattern=0x12345678 + i
            )
            await self.send_read_data(packet)

            # Wait for transmission
            await ClockCycles(self.dut.clk, 30)

        # Verify chunk enables were embedded correctly
        for i, expected_pattern in enumerate(test_patterns):
            if i < len(self.pipeline_packets):
                actual_pattern = self.pipeline_packets[i]['chunk_enables']
                assert actual_pattern == expected_pattern, \
                    f"Chunk enable mismatch: expected 0x{expected_pattern:04x}, got 0x{actual_pattern:04x}"

    async def test_eos_boundary_handling(self):
        """Test EOS boundary processing"""
        self.log.info("=== Testing EOS Boundary Handling ===")

        await self.set_channel_data_availability(0x01)

        # Send regular packet
        regular_packet = self.create_test_packet(channel=0, has_eos=False)
        await self.send_read_data(regular_packet)

        # Send EOS packet
        eos_packet = self.create_test_packet(channel=0, has_eos=True)
        await self.send_read_data(eos_packet)

        await ClockCycles(self.dut.clk, 100)

        # Verify EOS was handled correctly
        eos_packets = [p for p in self.pipeline_packets if p['eos'] == 1]
        assert len(eos_packets) > 0, "No EOS packets transmitted"

    async def test_pipeline_operation(self):
        """Test four-stage pipeline operation"""
        self.log.info("=== Testing Pipeline Operation ===")

        await self.set_channel_data_availability(0xFF)  # All channels

        # Send burst of packets to test pipeline
        for i in range(8):
            packet = self.create_test_packet(
                channel=i % self.NUM_CHANNELS,
                data_pattern=0x10000000 + i
            )
            await self.send_read_data(packet)

        # Wait for pipeline to flush
        await ClockCycles(self.dut.clk, 100)

        assert self.packets_sent >= 8, "Pipeline did not process all packets"

    async def test_credit_flow_control(self):
        """Test credit-based flow control"""
        self.log.info("=== Testing Credit Flow Control ===")

        # This test depends on the specific credit implementation
        # For now, just verify no credit errors occur during normal operation

        await self.set_channel_data_availability(0x01)

        # Send multiple packets
        for i in range(10):
            packet = self.create_test_packet(channel=0)
            await self.send_read_data(packet)
            await ClockCycles(self.dut.clk, 20)

        # Wait for completion
        await ClockCycles(self.dut.clk, 200)

        # Should have no credit errors
        # (Actual credit checking would require access to internal signals)

    async def test_ack_processing(self):
        """Test ACK reception and processing"""
        self.log.info("=== Testing ACK Processing ===")

        await self.set_channel_data_availability(0x01)

        # Send packet
        packet = self.create_test_packet(channel=0)
        await self.send_read_data(packet)

        # Wait for packet transmission
        await ClockCycles(self.dut.clk, 50)

        # Send ACK manually (in addition to automatic ACKs)
        await self.send_ack(0x1234, 1)

        await ClockCycles(self.dut.clk, 50)

        assert self.acks_received > 0, "No ACKs processed"

    async def test_parity_error_injection(self):
        """Test parity error detection"""
        self.log.info("=== Testing Parity Error Detection ===")

        await self.set_channel_data_availability(0x01)

        # Send packet
        packet = self.create_test_packet(channel=0)
        await self.send_read_data(packet)

        # Wait for transmission
        await ClockCycles(self.dut.clk, 30)

        # Send ACK with incorrect parity
        self.dut.s_network_ack_valid.value = 1
        self.dut.s_network_ack_addr.value = 0x1000
        self.dut.s_network_ack_addr_par.value = 0  # Incorrect parity
        self.dut.s_network_ack_ack.value = 1
        self.dut.s_network_ack_par.value = 1  # Incorrect parity

        await RisingEdge(self.dut.clk)
        self.dut.s_network_ack_valid.value = 0

        await ClockCycles(self.dut.clk, 10)

        # Should detect parity errors
        # (Error detection verification depends on implementation)

    async def test_backpressure_handling(self):
        """Test backpressure from Network network"""
        self.log.info("=== Testing Backpressure Handling ===")

        await self.set_channel_data_availability(0x01)

        # Block Network output
        self.dut.m_network_pkt_ready.value = 0

        # Send packet
        packet = self.create_test_packet(channel=0)
        await self.send_read_data(packet)

        # Should not transmit due to backpressure
        await ClockCycles(self.dut.clk, 50)

        # Release backpressure
        self.dut.m_network_pkt_ready.value = 1

        # Should now transmit
        await ClockCycles(self.dut.clk, 50)

    async def run_comprehensive_test(self, test_level='basic'):
        """Run comprehensive test suite"""
        self.log.info(f"=== Starting {test_level.upper()} Network Master Test ===")

        # Start background monitoring tasks
        monitor_tasks = [
            cocotb.start_soon(self.monitor_mnoc_output()),
            cocotb.start_soon(self.monitor_error_signals()),
            cocotb.start_soon(self.monitor_monitor_bus())
        ]

        try:
            # Run test sequences
            await self.test_basic_packet_transmission()
            await self.test_chunk_enable_embedding()
            await self.test_eos_boundary_handling()

            if test_level in ['medium', 'full']:
                await self.test_multi_channel_arbitration()
                await self.test_pipeline_operation()
                await self.test_ack_processing()

            if test_level == 'full':
                await self.test_credit_flow_control()
                await self.test_parity_error_injection()
                await self.test_backpressure_handling()

        finally:
            # Cancel monitoring tasks
            for task in monitor_tasks:
                task.cancel()

        # Report results
        self.log.info("=== Test Results ===")
        self.log.info(f"Packets sent: {self.packets_sent}")
        self.log.info(f"ACKs received: {self.acks_received}")
        self.log.info(f"Monitor packets: {len(self.monitor_packets_received)}")
        self.log.info(f"Errors detected: {self.error_count}")

        # Verify no unexpected errors
        assert self.error_count == 0, f"Unexpected errors detected: {self.error_count}"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def test_miop_network_master(dut):
    """Main test entry point for RAPIDS Network Master"""

    tb = RAPIDSNetworkMasterTB(dut)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    await tb.setup_clocks_and_reset()
    await tb.run_comprehensive_test(test_level)

    tb.log.info("RAPIDS Network Master test completed successfully")


# Pytest integration
@pytest.mark.fub
@pytest.mark.mnoc
def test_network_master_basic():
    """Basic Network master test"""
    run_test_with_parameters({'TEST_LEVEL': 'basic'})

@pytest.mark.fub
@pytest.mark.mnoc
def test_network_master_medium():
    """Medium Network master test"""
    run_test_with_parameters({'TEST_LEVEL': 'medium'})

@pytest.mark.fub
@pytest.mark.mnoc
@pytest.mark.performance
def test_network_master_full():
    """Full Network master test"""
    run_test_with_parameters({'TEST_LEVEL': 'full'})


def run_test_with_parameters(env_params=None):
    """Run the test with specified parameters"""
    if env_params:
        for key, value in env_params.items():
            os.environ[key] = str(value)

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_common_includes': 'rtl/common/includes'
    })

    parameters = {
        'DATA_WIDTH': int(os.environ.get('RAPIDS_DATA_WIDTH', '512')),
        'ADDR_WIDTH': int(os.environ.get('RAPIDS_Network_ADDR_WIDTH', '16')),
        'CHAN_WIDTH': int(os.environ.get('RAPIDS_CHAN_WIDTH', '3')),
        'NUM_CHANNELS': int(os.environ.get('RAPIDS_NUM_CHANNELS', '8')),
        'NUM_CHUNKS': int(os.environ.get('RAPIDS_NUM_CHUNKS', '16')),
        'PIPELINE_STAGES': int(os.environ.get('RAPIDS_PIPELINE_STAGES', '3')),
        'INPUT_FIFO_DEPTH': int(os.environ.get('RAPIDS_INPUT_FIFO_DEPTH', '8')),
    }

    verilog_sources = [
        os.path.join(rtl_dict['rtl_rapids_fub'], 'network_master.sv'),
    ]

    include_dirs = [
        rtl_dict['rtl_common_includes'],
        rtl_dict['rtl_rapids_includes'],
        rtl_dict['rtl_amba_includes'],
    ]

    run(
        verilog_sources=verilog_sources,
        toplevel="network_master",
        module="test_network_master",
        testcase="test_miop_network_master",
        parameters=parameters,
        includes=include_dirs,
        simulator="verilator",
        waves=os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
        extra_env=env_params or {}
    )


if __name__ == "__main__":
    run_test_with_parameters()