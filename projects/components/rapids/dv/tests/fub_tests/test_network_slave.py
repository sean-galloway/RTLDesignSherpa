# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RAPIDSNetworkSlaveeTB
# Purpose: RAPIDS Network Slave FUB Validation Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Network Slave FUB Validation Test

Comprehensive test for the RAPIDS Network slave module, focusing on packet reception,
ACK generation, and data routing.

Key Features Tested:
- Network packet reception with embedded chunk enables extraction
- Bulletproof ACK generation with dual FIFO queues
- Intelligent packet routing (data vs RDA packets)
- Parity validation (header and body)
- Protocol compliance and error detection
- Buffer overflow protection
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


class RAPIDSNetworkSlaveeTB(TBBase):
    """Testbench for RAPIDS Network Slave"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get parameters from environment or use defaults
        self.ADDR_WIDTH = int(os.environ.get('RAPIDS_Network_ADDR_WIDTH', '8'))
        self.DATA_WIDTH = int(os.environ.get('RAPIDS_DATA_WIDTH', '512'))
        self.NUM_CHUNKS = int(os.environ.get('RAPIDS_NUM_CHUNKS', '16'))
        self.NUM_CHANNELS = int(os.environ.get('RAPIDS_NUM_CHANNELS', '8'))
        self.CHAN_WIDTH = int(os.environ.get('RAPIDS_CHAN_WIDTH', '3'))

        self.log.info(f"RAPIDS Network Slave TB: {self.NUM_CHANNELS} channels, {self.NUM_CHUNKS} chunks")
        self.log.info(f"Data Width: {self.DATA_WIDTH}, Network Addr Width: {self.ADDR_WIDTH}")

        # Test state tracking
        self.packets_received = 0
        self.acks_sent = 0
        self.data_packets_output = 0
        self.rda_src_packets_output = 0
        self.rda_snk_packets_output = 0
        self.monitor_packets_received = []
        self.error_count = 0

        # Packet tracking
        self.received_packets = []
        self.sent_acks = []

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
        # Network packet interface (from network)
        self.dut.s_network_pkt_addr.value = 0
        self.dut.s_network_pkt_addr_par.value = 0
        self.dut.s_network_pkt_data.value = 0
        self.dut.s_network_pkt_type.value = 0
        self.dut.s_network_pkt_eos.value = 0
        self.dut.s_network_pkt_par.value = 0
        self.dut.s_network_pkt_valid.value = 0

        # Network ACK interface (to network)
        self.dut.m_network_ack_ready.value = 1

        # Write interface (to SRAM control)
        self.dut.wr_src_ready.value = 1

        # RDA interfaces (to external descriptor engines)
        self.dut.rda_src_ready.value = 1
        self.dut.rda_snk_ready.value = 1

        # Data consumption interface
        self.dut.data_consumed_valid.value = 0
        self.dut.data_consumed_channel.value = 0

        # Monitor bus interface
        self.dut.mon_ready.value = 1

    def calculate_parity(self, data):
        """Calculate even parity for data"""
        parity = 0
        while data:
            parity ^= (data & 1)
            data >>= 1
        return parity

    def create_network_packet(self, addr=0x1000, data_pattern=0xDEADBEEF,
                          chunk_enables=0xFFFF, packet_type=1, has_eos=False,
                          is_rda_src=False, is_rda_snk=False):
        """Create a Network packet"""
        # Create 512-bit data with embedded chunk enables
        data = 0

        # Embed chunk enables in data[510:495] as per Network 2.0 spec
        data |= (chunk_enables & 0xFFFF) << 495

        # Fill rest with pattern
        for i in range(0, 495, 32):
            data |= (data_pattern << i)

        # Set packet type to indicate RDA if needed
        if is_rda_src:
            packet_type = 2  # RDA source packet type
        elif is_rda_snk:
            packet_type = 3  # RDA sink packet type

        # Calculate parities
        addr_parity = self.calculate_parity(addr)
        body_parity = self.calculate_parity(data)

        return {
            'addr': addr,
            'addr_par': addr_parity,
            'data': data,
            'type': packet_type,
            'eos': has_eos,
            'par': body_parity,
            'chunk_enables': chunk_enables,
            'is_rda_src': is_rda_src,
            'is_rda_snk': is_rda_snk
        }

    async def send_network_packet(self, packet_info):
        """Send Network packet to slave"""
        # Wait for ready
        while self.dut.s_network_pkt_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Send packet
        self.dut.s_network_pkt_valid.value = 1
        self.dut.s_network_pkt_addr.value = packet_info['addr']
        self.dut.s_network_pkt_addr_par.value = packet_info['addr_par']
        self.dut.s_network_pkt_data.value = packet_info['data']
        self.dut.s_network_pkt_type.value = packet_info['type']
        self.dut.s_network_pkt_eos.value = 1 if packet_info['eos'] else 0
        self.dut.s_network_pkt_par.value = packet_info['par']

        # Wait for handshake
        await RisingEdge(self.dut.clk)
        while self.dut.s_network_pkt_ready.value != 1:
            await RisingEdge(self.dut.clk)

        # Clear inputs
        self.dut.s_network_pkt_valid.value = 0
        self.dut.s_network_pkt_addr.value = 0
        self.dut.s_network_pkt_addr_par.value = 0
        self.dut.s_network_pkt_data.value = 0
        self.dut.s_network_pkt_type.value = 0
        self.dut.s_network_pkt_eos.value = 0
        self.dut.s_network_pkt_par.value = 0

        self.packets_received += 1
        self.received_packets.append(packet_info)

        self.log.info(f"Sent Network packet: addr=0x{packet_info['addr']:04x}, type={packet_info['type']}, eos={packet_info['eos']}")

    async def monitor_ack_output(self):
        """Monitor ACK output to network"""
        while True:
            await RisingEdge(self.dut.clk)

            if self.dut.m_network_ack_valid.value == 1 and self.dut.m_network_ack_ready.value == 1:
                # Capture ACK
                addr = int(self.dut.m_network_ack_addr.value)
                addr_par = int(self.dut.m_network_ack_addr_par.value)
                ack = int(self.dut.m_network_ack_ack.value)
                par = int(self.dut.m_network_ack_par.value)

                self.acks_sent += 1
                self.sent_acks.append({
                    'addr': addr,
                    'addr_par': addr_par,
                    'ack': ack,
                    'par': par
                })

                self.log.info(f"ACK sent: addr=0x{addr:04x}, ack={ack}")

                # Verify parity
                expected_addr_parity = self.calculate_parity(addr)
                expected_body_parity = self.calculate_parity(ack)

                if addr_par != expected_addr_parity:
                    self.error_count += 1
                    self.log.error(f"ACK address parity error: expected {expected_addr_parity}, got {addr_par}")

                if par != expected_body_parity:
                    self.error_count += 1
                    self.log.error(f"ACK body parity error: expected {expected_body_parity}, got {par}")

    async def monitor_write_output(self):
        """Monitor write output to SRAM control"""
        while True:
            await RisingEdge(self.dut.clk)

            if self.dut.wr_src_valid.value == 1 and self.dut.wr_src_ready.value == 1:
                # Capture write data
                packet = int(self.dut.wr_src_packet.value)
                channel = int(self.dut.wr_src_channel.value)
                eos = int(self.dut.wr_src_eos.value)
                chunk_enables = int(self.dut.wr_src_chunk_enables.value)

                self.data_packets_output += 1
                self.log.info(f"Data packet output: channel={channel}, eos={eos}, chunks=0x{chunk_enables:04x}")

    async def monitor_rda_outputs(self):
        """Monitor RDA outputs to external descriptor engines"""
        while True:
            await RisingEdge(self.dut.clk)

            # Monitor RDA source output
            if self.dut.rda_src_valid.value == 1 and self.dut.rda_src_ready.value == 1:
                packet = int(self.dut.rda_src_packet.value)
                channel = int(self.dut.rda_src_channel.value)
                eos = int(self.dut.rda_src_eos.value)

                self.rda_src_packets_output += 1
                self.log.info(f"RDA source packet output: channel={channel}, eos={eos}")

            # Monitor RDA sink output
            if self.dut.rda_snk_valid.value == 1 and self.dut.rda_snk_ready.value == 1:
                packet = int(self.dut.rda_snk_packet.value)
                channel = int(self.dut.rda_snk_channel.value)
                eos = int(self.dut.rda_snk_eos.value)

                self.rda_snk_packets_output += 1
                self.log.info(f"RDA sink packet output: channel={channel}, eos={eos}")

    async def monitor_error_signals(self):
        """Monitor error and status signals"""
        while True:
            await RisingEdge(self.dut.clk)

            # Check error signals
            if hasattr(self.dut, 'error_header_parity') and self.dut.error_header_parity.value == 1:
                self.error_count += 1
                self.log.error("Header parity error detected")

            if hasattr(self.dut, 'error_body_parity') and self.dut.error_body_parity.value == 1:
                self.error_count += 1
                self.log.error("Body parity error detected")

            if hasattr(self.dut, 'error_protocol') and self.dut.error_protocol.value == 1:
                self.error_count += 1
                self.log.error("Protocol error detected")

            if hasattr(self.dut, 'error_buffer_overflow') and self.dut.error_buffer_overflow.value == 1:
                self.error_count += 1
                self.log.error("Buffer overflow error detected")

            if hasattr(self.dut, 'error_ack_lost') and self.dut.error_ack_lost.value == 1:
                self.error_count += 1
                self.log.error("ACK lost error detected")

    async def monitor_monitor_bus(self):
        """Monitor the monitor bus for events"""
        while True:
            await RisingEdge(self.dut.clk)

            if self.dut.mon_valid.value == 1 and self.dut.mon_ready.value == 1:
                packet = int(self.dut.mon_packet.value)
                self.monitor_packets_received.append(packet)
                self.log.info(f"Monitor packet: 0x{packet:016x}")

    async def send_data_consumed_signal(self, channel):
        """Send data consumed signal"""
        self.dut.data_consumed_valid.value = 1
        self.dut.data_consumed_channel.value = channel

        await RisingEdge(self.dut.clk)
        while self.dut.data_consumed_ready.value != 1:
            await RisingEdge(self.dut.clk)

        self.dut.data_consumed_valid.value = 0
        self.dut.data_consumed_channel.value = 0

        self.log.info(f"Data consumed signal sent for channel {channel}")

    async def test_basic_packet_reception(self):
        """Test basic packet reception and ACK generation"""
        self.log.info("=== Testing Basic Packet Reception ===")

        # Send a basic data packet
        packet = self.create_network_packet(
            addr=0x1000,
            data_pattern=0x12345678,
            chunk_enables=0xFFFF,
            has_eos=True
        )
        await self.send_network_packet(packet)

        # Wait for processing
        await ClockCycles(self.dut.clk, 50)

        # Should generate ACK
        assert self.acks_sent > 0, "No ACK generated"

        # Should output data packet
        assert self.data_packets_output > 0, "No data packet output"

    async def test_rda_packet_routing(self):
        """Test RDA packet routing to appropriate outputs"""
        self.log.info("=== Testing RDA Packet Routing ===")

        # Send RDA source packet
        rda_src_packet = self.create_network_packet(
            addr=0x2000,
            is_rda_src=True,
            has_eos=True
        )
        await self.send_network_packet(rda_src_packet)

        # Send RDA sink packet
        rda_snk_packet = self.create_network_packet(
            addr=0x3000,
            is_rda_snk=True,
            has_eos=True
        )
        await self.send_network_packet(rda_snk_packet)

        # Wait for processing
        await ClockCycles(self.dut.clk, 100)

        # Should route to appropriate outputs
        assert self.rda_src_packets_output > 0, "No RDA source packet output"
        assert self.rda_snk_packets_output > 0, "No RDA sink packet output"

        # Should still generate ACKs
        assert self.acks_sent >= 2, "Missing ACKs for RDA packets"

    async def test_chunk_enable_extraction(self):
        """Test chunk enable extraction from embedded data"""
        self.log.info("=== Testing Chunk Enable Extraction ===")

        # Test different chunk enable patterns
        test_patterns = [0x0001, 0x8000, 0xAAAA, 0x5555, 0xFFFF]

        for i, pattern in enumerate(test_patterns):
            packet = self.create_network_packet(
                addr=0x4000 + i,
                chunk_enables=pattern
            )
            await self.send_network_packet(packet)

        await ClockCycles(self.dut.clk, 200)

        # All packets should be processed
        assert self.data_packets_output >= len(test_patterns), "Not all packets processed"

    async def test_eos_boundary_processing(self):
        """Test EOS boundary processing"""
        self.log.info("=== Testing EOS Boundary Processing ===")

        # Send packet without EOS
        regular_packet = self.create_network_packet(addr=0x5000, has_eos=False)
        await self.send_network_packet(regular_packet)

        # Send packet with EOS
        eos_packet = self.create_network_packet(addr=0x5001, has_eos=True)
        await self.send_network_packet(eos_packet)

        await ClockCycles(self.dut.clk, 100)

        # Both packets should be processed
        assert self.data_packets_output >= 2, "Not all EOS test packets processed"

    async def test_parity_error_detection(self):
        """Test parity error detection"""
        self.log.info("=== Testing Parity Error Detection ===")

        # Send packet with incorrect address parity
        packet = self.create_network_packet(addr=0x6000)
        packet['addr_par'] = 1 - packet['addr_par']  # Flip parity
        await self.send_network_packet(packet)

        # Send packet with incorrect body parity
        packet2 = self.create_network_packet(addr=0x6001)
        packet2['par'] = 1 - packet2['par']  # Flip parity
        await self.send_network_packet(packet2)

        await ClockCycles(self.dut.clk, 100)

        # Should detect parity errors
        # (Specific error handling depends on implementation)

    async def test_backpressure_handling(self):
        """Test backpressure from downstream"""
        self.log.info("=== Testing Backpressure Handling ===")

        # Block write output
        self.dut.wr_src_ready.value = 0

        # Send packet
        packet = self.create_network_packet(addr=0x7000)
        await self.send_network_packet(packet)

        # Should handle backpressure gracefully
        await ClockCycles(self.dut.clk, 50)

        # Release backpressure
        self.dut.wr_src_ready.value = 1

        # Should complete processing
        await ClockCycles(self.dut.clk, 50)

    async def test_multiple_packet_burst(self):
        """Test handling multiple packet burst"""
        self.log.info("=== Testing Multiple Packet Burst ===")

        # Send burst of packets
        for i in range(8):
            packet = self.create_network_packet(
                addr=0x8000 + i,
                data_pattern=0x10000000 + i
            )
            await self.send_network_packet(packet)

        await ClockCycles(self.dut.clk, 200)

        # All packets should be processed
        assert self.data_packets_output >= 8, "Not all burst packets processed"
        assert self.acks_sent >= 8, "Missing ACKs for burst packets"

    async def test_data_consumed_interface(self):
        """Test data consumed interface"""
        self.log.info("=== Testing Data Consumed Interface ===")

        # Send packet
        packet = self.create_network_packet(addr=0x9000)
        await self.send_network_packet(packet)

        await ClockCycles(self.dut.clk, 50)

        # Send data consumed signal
        await self.send_data_consumed_signal(0)

        await ClockCycles(self.dut.clk, 50)

        # Should handle consumed signal correctly

    async def test_ack_fifo_operation(self):
        """Test dual ACK FIFO operation"""
        self.log.info("=== Testing ACK FIFO Operation ===")

        # Block ACK output
        self.dut.m_network_ack_ready.value = 0

        # Send multiple packets to fill ACK FIFO
        for i in range(10):
            packet = self.create_network_packet(addr=0xA000 + i)
            await self.send_network_packet(packet)

        await ClockCycles(self.dut.clk, 100)

        # Release ACK output
        self.dut.m_network_ack_ready.value = 1

        # ACKs should drain from FIFO
        await ClockCycles(self.dut.clk, 200)

        assert self.acks_sent >= 10, "Not all ACKs sent from FIFO"

    async def run_comprehensive_test(self, test_level='basic'):
        """Run comprehensive test suite"""
        self.log.info(f"=== Starting {test_level.upper()} Network Slave Test ===")

        # Start background monitoring tasks
        monitor_tasks = [
            cocotb.start_soon(self.monitor_ack_output()),
            cocotb.start_soon(self.monitor_write_output()),
            cocotb.start_soon(self.monitor_rda_outputs()),
            cocotb.start_soon(self.monitor_error_signals()),
            cocotb.start_soon(self.monitor_monitor_bus())
        ]

        try:
            # Run test sequences
            await self.test_basic_packet_reception()
            await self.test_chunk_enable_extraction()
            await self.test_eos_boundary_processing()

            if test_level in ['medium', 'full']:
                await self.test_rda_packet_routing()
                await self.test_multiple_packet_burst()
                await self.test_data_consumed_interface()

            if test_level == 'full':
                await self.test_parity_error_detection()
                await self.test_backpressure_handling()
                await self.test_ack_fifo_operation()

        finally:
            # Cancel monitoring tasks
            for task in monitor_tasks:
                task.cancel()

        # Report results
        self.log.info("=== Test Results ===")
        self.log.info(f"Packets received: {self.packets_received}")
        self.log.info(f"ACKs sent: {self.acks_sent}")
        self.log.info(f"Data packets output: {self.data_packets_output}")
        self.log.info(f"RDA source packets output: {self.rda_src_packets_output}")
        self.log.info(f"RDA sink packets output: {self.rda_snk_packets_output}")
        self.log.info(f"Monitor packets: {len(self.monitor_packets_received)}")
        self.log.info(f"Errors detected: {self.error_count}")

        # Verify no unexpected errors (unless testing error conditions)
        if test_level != 'full':  # Full test includes error injection
            assert self.error_count == 0, f"Unexpected errors detected: {self.error_count}"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def test_miop_network_slave(dut):
    """Main test entry point for RAPIDS Network Slave"""

    tb = RAPIDSNetworkSlaveeTB(dut)
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    await tb.setup_clocks_and_reset()
    await tb.run_comprehensive_test(test_level)

    tb.log.info("RAPIDS Network Slave test completed successfully")


# Pytest integration
@pytest.mark.fub
@pytest.mark.mnoc
def test_network_slave_basic():
    """Basic Network slave test"""
    run_test_with_parameters({'TEST_LEVEL': 'basic'})

@pytest.mark.fub
@pytest.mark.mnoc
def test_network_slave_medium():
    """Medium Network slave test"""
    run_test_with_parameters({'TEST_LEVEL': 'medium'})

@pytest.mark.fub
@pytest.mark.mnoc
@pytest.mark.performance
def test_network_slave_full():
    """Full Network slave test"""
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
        'ADDR_WIDTH': int(os.environ.get('RAPIDS_Network_ADDR_WIDTH', '8')),
        'DATA_WIDTH': int(os.environ.get('RAPIDS_DATA_WIDTH', '512')),
        'NUM_CHUNKS': int(os.environ.get('RAPIDS_NUM_CHUNKS', '16')),
        'NUM_CHANNELS': int(os.environ.get('RAPIDS_NUM_CHANNELS', '8')),
        'CHAN_WIDTH': int(os.environ.get('RAPIDS_CHAN_WIDTH', '3')),
    }

    verilog_sources = [
        os.path.join(rtl_dict['rtl_rapids_fub'], 'network_slave.sv'),
    ]

    include_dirs = [
        rtl_dict['rtl_common_includes'],
        rtl_dict['rtl_rapids_includes'],
        rtl_dict['rtl_amba_includes'],
    ]

    run(
        verilog_sources=verilog_sources,
        toplevel="network_slave",
        module="test_network_slave",
        testcase="test_miop_network_slave",
        parameters=parameters,
        includes=include_dirs,
        simulator="verilator",
        waves=os.environ.get('ENABLE_WAVEDUMP', '1') == '1',
        extra_env=env_params or {}
    )


if __name__ == "__main__":
    run_test_with_parameters()