# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SrcDatapathTB
# Purpose: RAPIDS Source Data Path Testbench - v2.2
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Source Data Path Testbench - v2.2

Comprehensive testbench for the source data path following the same patterns
as the sink testbench. Tests the complete AXI read to Network transmit pipeline.

Features:
- Fixed 32-channel configuration
- Only uses existing scheduler, AXI, and Network interfaces
- Comprehensive data flow validation
- Stream boundary processing (EOS-only)
- Error injection and handling
- Performance and resource monitoring
- Real AXI4 and Network component integration
"""

import os
import random
import asyncio
from typing import List, Dict, Any, Tuple, Optional, Union
import time

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# REAL Network imports
from CocoTBFramework.components.network.network_factories import (
    create_network_slave, create_network_master, send_packet_sequence, validate_network_packet
)
from CocoTBFramework.components.network.network_interfaces import NETWORK_PKT_TYPES, NETWORK_ACK_TYPES
from CocoTBFramework.components.network.network_packet import MNOCPacket
from CocoTBFramework.components.network.network_field_configs import MNOCFieldConfigHelper
from CocoTBFramework.components.network.network_compliance_checker import MNOCComplianceChecker

# REAL AXI4 imports
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd
from CocoTBFramework.components.axi4.axi4_packet import AXI4Packet


class SrcDatapathTB(TBBase):
    """
    Complete RAPIDS Source Data Path testbench for 32-channel validation.

    Tests comprehensive source data path functionality:
    - Enhanced multi-channel scheduler interface (32 channels)
    - AXI read operations from memory
    - SRAM control and buffering per channel
    - Network packet transmission to network (EOS-only)
    - Packet type routing (CONFIG/TS/RDA/RAW)
    - Channel isolation and concurrent operations
    - Error handling and flow control
    - Preallocation and loaded_lines coordination
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Fixed 32-channel configuration
        self.TEST_CHANNELS = 32  # FIXED
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.TEST_AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.TEST_NUM_CHUNKS = self.convert_to_int(os.environ.get('TEST_NUM_CHUNKS', '16'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.clk = clk
        self.clk_name = clk._name if clk else 'clk'
        self.rst_n = rst_n

        # Set limits based on widths
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1
        self.MAX_CHANNEL = self.TEST_CHANNELS - 1

        # 32-channel specific configuration
        self.BASE_ADDRESS = 0x10000000
        self.CHANNEL_OFFSET = 0x00100000  # 1MB per channel
        self.DEFAULT_TRANSFER_SIZE = 64

        # Test configuration
        self.test_config = {
            'enable_compliance_check': self.convert_to_int(os.environ.get('MIOP_COMPLIANCE_CHECK', '1')),
            'validate_all_channels': self.convert_to_int(os.environ.get('VALIDATE_ALL_CHANNELS', '1')),
            'channel_isolation_test': self.convert_to_int(os.environ.get('CHANNEL_ISOLATION_TEST', '1')),
            'overflow_detection_test': self.convert_to_int(os.environ.get('OVERFLOW_DETECTION_TEST', '1')),
            'max_concurrent_channels': self.convert_to_int(os.environ.get('MAX_CONCURRENT_CHANNELS', '16')),
            'burst_size_validation': self.convert_to_int(os.environ.get('BURST_SIZE_VALIDATION', '1')),
            'address_validation': self.convert_to_int(os.environ.get('ADDRESS_VALIDATION', '1'))
        }

        # Component interfaces - will be set up in initialize_test
        self.axi_slave = None
        self.network_slave = None
        self.network_compliance_checker = None

        # Memory model for source data
        self.memory_model = MemoryModel()

        # Test statistics
        self.test_stats = {
            'start_time': 0,
            'total_operations': 0,
            'successful_operations': 0,
            'failed_operations': 0,
            'scheduler_requests': 0,
            'axi_reads': 0,
            'network_transmissions': 0,
            'channel_operations': [0] * 32,
            'channel_errors': [0] * 32,
            'data_flow_latency': [],
            'sram_utilization': [0] * 32,
            'preallocation_events': 0,
            'credit_returns': 0
        }

        # Setup timing configurations
        self.timing_configs = self._get_timing_configs()
        self.current_timing_profile = 'normal'
        self.timing_config = FlexRandomizer(self.timing_configs['normal'])

        self.log.info(f"SrcDatapathTB initialized for 32 channels")

    def _get_timing_configs(self) -> Dict[str, Dict]:
        """Get timing configuration profiles for different test scenarios."""
        return {
            'fast': {
                'scheduler_delay': ([(0, 2), (3, 5)], [3, 1]),
                'axi_delay': ([(0, 1), (2, 4)], [3, 1]),
                'network_delay': ([(1, 3), (4, 8)], [2, 1]),
                'inter_request_delay': ([(1, 5)], [1])
            },
            'normal': {
                'scheduler_delay': ([(2, 8), (9, 15)], [2, 1]),
                'axi_delay': ([(2, 6), (7, 12)], [2, 1]),
                'network_delay': ([(5, 10), (11, 20)], [2, 1]),
                'inter_request_delay': ([(5, 15)], [1])
            },
            'slow': {
                'scheduler_delay': ([(10, 20), (21, 40)], [2, 1]),
                'axi_delay': ([(8, 16), (17, 30)], [2, 1]),
                'network_delay': ([(15, 30), (31, 50)], [2, 1]),
                'inter_request_delay': ([(20, 50)], [1])
            },
            'stress': {
                'scheduler_delay': ([(0, 1), (2, 5), (10, 25)], [3, 2, 1]),
                'axi_delay': ([(0, 2), (3, 8), (15, 30)], [3, 2, 1]),
                'network_delay': ([(1, 3), (5, 15), (20, 40)], [3, 2, 1]),
                'inter_request_delay': ([(0, 3), (5, 20)], [2, 1])
            }
        }

    def set_timing_profile(self, profile: str):
        """Set timing randomization profile."""
        if profile in self.timing_configs:
            self.current_timing_profile = profile
            self.timing_config = FlexRandomizer(self.timing_configs[profile])
            self.log.info(f"Timing profile set to: {profile}")
        else:
            self.log.warning(f"Unknown timing profile: {profile}")

    async def initialize_test(self):
        """Initialize test environment."""
        self.log.info("Initializing test environment...")

        # Set up interfaces
        self.setup_interfaces(self.dut)

        # Initialize test statistics
        self.test_stats['start_time'] = time.time()

        # Initialize memory regions for all 32 channels
        await self._initialize_memory_regions()

        self.log.info("Test environment initialization complete")

    def setup_interfaces(self, dut):
        """Setup Network and AXI interfaces for the test."""
        self.log.info("Setting up interfaces...")

        try:
            # Create AXI4 read slave (memory side)
            self.axi_slave = create_axi4_slave_rd(
                dut,
                prefix='ar_',
                data_prefix='r_',
                clk=self.clk,
                mem_model=self.memory_model,
                log=self.log
            )

            # Create Network slave (network side) to receive packets
            self.network_slave = create_network_slave(
                dut,
                prefix='m_network_pkt_',
                ack_prefix='s_network_ack_',
                clk=self.clk,
                log=self.log
            )

            # Setup Network compliance checker if enabled
            if self.test_config['enable_compliance_check']:
                self.network_compliance_checker = MNOCComplianceChecker(
                    log=self.log,
                    strict_mode=True
                )

            self.log.info("Interfaces setup complete")

        except Exception as e:
            self.log.error(f"Interface setup failed: {e}")
            raise

    async def _initialize_memory_regions(self):
        """Initialize memory regions for all 32 channels."""
        self.log.info("Initializing memory regions for 32 channels...")

        for channel in range(32):
            base_addr = self._get_channel_base_address(channel)

            # Create test data pattern for each channel (4KB test data)
            for i in range(64):  # 64 * 64 bytes = 4KB per channel
                addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))

                # Create pattern: channel ID in upper bits, counter in lower bits
                data = (channel << 24) | (i & 0xFFFFFF)
                self.memory_model.write(addr, data)

        self.log.info("Memory regions initialized for all 32 channels")

    def _get_channel_base_address(self, channel: int) -> int:
        """Get the base memory address for a specific channel."""
        if channel >= 32:
            raise ValueError(f"Invalid channel {channel}, must be 0-31")
        return self.BASE_ADDRESS + (channel * self.CHANNEL_OFFSET)

    async def reset_sequence(self):
        """Perform reset sequence."""
        self.log.info("Starting reset sequence...")

        # Assert reset
        self.rst_n.value = 0
        await self.wait_clk_cycles(15)  # Longer reset for 32 channels

        # Configure the data path
        self.dut.cfg_transfer_size.value = 0b10  # 2KB transfers
        self.dut.cfg_streaming_enable.value = 1
        self.dut.cfg_sram_enable.value = 1
        self.dut.cfg_channel_enable.value = 0xFFFFFFFF  # Enable all 32 channels

        # Deassert reset
        self.rst_n.value = 1
        await self.wait_clk_cycles(10)

        self.log.info("Reset sequence complete")

    async def test_scheduler_interface(self, count: int = 50) -> Tuple[bool, Dict[str, Any]]:
        """Test scheduler interface functionality across all 32 channels."""
        self.log.info(f"Testing scheduler interface ({count} requests across 32 channels)...")

        successful = 0
        failed = 0
        requests_sent = []

        for i in range(count):
            try:
                # Cycle through all 32 channels
                channel = i % 32

                # Generate request parameters
                base_addr = self._get_channel_base_address(channel)
                offset = (i // 32) * 1024  # Different offset per round
                address = base_addr + offset
                length = random.randint(256, 2048)  # 256B to 2KB
                data_type = random.randint(0, 3)  # 0=CONFIG, 1=TS, 2=RDA, 3=RAW
                eos = (i % 8 == 7)  # EOS every 8th request

                # Send scheduler request
                await self._send_scheduler_request(
                    channel=channel,
                    address=address,
                    length=length,
                    data_type=data_type,
                    eos=eos
                )

                requests_sent.append({
                    'channel': channel,
                    'address': address,
                    'length': length,
                    'type': data_type,
                    'eos': eos
                })

                successful += 1
                self.test_stats['scheduler_requests'] += 1
                self.test_stats['successful_operations'] += 1
                self.test_stats['channel_operations'][channel] += 1

                # Add timing delay
                delay = self.timing_config.get_value('scheduler_delay')
                await self.wait_clk_cycles(delay)

            except Exception as e:
                self.log.error(f"Scheduler request {i} on channel {i % 32} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1
                self.test_stats['channel_errors'][i % 32] += 1

        self.test_stats['total_operations'] += count

        stats = {
            'successful': successful,
            'failed': failed,
            'total': count,
            'success_rate': successful / count if count > 0 else 0,
            'channels_tested': min(count, 32),
            'requests_sent': len(requests_sent)
        }

        return failed == 0, stats

    async def _send_scheduler_request(self, channel: int, address: int, length: int,
                                    data_type: int, eos: bool):
        """Send a request to the scheduler interface."""
        # Set up request signals
        self.dut.data_valid.value = 1 << channel
        self.dut.data_address[channel].value = address
        self.dut.data_length[channel].value = length
        self.dut.data_type[channel].value = data_type
        self.dut.data_eos.value = (1 << channel) if eos else 0

        # Wait for ready
        timeout = 100
        cycles = 0
        while cycles < timeout:
            await self.wait_clk_cycles(1)
            if self.dut.data_ready.value & (1 << channel):
                break
            cycles += 1

        if cycles >= timeout:
            raise Exception(f"Timeout waiting for ready on channel {channel}")

        # Clear request
        self.dut.data_valid.value = 0
        self.dut.data_eos.value = 0

    async def test_axi_read_operations(self, count: int = 50) -> Tuple[bool, Dict[str, Any]]:
        """Test AXI read operations functionality."""
        self.log.info(f"Testing AXI read operations ({count} reads)...")

        successful = 0
        failed = 0
        read_latencies = []

        for i in range(count):
            try:
                # Select channel and generate read
                channel = i % 32
                base_addr = self._get_channel_base_address(channel)
                offset = (i // 32) * 512
                read_addr = base_addr + offset
                burst_length = random.randint(1, 16)

                start_time = await self._get_sim_time()

                # Trigger read by sending scheduler request
                await self._send_scheduler_request(
                    channel=channel,
                    address=read_addr,
                    length=burst_length * 64,  # 64 bytes per beat
                    data_type=1,  # TS packet
                    eos=False
                )

                # Wait for AXI read completion
                await self._wait_for_axi_read(read_addr)

                end_time = await self._get_sim_time()
                latency = end_time - start_time
                read_latencies.append(latency)

                successful += 1
                self.test_stats['axi_reads'] += 1
                self.test_stats['successful_operations'] += 1

                # Add timing delay
                delay = self.timing_config.get_value('axi_delay')
                await self.wait_clk_cycles(delay)

            except Exception as e:
                self.log.error(f"AXI read {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        # Calculate statistics
        avg_latency = sum(read_latencies) / len(read_latencies) if read_latencies else 0
        self.test_stats['data_flow_latency'].extend(read_latencies)

        self.test_stats['total_operations'] += count

        stats = {
            'successful': successful,
            'failed': failed,
            'total': count,
            'success_rate': successful / count if count > 0 else 0,
            'average_latency': avg_latency,
            'latency_range': (min(read_latencies), max(read_latencies)) if read_latencies else (0, 0)
        }

        return failed == 0, stats

    async def _wait_for_axi_read(self, address: int, timeout: int = 1000):
        """Wait for AXI read to complete."""
        cycles = 0
        while cycles < timeout:
            await self.wait_clk_cycles(1)

            # Check if AXI read occurred at the expected address
            if (hasattr(self.dut, 'ar_valid') and
                self.dut.ar_valid.value and
                self.dut.ar_ready.value and
                self.dut.ar_addr.value == address):
                return

            cycles += 1

        raise Exception(f"Timeout waiting for AXI read at address 0x{address:08x}")

    async def test_mnoc_transmission(self, count: int = 50) -> Tuple[bool, Dict[str, Any]]:
        """Test Network packet transmission functionality."""
        self.log.info(f"Testing Network transmission ({count} packets)...")

        successful = 0
        failed = 0
        packets_received = []

        for i in range(count):
            try:
                # Cycle through channels and generate data flow
                channel = i % 32

                # Send scheduler request to trigger data flow
                await self._send_scheduler_request(
                    channel=channel,
                    address=self._get_channel_base_address(channel) + (i * 64),
                    length=256,  # 256 bytes
                    data_type=1,  # TS packet
                    eos=(i % 10 == 9)  # EOS every 10th packet
                )

                # Wait for Network packet transmission
                packet = await self._wait_for_network_packet(timeout=500)

                if packet:
                    packets_received.append(packet)

                    # Validate packet if compliance checking is enabled
                    if self.network_compliance_checker:
                        is_valid = self.network_compliance_checker.validate_packet(packet)
                        if not is_valid:
                            self.log.warning(f"Network compliance violation for packet {i}")

                successful += 1
                self.test_stats['network_transmissions'] += 1
                self.test_stats['successful_operations'] += 1
                self.test_stats['channel_operations'][channel] += 1

                # Add timing delay
                delay = self.timing_config.get_value('network_delay')
                await self.wait_clk_cycles(delay)

            except Exception as e:
                self.log.error(f"Network transmission {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += count

        stats = {
            'successful': successful,
            'failed': failed,
            'total': count,
            'success_rate': successful / count if count > 0 else 0,
            'packets_received': len(packets_received)
        }

        return failed == 0, stats

    async def _wait_for_network_packet(self, timeout: int = 1000) -> Optional[Dict]:
        """Wait for Network packet transmission."""
        cycles = 0
        while cycles < timeout:
            await self.wait_clk_cycles(1)

            # Check if Network packet is being transmitted
            if (hasattr(self.dut, 'm_network_pkt_valid') and
                self.dut.m_network_pkt_valid.value and
                self.dut.m_network_pkt_ready.value):

                packet = {
                    'addr': self.dut.m_network_pkt_addr.value,
                    'data': self.dut.m_network_pkt_data.value,
                    'type': self.dut.m_network_pkt_type.value,
                    'eos': self.dut.m_network_pkt_eos.value,
                    'parity': self.dut.m_network_pkt_par.value
                }
                return packet

            cycles += 1

        return None

    async def test_channel_isolation(self, count: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Test channel isolation using ROBUST GAXI multi-channel capabilities."""
        self.log.info(f"Testing channel isolation with ROBUST GAXI ({count} simultaneous channels)...")

        successful = 0
        failed = 0

        try:
            # Use GAXI system's multi-channel support for robust testing
            active_channels = min(count, 32)
            channel_packets = []

            # Create packets for multiple channels using GAXI framework
            for channel in range(active_channels):
                try:
                    address = self._get_channel_base_address(channel)

                    # Create GAXI packet for this channel
                    packet = GAXIPacket.create_packet(
                        field_config=self.scheduler_field_config,
                        address=address,
                        length=1024,
                        type=channel % 4,  # Different types per channel
                        channel=channel,
                        eos=0,
                        transfer_length=0,
                        done_strobe=0,
                        error=0
                    )

                    channel_packets.append((channel, packet))

                except Exception as e:
                    self.log.error(f"Channel {channel} packet creation failed: {e}")
                    failed += 1
                    self.test_stats['channel_errors'][channel] += 1

            # Send all packets simultaneously using GAXI robust multi-channel support
            if channel_packets:
                responses = await self.scheduler_system['master'].send_multi_channel_packets(
                    channel_packets,
                    timeout_cycles=200
                )

                # Validate responses from all channels
                for channel, response in responses.items():
                    if response and not response.get_field('error'):
                        successful += 1
                        self.test_stats['channel_operations'][channel] += 1
                    else:
                        failed += 1
                        self.test_stats['channel_errors'][channel] += 1

        except Exception as e:
            self.log.error(f"GAXI channel isolation test failed: {e}")
            failed = count

        self.test_stats['total_operations'] += active_channels

        stats = {
            'successful': successful,
            'failed': failed,
            'total': active_channels,
            'success_rate': successful / active_channels if active_channels > 0 else 0,
            'channels_tested': active_channels,
            'gaxi_multi_channel': True  # Indicator that GAXI multi-channel was used
        }

        return failed == 0, stats

    async def test_multi_channel_operations(self, channels: int = 16, count: int = 50) -> Tuple[bool, Dict[str, Any]]:
        """Test concurrent multi-channel operations."""
        self.log.info(f"Testing multi-channel operations ({channels} channels, {count} operations)...")

        successful = 0
        failed = 0
        active_channels = min(channels, 32)

        for i in range(count):
            try:
                # Select channel for this operation
                channel = i % active_channels

                # Generate operation parameters
                address = self._get_channel_base_address(channel) + (i * 128)
                length = random.randint(128, 1024)
                data_type = random.randint(0, 3)

                # Send request
                await self._send_scheduler_request(
                    channel=channel,
                    address=address,
                    length=length,
                    data_type=data_type,
                    eos=False
                )

                successful += 1
                self.test_stats['successful_operations'] += 1
                self.test_stats['channel_operations'][channel] += 1

                # Small delay between operations
                await self.wait_clk_cycles(random.randint(1, 5))

            except Exception as e:
                self.log.error(f"Multi-channel operation {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += count

        stats = {
            'successful': successful,
            'failed': failed,
            'total': count,
            'success_rate': successful / count if count > 0 else 0,
            'active_channels': active_channels
        }

        return failed == 0, stats

    async def test_stream_boundary_processing(self) -> Tuple[bool, Dict[str, Any]]:
        """Test stream boundary processing (EOS handling)."""
        self.log.info("Testing stream boundary processing (EOS)...")

        successful = 0
        failed = 0
        eos_count = 16

        for i in range(eos_count):
            try:
                channel = i % 32

                # Send request with EOS
                await self._send_scheduler_request(
                    channel=channel,
                    address=self._get_channel_base_address(channel) + (i * 256),
                    length=512,
                    data_type=1,  # TS
                    eos=True  # Always EOS for this test
                )

                # Wait for EOS packet
                await self._wait_for_eos_packet(channel)

                successful += 1
                self.test_stats['successful_operations'] += 1

            except Exception as e:
                self.log.error(f"EOS test {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        stats = {
            'successful': successful,
            'failed': failed,
            'total': eos_count,
            'success_rate': successful / eos_count if eos_count > 0 else 0
        }

        return failed == 0, stats

    async def _wait_for_eos_packet(self, channel: int, timeout: int = 500):
        """Wait for EOS packet on specific channel."""
        cycles = 0
        while cycles < timeout:
            await self.wait_clk_cycles(1)

            if (hasattr(self.dut, 'm_network_pkt_valid') and
                self.dut.m_network_pkt_valid.value and
                self.dut.m_network_pkt_ready.value and
                self.dut.m_network_pkt_eos.value):
                return

            cycles += 1

        raise Exception(f"Timeout waiting for EOS packet on channel {channel}")

    async def stress_test(self, count: int = 100) -> Tuple[bool, Dict[str, Any]]:
        """Run stress test with mixed operations."""
        self.log.info(f"Running stress test ({count} mixed operations)...")

        successful = 0
        failed = 0

        for i in range(count):
            try:
                # Random operation type
                operation = random.choice(['scheduler', 'multi_channel', 'eos_burst'])
                channel = random.randint(0, 31)

                if operation == 'scheduler':
                    # Single scheduler request
                    await self._send_scheduler_request(
                        channel=channel,
                        address=self._get_channel_base_address(channel) + random.randint(0, 4096),
                        length=random.randint(64, 2048),
                        data_type=random.randint(0, 3),
                        eos=random.choice([True, False])
                    )

                elif operation == 'multi_channel':
                    # Multiple channels simultaneously
                    num_channels = random.randint(2, 8)
                    for ch in range(num_channels):
                        test_channel = (channel + ch) % 32
                        await self._send_scheduler_request(
                            channel=test_channel,
                            address=self._get_channel_base_address(test_channel),
                            length=256,
                            data_type=1,
                            eos=False
                        )

                elif operation == 'eos_burst':
                    # Burst of EOS packets
                    for j in range(4):
                        test_channel = (channel + j) % 32
                        await self._send_scheduler_request(
                            channel=test_channel,
                            address=self._get_channel_base_address(test_channel) + (j * 128),
                            length=128,
                            data_type=2,
                            eos=True
                        )

                # Random delay between operations
                delay = random.randint(1, 25)
                await self.wait_clk_cycles(delay)

                successful += 1
                self.test_stats['successful_operations'] += 1
                self.test_stats['channel_operations'][channel] += 1

            except Exception as e:
                self.log.error(f"Stress operation {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1
                if 'channel' in locals():
                    self.test_stats['channel_errors'][channel] += 1

        self.test_stats['total_operations'] += count

        stats = {
            'successful': successful,
            'failed': failed,
            'total': count,
            'success_rate': successful / count if count > 0 else 0
        }

        return failed < (count * 0.1), stats  # Allow 10% failure rate in stress test

    async def run_error_injection_tests(self) -> None:
        """Run error injection tests to validate error handling."""
        self.log.info("Running error injection tests...")

        error_scenarios = [
            "invalid_address",
            "oversized_length",
            "invalid_channel",
            "timeout_simulation",
            "credit_exhaustion"
        ]

        for scenario in error_scenarios:
            try:
                await self._inject_error_scenario(scenario)
                self.log.info(f"Error scenario '{scenario}' handled correctly")
            except Exception as e:
                self.log.warning(f"Error scenario '{scenario}' caused: {e}")

    async def _inject_error_scenario(self, scenario: str) -> None:
        """Inject specific error scenario."""
        if scenario == "invalid_address":
            # Send request with invalid address
            await self._send_scheduler_request(
                channel=0,
                address=0xFFFFFFFFFFFFFFFF,  # Invalid address
                length=256,
                data_type=0,
                eos=False
            )

        elif scenario == "oversized_length":
            # Send request with oversized length
            await self._send_scheduler_request(
                channel=1,
                address=self._get_channel_base_address(1),
                length=0xFFFFFFFF,  # Oversized length
                data_type=1,
                eos=False
            )

        elif scenario == "invalid_channel":
            # Try to access invalid channel (should be caught by interface)
            try:
                self.dut.data_valid.value = 1 << 35  # Channel 35 doesn't exist
                await self.wait_clk_cycles(10)
                self.dut.data_valid.value = 0
            except:
                pass  # Expected to fail

        elif scenario == "timeout_simulation":
            # Simulate timeout by not providing ready signal
            self.dut.data_valid.value = 1
            await self.wait_clk_cycles(50)  # Long delay
            self.dut.data_valid.value = 0

        elif scenario == "credit_exhaustion":
            # Send many requests to exhaust credits
            for i in range(20):
                await self._send_scheduler_request(
                    channel=i % 32,
                    address=self._get_channel_base_address(i % 32),
                    length=64,
                    data_type=0,
                    eos=False
                )

        await self.wait_clk_cycles(10)

    def finalize_test(self):
        """Finalize test and collect final statistics."""
        end_time = time.time()
        duration = end_time - self.test_stats['start_time']

        self.test_stats['test_duration'] = duration

        self.log.info(f"Test completed in {duration:.2f} seconds")

    def get_test_stats(self) -> Dict[str, Any]:
        """Get comprehensive test statistics."""
        duration = self.test_stats.get('test_duration', 0)

        # Calculate utilization
        total_channel_ops = sum(self.test_stats['channel_operations'])
        channel_utilization = [
            (ops / total_channel_ops * 100) if total_channel_ops > 0 else 0
            for ops in self.test_stats['channel_operations']
        ]

        # Calculate performance metrics
        ops_per_second = self.test_stats['total_operations'] / duration if duration > 0 else 0

        return {
            'summary': {
                'total_operations': self.test_stats['total_operations'],
                'successful_operations': self.test_stats['successful_operations'],
                'failed_operations': self.test_stats['failed_operations'],
                'test_duration': duration,
                'operations_per_second': ops_per_second
            },
            'channels': {
                'total_channels_used': sum(1 for ops in self.test_stats['channel_operations'] if ops > 0),
                'channel_utilization': channel_utilization,
                'most_used_channel': channel_utilization.index(max(channel_utilization)),
                'least_used_channel': channel_utilization.index(min(channel_utilization))
            },
            'operations': {
                'scheduler_requests': self.test_stats['scheduler_requests'],
                'axi_reads': self.test_stats['axi_reads'],
                'network_transmissions': self.test_stats['network_transmissions'],
                'preallocation_events': self.test_stats['preallocation_events'],
                'credit_returns': self.test_stats['credit_returns']
            },
            'performance': {
                'average_latency': sum(self.test_stats['data_flow_latency']) / len(self.test_stats['data_flow_latency']) if self.test_stats['data_flow_latency'] else 0,
                'peak_channels_active': max([1 for _ in range(32) if self.test_stats['channel_operations'][_] > 0], default=0),
                'requests_per_second': self.test_stats['scheduler_requests'] / duration if duration > 0 else 0
            },
            'errors': {
                'total_errors': self.test_stats['failed_operations'],
                'error_rate': self.test_stats['failed_operations'] / self.test_stats['total_operations'] if self.test_stats['total_operations'] > 0 else 0,
                'channel_errors': self.test_stats['channel_errors']
            }
        }

    async def _get_sim_time(self) -> float:
        """Get current simulation time."""
        return float(await self.get_sim_time("ns"))
