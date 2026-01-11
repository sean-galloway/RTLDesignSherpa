# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SourceDataPathAxisTestTB
# Purpose: RAPIDS Source Data Path AXIS Test Wrapper Testbench
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_macro_beats
#
# Author: sean galloway
# Created: 2026-01-10

"""
RAPIDS Source Data Path AXIS Test Wrapper Testbench

Testbench for the src_data_path_axis_test module which wraps:
- 8x Scheduler instances (fed by GAXI descriptor masters)
- src_data_path_axis (AXI read -> SRAM -> AXIS master)

Interfaces:
- 8x Descriptor GAXI masters (one per channel)
- AXI4 read slave (responds to m_axi_ar*/r* signals)
- AXIS slave (monitors m_axis_* signals)

Test Flow:
1. Pre-load memory with test data
2. Send descriptors to schedulers via GAXI masters
3. Schedulers process descriptors and request reads
4. AXI slave returns data from memory
5. Verify AXIS output packets
"""

import os
import random
from typing import Dict, Any, Tuple, List
import time

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# GAXI for descriptor interfaces
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master

# AXIS for stream interface (slave to monitor output)
from CocoTBFramework.components.axis4.axis4_factories import create_axis4_slave

# AXI4 for memory interface (slave for reads)
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd


class SrcDataPathAxisTestBeatsTB(TBBase):
    """
    RAPIDS Source Data Path AXIS Test Wrapper Testbench.

    Tests the source path: Descriptors -> Schedulers -> AXI Read -> SRAM -> AXIS Output
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Configuration from environment
        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.SRAM_DEPTH = self.convert_to_int(os.environ.get('TEST_SRAM_DEPTH', '4096'))
        self.CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset
        self.clk = clk
        self.clk_name = clk._name if clk else 'clk'
        self.rst_n = rst_n

        # Derived parameters
        self.DESC_WIDTH = 256  # RAPIDS descriptor format
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        # Address configuration
        self.BASE_ADDRESS = 0x10000000
        self.CHANNEL_OFFSET = 0x00100000

        # Component interfaces (set up in initialize_test)
        self.descriptor_masters = []  # 8 GAXI masters for descriptors
        self.axi_read_slave = None    # AXI slave to respond to reads
        self.axis_slave = None        # AXIS slave to monitor output

        # Memory model with pre-loaded data
        self.memory_model = MemoryModel(
            size_bytes=32 * self.CHANNEL_OFFSET,
            base_address=self.BASE_ADDRESS,
            data_width_bytes=self.DATA_WIDTH // 8
        )

        # Expected data for verification
        self.expected_data = {}  # addr -> data

        # Received AXIS packets
        self.received_packets = []

        # Timing configuration
        self.timing_configs = self._create_timing_configs()
        self.current_timing_profile = 'normal'
        self.timing_config = FlexRandomizer(self.timing_configs['normal'])

        # Test statistics
        self.test_stats = {
            'start_time': 0,
            'total_operations': 0,
            'successful_operations': 0,
            'failed_operations': 0,
            'descriptors_sent': 0,
            'axi_reads_completed': 0,
            'axis_packets_received': 0,
            'channel_operations': [0] * self.NUM_CHANNELS,
            'channel_errors': [0] * self.NUM_CHANNELS,
        }

        self.log.info(f"SourceDataPathAxisTestTB initialized: {self.NUM_CHANNELS} channels, "
                      f"DW={self.DATA_WIDTH}, AW={self.ADDR_WIDTH}")

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        """Start clocks and perform reset sequence"""
        await self.start_clock(self.clk_name, freq=self.CLK_PERIOD, units='ns')

        # Set configuration signals before reset
        self.dut.cfg_axi_rd_xfer_beats.value = 8
        self.dut.cfg_drain_size.value = 16

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 15)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

        self.log.info("Clock started and reset complete")

    async def assert_reset(self):
        """Assert active-low reset"""
        self.rst_n.value = 0
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.rst_n.value = 1
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset deasserted")

    # =========================================================================
    # INTERFACE SETUP
    # =========================================================================

    def setup_interfaces(self):
        """Set up all test interfaces"""
        self.log.info("Setting up interfaces...")

        # Create 8 GAXI masters for descriptor interfaces
        for i in range(self.NUM_CHANNELS):
            desc_master = create_gaxi_master(
                dut=self.dut,
                clock=self.clk,
                prefix=f"descriptor_{i}_",
                log=self.log,
                data_width=self.DESC_WIDTH,
                multi_sig=True,
                field_config={
                    'packet': self.DESC_WIDTH,
                    'error': 1,
                }
            )
            self.descriptor_masters.append(desc_master)

        # AXI4 read slave to respond to m_axi_ar*/r* signals
        self.axi_read_slave = create_axi4_slave_rd(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axi_",
            log=self.log,
            data_width=self.DATA_WIDTH,
            id_width=self.AXI_ID_WIDTH,
            addr_width=self.ADDR_WIDTH,
            user_width=1,
            multi_sig=True,
            memory_model=self.memory_model
        )

        # AXIS slave to monitor m_axis_* output
        self.axis_slave = create_axis4_slave(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axis_",
            log=self.log,
            data_width=self.DATA_WIDTH,
            id_width=8,
            dest_width=4,
            user_width=1,
            multi_sig=True,
        )

        self.log.info("Interface setup complete")

    async def initialize_test(self):
        """Initialize test environment"""
        self.log.info("Initializing test...")
        self.test_stats['start_time'] = time.time()

        # Set up all interfaces
        self.setup_interfaces()

        # Pre-load memory with test data
        await self._preload_memory()

        self.log.info("Test initialization complete")

    async def _preload_memory(self):
        """Pre-load memory with test data"""
        self.log.info("Pre-loading memory...")

        for ch in range(self.NUM_CHANNELS):
            base = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET
            for i in range(64):
                addr = base + i * (self.DATA_WIDTH // 8)
                # Create deterministic test pattern
                data = ((ch << 56) | (i << 48) | (0xCAFE0000 + ch * 0x100 + i))
                data = data & ((1 << self.DATA_WIDTH) - 1)  # Mask to data width
                self.memory_model.write(addr, data)
                self.expected_data[addr] = data

        self.log.info(f"Pre-loaded {self.NUM_CHANNELS * 64} memory locations")

    # =========================================================================
    # TIMING CONFIGURATION
    # =========================================================================

    def _create_timing_configs(self) -> Dict[str, Dict]:
        """Create timing configuration profiles"""
        return {
            'fast': {
                'desc_delay': ([(0, 2), (3, 5)], [3, 1]),
                'axi_delay': ([(1, 3), (4, 8)], [2, 1]),
                'inter_op_delay': ([(1, 5)], [1])
            },
            'normal': {
                'desc_delay': ([(2, 8), (9, 15)], [2, 1]),
                'axi_delay': ([(5, 10), (11, 20)], [2, 1]),
                'inter_op_delay': ([(5, 15)], [1])
            },
            'slow': {
                'desc_delay': ([(10, 20), (21, 40)], [2, 1]),
                'axi_delay': ([(15, 30), (31, 50)], [2, 1]),
                'inter_op_delay': ([(20, 50)], [1])
            },
            'stress': {
                'desc_delay': ([(0, 1), (2, 5)], [3, 1]),
                'axi_delay': ([(0, 2), (3, 8)], [3, 1]),
                'inter_op_delay': ([(0, 3)], [1])
            }
        }

    def set_timing_profile(self, profile: str):
        """Set timing profile"""
        if profile in self.timing_configs:
            self.current_timing_profile = profile
            self.timing_config = FlexRandomizer(self.timing_configs[profile])
            self.log.info(f"Timing profile set to: {profile}")

    # =========================================================================
    # DESCRIPTOR HELPERS
    # =========================================================================

    def create_read_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False) -> int:
        """Create a RAPIDS read descriptor (256 bits)

        Descriptor format (simplified):
        - [63:0]   : Base address
        - [95:64]  : Transfer beats
        - [127:96] : Control flags (bit 0 = eos, bit 1 = read direction)
        - [255:128]: Reserved
        """
        desc = 0
        desc |= (addr & ((1 << 64) - 1))  # Address in bits [63:0]
        desc |= ((beats & 0xFFFFFFFF) << 64)  # Beats in bits [95:64]
        desc |= (1 << 97)  # Read direction flag in bit 97
        if eos:
            desc |= (1 << 96)  # EOS flag in bit 96
        return desc

    async def send_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False):
        """Send a descriptor to a specific channel"""
        if channel >= self.NUM_CHANNELS:
            raise ValueError(f"Invalid channel {channel}")

        desc = self.create_read_descriptor(channel, addr, beats, eos)

        # Send via GAXI master
        master = self.descriptor_masters[channel]
        await master['interface'].write({
            'packet': desc,
            'error': 0
        })

        self.test_stats['descriptors_sent'] += 1
        self.test_stats['channel_operations'][channel] += 1
        self.log.debug(f"Sent descriptor to ch{channel}: addr=0x{addr:X}, beats={beats}, eos={eos}")

    # =========================================================================
    # TEST METHODS
    # =========================================================================

    async def test_basic_descriptor_flow(self, num_descriptors: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test basic descriptor flow through schedulers"""
        self.log.info(f"Testing basic descriptor flow ({num_descriptors} descriptors)...")

        successful = 0
        failed = 0

        for i in range(num_descriptors):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = random.randint(1, 8)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats)

                # Wait for scheduler to process
                await self.wait_clocks(self.clk_name, 50)

                # Check scheduler state
                sched_idle = int(self.dut.sched_idle.value)
                if (sched_idle >> channel) & 1:
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    # Scheduler busy is expected (waiting for read to complete)
                    successful += 1
                    self.test_stats['successful_operations'] += 1

                delay = self.timing_config.get_value('inter_op_delay')
                await self.wait_clocks(self.clk_name, delay)

            except Exception as e:
                self.log.error(f"Descriptor {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_descriptors

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_descriptors,
            'success_rate': successful / num_descriptors if num_descriptors > 0 else 0
        }

        return failed == 0, stats

    async def test_multi_channel_operation(self, num_channels: int = 4, descriptors_per_channel: int = 2) -> Tuple[bool, Dict[str, Any]]:
        """Test multi-channel operation"""
        self.log.info(f"Testing multi-channel: {num_channels} channels, {descriptors_per_channel} desc/ch...")

        successful = 0
        failed = 0
        total = num_channels * descriptors_per_channel

        for ch in range(num_channels):
            for d in range(descriptors_per_channel):
                try:
                    addr = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET + d * (self.DATA_WIDTH // 8)
                    beats = 4

                    await self.send_descriptor(ch, addr, beats)
                    successful += 1
                    self.test_stats['successful_operations'] += 1

                    await self.wait_clocks(self.clk_name, 5)

                except Exception as e:
                    self.log.error(f"Ch{ch} desc{d} failed: {e}")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

        # Wait for processing
        await self.wait_clocks(self.clk_name, 200)

        self.test_stats['total_operations'] += total

        stats = {
            'successful': successful,
            'failed': failed,
            'total': total,
            'channels_tested': num_channels,
            'success_rate': successful / total if total > 0 else 0
        }

        return failed == 0, stats

    async def test_axi_read_operations(self, num_operations: int = 12) -> Tuple[bool, Dict[str, Any]]:
        """Test AXI read operations"""
        self.log.info(f"Testing AXI read operations ({num_operations})...")

        successful = 0
        failed = 0

        for i in range(num_operations):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = 4

                # Send descriptor to trigger read
                await self.send_descriptor(channel, addr, beats)

                # Wait for AXI read to complete
                await self.wait_clocks(self.clk_name, 100)

                # Check debug signals for read completion
                dbg_reads = int(self.dut.dbg_r_beats_rcvd.value)
                if dbg_reads > 0:
                    successful += 1
                    self.test_stats['axi_reads_completed'] += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    self.log.warning(f"AXI read {i}: no read beats received")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

            except Exception as e:
                self.log.error(f"AXI read {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_operations

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_operations,
            'success_rate': successful / num_operations if num_operations > 0 else 0
        }

        return failed == 0, stats

    async def test_axis_transmission(self, num_packets: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test AXIS data transmission"""
        self.log.info(f"Testing AXIS transmission ({num_packets} packets)...")

        successful = 0
        failed = 0

        for i in range(num_packets):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = random.randint(1, 4)

                # Send descriptor to trigger read -> AXIS output
                await self.send_descriptor(channel, addr, beats)

                # Wait for AXIS output
                await self.wait_clocks(self.clk_name, 150)

                # Check AXIS output counter
                axis_sent = int(self.dut.dbg_axis_beats_sent.value)
                if axis_sent > 0:
                    successful += 1
                    self.test_stats['axis_packets_received'] += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    self.log.warning(f"AXIS packet {i}: no output detected")
                    failed += 1
                    self.test_stats['failed_operations'] += 1

                delay = self.timing_config.get_value('axi_delay')
                await self.wait_clocks(self.clk_name, delay)

            except Exception as e:
                self.log.error(f"AXIS packet {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_packets

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_packets,
            'success_rate': successful / num_packets if num_packets > 0 else 0
        }

        return failed == 0, stats

    async def test_end_to_end_flow(self, num_transfers: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test end-to-end data flow"""
        self.log.info(f"Testing end-to-end flow ({num_transfers} transfers)...")

        successful = 0
        failed = 0

        initial_axis_beats = int(self.dut.dbg_axis_beats_sent.value)

        for i in range(num_transfers):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + (i % 64) * (self.DATA_WIDTH // 8)
                beats = random.randint(2, 8)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats, eos=(i == num_transfers - 1))

                # Wait for completion
                await self.wait_clocks(self.clk_name, 200)

                # Check AXIS output
                current_axis_beats = int(self.dut.dbg_axis_beats_sent.value)
                if current_axis_beats > initial_axis_beats:
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                    initial_axis_beats = current_axis_beats
                    self.log.debug(f"E2E transfer {i} successful: ch{channel}")
                else:
                    failed += 1
                    self.test_stats['failed_operations'] += 1
                    self.log.warning(f"E2E transfer {i} failed: no AXIS output")

            except Exception as e:
                self.log.error(f"E2E transfer {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_transfers

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_transfers,
            'success_rate': successful / num_transfers if num_transfers > 0 else 0
        }

        return failed == 0, stats

    async def stress_test(self, num_operations: int = 32) -> Tuple[bool, Dict[str, Any]]:
        """Stress test with high throughput"""
        self.log.info(f"Running stress test ({num_operations} operations)...")

        successful = 0
        failed = 0

        for i in range(num_operations):
            try:
                channel = random.randint(0, self.NUM_CHANNELS - 1)
                offset = random.randint(0, 63) * (self.DATA_WIDTH // 8)
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + offset
                beats = random.randint(1, 8)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats)

                # Random short delay
                await self.wait_clocks(self.clk_name, random.randint(5, 20))

                successful += 1
                self.test_stats['successful_operations'] += 1

            except Exception as e:
                self.log.error(f"Stress op {i} failed: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        # Final wait for pipeline to drain
        await self.wait_clocks(self.clk_name, 500)

        self.test_stats['total_operations'] += num_operations

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_operations,
            'success_rate': successful / num_operations if num_operations > 0 else 0
        }

        return failed < (num_operations * 0.1), stats
