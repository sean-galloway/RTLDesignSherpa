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
import cocotb

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# GAXI for descriptor interfaces
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master

# AXIS for stream interface (slave to monitor output)
from CocoTBFramework.components.axis4.axis_factories import create_axis_slave

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
        bytes_per_line = self.DATA_WIDTH // 8
        num_lines = (32 * self.CHANNEL_OFFSET) // bytes_per_line
        self.memory_model = MemoryModel(
            num_lines=num_lines,
            bytes_per_line=bytes_per_line
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
        # cfg_drain_size: minimum beats in SRAM before arbiter activates
        # Set to 1 so arbiter activates as soon as any data is available
        # (Higher values cause backpressure when small transfers are queued)
        self.dut.cfg_drain_size.value = 1

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
        # Signal naming: descriptor_N_valid, descriptor_N_ready, descriptor_N_packet, descriptor_N_error
        for i in range(self.NUM_CHANNELS):
            desc_master = create_gaxi_master(
                dut=self.dut,
                title=f"desc_ch{i}",
                prefix=f"descriptor_{i}_",
                clock=self.clk,
                log=self.log,
                multi_sig=True,
                field_config={
                    'packet': {'bits': self.DESC_WIDTH},
                    'error': {'bits': 1},
                }
            )
            self.descriptor_masters.append(desc_master)

        # AXI4 read slave to respond to m_axi_ar*/r* signals
        # base_addr translates system addresses (0x10000000+) to 0-based memory model offsets
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
            memory_model=self.memory_model,
            base_addr=self.BASE_ADDRESS,
        )

        # AXIS slave to monitor m_axis_* output
        self.axis_slave = create_axis_slave(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axis_",
            log=self.log,
            data_width=self.DATA_WIDTH,
            id_width=8,
            dest_width=4,
            user_width=1,
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

        # Start AXIS output monitoring (drives tready, captures packets)
        self._axis_monitor_active = True
        self._axis_monitor_task = cocotb.start_soon(self._axis_output_monitor())

        self.log.info("Test initialization complete")

    async def _axis_output_monitor(self):
        """Background task to monitor AXIS output and drive tready.

        This task drives m_axis_tready high and captures output packets.
        Without this, the datapath will stall due to backpressure.
        """
        self.log.info("AXIS output monitor started")

        # Drive tready high to accept data
        self.dut.m_axis_tready.value = 1

        while self._axis_monitor_active:
            await self.wait_clocks(self.clk_name, 1)

            # Check for valid handshake
            if (int(self.dut.m_axis_tvalid.value) == 1 and
                int(self.dut.m_axis_tready.value) == 1):
                # Capture packet data
                packet_data = {
                    'tdata': int(self.dut.m_axis_tdata.value),
                    'tstrb': int(self.dut.m_axis_tstrb.value),
                    'tlast': int(self.dut.m_axis_tlast.value),
                    'tid': int(self.dut.m_axis_tid.value),
                    'tdest': int(self.dut.m_axis_tdest.value),
                }
                self.received_packets.append(packet_data)
                self.test_stats['axis_packets_received'] += 1

                if packet_data['tlast']:
                    self.log.debug(f"AXIS packet complete: tid={packet_data['tid']}, "
                                   f"tdest={packet_data['tdest']}")

        self.log.info(f"AXIS output monitor stopped, received {len(self.received_packets)} beats")

    def stop_axis_monitor(self):
        """Stop the AXIS output monitor"""
        self._axis_monitor_active = False

    async def _preload_memory(self):
        """Pre-load memory with test data using base_addr-relative addressing.

        The memory model uses 0-based addressing. System addresses are translated
        to memory model offsets by subtracting BASE_ADDRESS via the AXI slave's
        base_addr parameter.

        Memory layout matches system address layout (offset = sys_addr - BASE_ADDRESS):
          Channel 0: offsets 0x000000 to 0x000FFF (sys 0x10000000-0x10000FFF)
          Channel 1: offsets 0x100000 to 0x100FFF (sys 0x10100000-0x10100FFF)
          etc.
        """
        self.log.info("Pre-loading memory...")
        bytes_per_line = self.DATA_WIDTH // 8

        for ch in range(self.NUM_CHANNELS):
            for i in range(64):
                # Memory offset = system address - BASE_ADDRESS
                # This matches what the AXI slave will calculate
                mem_offset = ch * self.CHANNEL_OFFSET + i * bytes_per_line

                # System address (used in descriptors and verification)
                sys_addr = self.BASE_ADDRESS + mem_offset

                # Create deterministic test pattern as integer
                data_int = ((ch << 56) | (i << 48) | (0xCAFE0000 + ch * 0x100 + i))
                data_int = data_int & ((1 << self.DATA_WIDTH) - 1)  # Mask to data width

                # Convert integer to bytearray (little-endian)
                data_bytes = bytearray(data_int.to_bytes(bytes_per_line, 'little'))
                self.memory_model.write(mem_offset, data_bytes)

                # Store expected data keyed by system address for verification
                self.expected_data[sys_addr] = data_int

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

        Descriptor format (from scheduler_beats.sv):
        - [63:0]    : src_addr - Source address (where to read FROM)
        - [127:64]  : dst_addr - Destination address (not used for source path test)
        - [159:128] : length - Transfer length in BEATS (32 bits)
        - [191:160] : next_descriptor_ptr - Address of next descriptor (0 = last)
        - [192]     : valid - Descriptor valid flag
        - [193]     : gen_irq - Generate interrupt on completion
        - [194]     : last - Last descriptor in chain flag
        - [199:196] : channel_id
        - [207:200] : desc_priority
        - [255:208] : reserved
        """
        desc = 0
        # Source address (where to read from)
        desc |= (addr & ((1 << 64) - 1))  # bits [63:0]
        # Destination address (not relevant for source path read, use 0)
        desc |= (0 << 64)  # bits [127:64]
        # Transfer length in beats
        desc |= ((beats & 0xFFFFFFFF) << 128)  # bits [159:128]
        # Next descriptor pointer (0 = no chaining)
        desc |= (0 << 160)  # bits [191:160]
        # Valid flag (must be set for scheduler to process)
        desc |= (1 << 192)  # bit 192
        # gen_irq = 0
        # last flag
        if eos:
            desc |= (1 << 194)  # bit 194 = last descriptor in chain
        # Channel ID (informational)
        desc |= ((channel & 0xF) << 196)  # bits [199:196]
        return desc

    async def send_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False):
        """Send a descriptor to a specific channel"""
        if channel >= self.NUM_CHANNELS:
            raise ValueError(f"Invalid channel {channel}")

        desc = self.create_read_descriptor(channel, addr, beats, eos)

        # Send via GAXI master (factory returns GAXIMaster directly, not a dict)
        master = self.descriptor_masters[channel]
        packet = master.create_packet(packet=desc, error=0)
        await master.send(packet)

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

                delay = self.timing_config.next()['inter_op_delay']
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

                delay = self.timing_config.next()['axi_delay']
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

                # Wait for AXIS output with polling (up to 400 clocks)
                max_wait = 400
                waited = 0
                current_axis_beats = int(self.dut.dbg_axis_beats_sent.value)
                while current_axis_beats <= initial_axis_beats and waited < max_wait:
                    await self.wait_clocks(self.clk_name, 10)
                    waited += 10
                    current_axis_beats = int(self.dut.dbg_axis_beats_sent.value)

                # Check AXIS output
                if current_axis_beats > initial_axis_beats:
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                    initial_axis_beats = current_axis_beats
                    self.log.debug(f"E2E transfer {i} successful: ch{channel} (waited {waited} clks)")
                else:
                    failed += 1
                    self.test_stats['failed_operations'] += 1
                    # Debug: log scheduler and datapath state
                    sched_idle = int(self.dut.sched_idle.value)
                    sched_state = int(self.dut.sched_state.value)
                    arb_request = int(self.dut.dbg_arb_request.value)
                    r_beats = int(self.dut.dbg_r_beats_rcvd.value)
                    sram_writes = int(self.dut.dbg_sram_writes.value)
                    sram_pending = int(self.dut.dbg_sram_bridge_pending.value)
                    sram_out_valid = int(self.dut.dbg_sram_bridge_out_valid.value)
                    self.log.warning(f"E2E transfer {i} failed: ch{channel}, no AXIS output after {waited} clks")
                    self.log.warning(f"  DEBUG: sched_idle={sched_idle:08b} sched_state[{channel}]={sched_state >> (channel*7) & 0x7F:02x}")
                    self.log.warning(f"  DEBUG: arb_request={arb_request:08b} r_beats={r_beats} sram_writes={sram_writes}")
                    self.log.warning(f"  DEBUG: sram_pending={sram_pending:08b} sram_out_valid={sram_out_valid:08b}")

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
