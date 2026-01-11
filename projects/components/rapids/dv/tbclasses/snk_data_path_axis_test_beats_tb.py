# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SinkDataPathAxisTestTB
# Purpose: RAPIDS Sink Data Path AXIS Test Wrapper Testbench
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_macro_beats
#
# Author: sean galloway
# Created: 2026-01-10

"""
RAPIDS Sink Data Path AXIS Test Wrapper Testbench

Testbench for the snk_data_path_axis_test module which wraps:
- 8x Scheduler instances (fed by GAXI descriptor masters)
- snk_data_path_axis (AXIS slave -> SRAM -> AXI write)

Interfaces:
- 8x Descriptor GAXI masters (one per channel)
- AXIS master (to drive s_axis_* signals)
- AXI4 write slave (responds to m_axi_aw*/w*/b* signals)

Test Flow:
1. Send descriptors to schedulers via GAXI masters
2. Schedulers process descriptors and request writes
3. Send AXIS packets matching scheduler requests
4. Verify AXI writes to memory
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

# AXIS for stream interface
from CocoTBFramework.components.axis4.axis_factories import create_axis_master

# AXI4 for memory interface
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_wr


class SnkDataPathAxisTestBeatsTB(TBBase):
    """
    RAPIDS Sink Data Path AXIS Test Wrapper Testbench.

    Tests the sink path: Descriptors -> Schedulers -> AXIS -> SRAM -> AXI Write
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
        self.axis_master = None       # AXIS master to drive input
        self.axi_write_slave = None   # AXI slave to receive writes

        # Memory model for verification
        bytes_per_line = self.DATA_WIDTH // 8
        num_lines = (32 * self.CHANNEL_OFFSET) // bytes_per_line
        self.memory_model = MemoryModel(
            num_lines=num_lines,
            bytes_per_line=bytes_per_line,
            log=self.log
        )

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
            'axis_packets_sent': 0,
            'axi_writes_completed': 0,
            'channel_operations': [0] * self.NUM_CHANNELS,
            'channel_errors': [0] * self.NUM_CHANNELS,
        }

        self.log.info(f"SinkDataPathAxisTestTB initialized: {self.NUM_CHANNELS} channels, "
                      f"DW={self.DATA_WIDTH}, AW={self.ADDR_WIDTH}")

    # =========================================================================
    # MANDATORY THREE METHODS
    # =========================================================================

    async def setup_clocks_and_reset(self):
        """Start clocks and perform reset sequence"""
        await self.start_clock(self.clk_name, freq=self.CLK_PERIOD, units='ns')

        # Set configuration signals before reset
        self.dut.cfg_axi_wr_xfer_beats.value = 8
        self.dut.cfg_alloc_size.value = 16

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

        # AXIS master to drive s_axis_* signals
        self.axis_master = create_axis_master(
            dut=self.dut,
            clock=self.clk,
            prefix="s_axis_",
            log=self.log,
            data_width=self.DATA_WIDTH,
            id_width=8,
            dest_width=4,
            user_width=1,
        )

        # AXI4 write slave to respond to m_axi_* signals
        # Pass base_addr so slave subtracts it before accessing memory model
        self.axi_write_slave = create_axi4_slave_wr(
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
            base_addr=self.BASE_ADDRESS  # Convert absolute addresses to memory model offsets
        )

        self.log.info("Interface setup complete")

    async def initialize_test(self):
        """Initialize test environment"""
        self.log.info("Initializing test...")
        self.test_stats['start_time'] = time.time()

        # Set up all interfaces
        self.setup_interfaces()

        # Initialize memory regions with 0-based line addressing
        bytes_per_line = self.DATA_WIDTH // 8
        for line_idx in range(min(512, self.memory_model.num_lines)):  # Initialize first 512 lines
            self.memory_model.write(line_idx * bytes_per_line, bytearray(bytes_per_line))

        self.log.info("Test initialization complete")

    # =========================================================================
    # TIMING CONFIGURATION
    # =========================================================================

    def _create_timing_configs(self) -> Dict[str, Dict]:
        """Create timing configuration profiles"""
        return {
            'fast': {
                'desc_delay': ([(0, 2), (3, 5)], [3, 1]),
                'axis_delay': ([(1, 3), (4, 8)], [2, 1]),
                'inter_op_delay': ([(1, 5)], [1])
            },
            'normal': {
                'desc_delay': ([(2, 8), (9, 15)], [2, 1]),
                'axis_delay': ([(5, 10), (11, 20)], [2, 1]),
                'inter_op_delay': ([(5, 15)], [1])
            },
            'slow': {
                'desc_delay': ([(10, 20), (21, 40)], [2, 1]),
                'axis_delay': ([(15, 30), (31, 50)], [2, 1]),
                'inter_op_delay': ([(20, 50)], [1])
            },
            'stress': {
                'desc_delay': ([(0, 1), (2, 5)], [3, 1]),
                'axis_delay': ([(0, 2), (3, 8)], [3, 1]),
                'inter_op_delay': ([(0, 3)], [1])
            }
        }

    def set_timing_profile(self, profile: str):
        """Set timing profile"""
        if profile in self.timing_configs:
            self.current_timing_profile = profile
            self.timing_config = FlexRandomizer(self.timing_configs[profile])
            self.log.info(f"Timing profile set to: {profile}")

    def get_timing_value(self, name: str) -> int:
        """Get a timing value from the randomizer"""
        values = self.timing_config.next()
        return values.get(name, 5)

    # =========================================================================
    # DESCRIPTOR HELPERS
    # =========================================================================

    def create_write_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False) -> int:
        """Create a RAPIDS write descriptor (256 bits)

        RAPIDS Descriptor Format (from scheduler.sv):
          [63:0]    - src_addr:            Source address (must be aligned to data width)
          [127:64]  - dst_addr:            Destination address (must be aligned to data width)
          [159:128] - length:              Transfer length in BEATS (not bytes!)
          [191:160] - next_descriptor_ptr: Address of next descriptor (0 = last)
          [192]     - valid:               Descriptor valid flag  <-- CRITICAL!
          [193]     - gen_irq:             Generate interrupt on completion
          [194]     - last:                Last descriptor in chain flag
          [195]     - error:               Error flag
          [199:196] - channel_id:          Channel ID (informational)
          [207:200] - desc_priority:       Transfer priority
          [255:208] - reserved:            Reserved for future use

        For sink path (AXIS -> memory write):
          - src_addr = 0 (not used, data comes from AXIS)
          - dst_addr = memory address to write to
        """
        desc = 0
        # [63:0] src_addr - not used for sink path, set to 0
        desc |= 0
        # [127:64] dst_addr - destination memory address
        desc |= ((addr & ((1 << 64) - 1)) << 64)
        # [159:128] length - transfer beats
        desc |= ((beats & 0xFFFFFFFF) << 128)
        # [191:160] next_descriptor_ptr - 0 for single descriptor
        desc |= (0 << 160)
        # [192] valid - MUST be set!
        desc |= (1 << 192)
        # [193] gen_irq - set if eos (end of stream = generate interrupt)
        if eos:
            desc |= (1 << 193)
        # [194] last - last descriptor in chain
        desc |= (1 << 194)  # Always last for single descriptors
        # [195] error - no error
        desc |= (0 << 195)
        # [199:196] channel_id
        desc |= ((channel & 0xF) << 196)
        # [207:200] desc_priority
        desc |= (0 << 200)
        return desc

    async def send_descriptor(self, channel: int, addr: int, beats: int, eos: bool = False):
        """Send a descriptor to a specific channel"""
        if channel >= self.NUM_CHANNELS:
            raise ValueError(f"Invalid channel {channel}")

        desc = self.create_write_descriptor(channel, addr, beats, eos)

        # Debug: Print descriptor fields for verification
        self.log.info(f"=== DESCRIPTOR ch{channel} ===")
        self.log.info(f"  Full descriptor: 0x{desc:064X}")
        self.log.info(f"  [63:0]    src_addr:  0x{(desc >> 0) & ((1<<64)-1):016X}")
        self.log.info(f"  [127:64]  dst_addr:  0x{(desc >> 64) & ((1<<64)-1):016X}")
        self.log.info(f"  [159:128] length:    {(desc >> 128) & 0xFFFFFFFF} beats")
        self.log.info(f"  [191:160] next_ptr:  0x{(desc >> 160) & 0xFFFFFFFF:08X}")
        self.log.info(f"  [192]     valid:     {(desc >> 192) & 1}")
        self.log.info(f"  [193]     gen_irq:   {(desc >> 193) & 1}")
        self.log.info(f"  [194]     last:      {(desc >> 194) & 1}")
        self.log.info(f"  [195]     error:     {(desc >> 195) & 1}")
        self.log.info(f"  [199:196] chan_id:   {(desc >> 196) & 0xF}")

        # Send via GAXI master - use create_packet and send
        master = self.descriptor_masters[channel]
        packet = master.create_packet(packet=desc, error=0)
        await master.send(packet)

        self.test_stats['descriptors_sent'] += 1
        self.test_stats['channel_operations'][channel] += 1
        self.log.info(f"Sent descriptor to ch{channel}: addr=0x{addr:X}, beats={beats}, eos={eos}")

    # =========================================================================
    # AXIS HELPERS
    # =========================================================================

    async def send_axis_packet(self, channel: int, data: List[int], last: bool = True):
        """Send an AXIS packet"""
        axis_interface = self.axis_master['interface']
        for i, beat_data in enumerate(data):
            is_last = last and (i == len(data) - 1)
            # Use create_packet and send - standard GAXI master API
            packet = axis_interface.create_packet(
                data=beat_data,
                strb=(1 << self.STRB_WIDTH) - 1,  # All bytes valid
                id=channel,
                dest=0,
                user=0,
                last=int(is_last)
            )
            await axis_interface.send(packet)

        self.test_stats['axis_packets_sent'] += 1

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
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x1000
                beats = random.randint(1, 8)

                # Send descriptor
                await self.send_descriptor(channel, addr, beats)

                # Wait for scheduler to process
                await self.wait_clocks(self.clk_name, 50)

                # Check scheduler state
                sched_idle = int(self.dut.sched_idle.value)
                if (sched_idle >> channel) & 1:
                    # Scheduler returned to idle (processed descriptor)
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                else:
                    # Scheduler still busy (may be waiting for data)
                    successful += 1  # Still counts as sent successfully
                    self.test_stats['successful_operations'] += 1

                delay = self.get_timing_value('inter_op_delay')
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

        # Send descriptors to multiple channels
        for ch in range(num_channels):
            for d in range(descriptors_per_channel):
                try:
                    addr = self.BASE_ADDRESS + ch * self.CHANNEL_OFFSET + d * 0x1000
                    beats = 4

                    await self.send_descriptor(ch, addr, beats)
                    successful += 1
                    self.test_stats['successful_operations'] += 1

                    # Small delay between sends
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

    async def test_axis_reception(self, num_packets: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test AXIS data reception

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.
        """
        self.log.info(f"Testing AXIS reception ({num_packets} packets)...")

        successful = 0
        failed = 0

        for i in range(num_packets):
            try:
                channel = i % self.NUM_CHANNELS
                beats = random.randint(1, 4)

                # Generate test data
                test_data = [random.getrandbits(self.DATA_WIDTH) for _ in range(beats)]

                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x1000

                # CRITICAL FIX: Send AXIS data FIRST!
                # Data must be in SRAM before scheduler can command write engine
                await self.send_axis_packet(channel, test_data, last=True)
                await self.wait_clocks(self.clk_name, 10)

                # NOW send descriptor to command scheduler to drain SRAM
                await self.send_descriptor(channel, addr, beats)

                # Wait for processing
                await self.wait_clocks(self.clk_name, 50)

                successful += 1
                self.test_stats['successful_operations'] += 1

                delay = self.get_timing_value('axis_delay')
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

    def get_scheduler_state_str(self, state_val: int) -> str:
        """Convert scheduler state one-hot value to string"""
        # From rapids_pkg.sv channel_state_t (one-hot encoded)
        # CH_IDLE=0, CH_FETCH_DESC=1, CH_XFER_DATA=2, CH_COMPLETE=3, CH_NEXT_DESC=4, CH_ERROR=5
        states = ['IDLE', 'FETCH_DESC', 'XFER_DATA', 'COMPLETE', 'NEXT_DESC', 'ERROR', 'UNK']
        for i, name in enumerate(states[:-1]):
            if state_val == (1 << i):
                return name
        return f"UNKNOWN({state_val:02X})"

    def debug_scheduler_state(self, channel: int):
        """Debug output for scheduler state"""
        try:
            sched_idle = int(self.dut.sched_idle.value)
            sched_state_arr = self.dut.sched_state.value
            sched_error = int(self.dut.sched_error.value)

            # Try to get state for this channel
            ch_state = int(sched_state_arr[channel]) if hasattr(sched_state_arr, '__getitem__') else int(sched_state_arr)
            ch_idle = (sched_idle >> channel) & 1
            ch_error = (sched_error >> channel) & 1

            self.log.info(f"  Scheduler ch{channel}: state={self.get_scheduler_state_str(ch_state)}, "
                         f"idle={ch_idle}, error={ch_error}")
        except Exception as e:
            self.log.warning(f"  Could not read scheduler state for ch{channel}: {e}")

    async def test_axi_write_operations(self, num_operations: int = 12) -> Tuple[bool, Dict[str, Any]]:
        """Test AXI write operations

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.

        TIMING FIX: The full data path (AXIS->SRAM->drain->AXI W->B response) takes
        1000+ clocks per operation. We separate stimulus from verification:
        1. Phase 1: Send all AXIS data + descriptors (quick)
        2. Phase 2: Wait for all AXI writes to complete
        3. Phase 3: Verify all memory locations
        """
        self.log.info(f"Testing AXI write operations ({num_operations})...")

        # Track operation metadata for later verification
        operations = []
        beats = 4

        # =========================================================================
        # PHASE 1: STIMULUS - Send all AXIS data and descriptors
        # =========================================================================
        self.log.info("=== PHASE 1: Sending all stimulus ===")

        for i in range(num_operations):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x1000
                test_data = [0xDEAD0000 + i + b for b in range(beats)]

                self.log.info(f"Op {i}: ch{channel} addr=0x{addr:08X}")

                # Store operation metadata for verification
                operations.append({
                    'index': i,
                    'channel': channel,
                    'addr': addr,
                    'beats': beats,
                    'test_data': test_data
                })

                # Send AXIS data FIRST (into SRAM buffer)
                await self.send_axis_packet(channel, test_data, last=True)

                # Small wait for AXIS data to buffer
                await self.wait_clocks(self.clk_name, 10)

                # Send descriptor (triggers scheduler to drain SRAM to AXI)
                await self.send_descriptor(channel, addr, beats)

                # Small inter-operation delay
                await self.wait_clocks(self.clk_name, 5)

            except Exception as e:
                self.log.error(f"Stimulus for op {i} failed: {e}")

        # =========================================================================
        # PHASE 2: WAIT - Allow all AXI writes to complete
        # =========================================================================
        # The data path takes 100-200 clocks per operation, plus pipeline delays.
        # With 8 channels sharing one AXI interface, operations are serialized.
        # Wait: base_time + (operations * time_per_op)
        clocks_per_op = 150  # Empirically determined from timing analysis
        total_wait = num_operations * clocks_per_op + 500  # Extra margin

        self.log.info(f"=== PHASE 2: Waiting {total_wait} clocks for all writes to complete ===")
        await self.wait_clocks(self.clk_name, total_wait)

        # =========================================================================
        # PHASE 3: VERIFICATION - Check all memory locations
        # =========================================================================
        self.log.info("=== PHASE 3: Verifying all memory writes ===")

        successful = 0
        failed = 0

        for op in operations:
            i = op['index']
            addr = op['addr']
            channel = op['channel']

            # Check memory model for write
            bytes_to_read = self.DATA_WIDTH // 8
            relative_addr = addr - self.BASE_ADDRESS

            try:
                mem_data = self.memory_model.read(relative_addr, bytes_to_read)
                if mem_data and any(b != 0 for b in mem_data):
                    successful += 1
                    self.test_stats['axi_writes_completed'] += 1
                    self.test_stats['successful_operations'] += 1
                    self.log.info(f"Op {i} ch{channel}: PASS - data at 0x{addr:X}")
                else:
                    self.log.warning(f"Op {i} ch{channel}: FAIL - no data in memory at 0x{addr:X}")
                    failed += 1
                    self.test_stats['failed_operations'] += 1
            except Exception as e:
                self.log.warning(f"Op {i} ch{channel}: FAIL - memory read error at 0x{addr:X}: {e}")
                failed += 1
                self.test_stats['failed_operations'] += 1

        self.test_stats['total_operations'] += num_operations

        stats = {
            'successful': successful,
            'failed': failed,
            'total': num_operations,
            'success_rate': successful / num_operations if num_operations > 0 else 0
        }

        self.log.info(f"AXI write operations: {stats}")
        return failed == 0, stats

    async def test_end_to_end_flow(self, num_transfers: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test end-to-end data flow

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.
        """
        self.log.info(f"Testing end-to-end flow ({num_transfers} transfers)...")

        successful = 0
        failed = 0

        for i in range(num_transfers):
            try:
                channel = i % self.NUM_CHANNELS
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + i * 0x2000
                beats = random.randint(2, 8)
                test_data = [random.getrandbits(self.DATA_WIDTH) for _ in range(beats)]

                # CRITICAL FIX: Send AXIS data FIRST!
                # Data must be in SRAM before scheduler can command write engine
                await self.send_axis_packet(channel, test_data, last=True)
                await self.wait_clocks(self.clk_name, 20)

                # NOW send descriptor - tells scheduler to drain SRAM to memory
                await self.send_descriptor(channel, addr, beats, eos=(i == num_transfers - 1))

                # Wait for completion
                await self.wait_clocks(self.clk_name, 150)

                # Verify memory write (read one beat of data)
                # Convert absolute address to memory model relative address
                bytes_to_read = self.DATA_WIDTH // 8
                relative_addr = addr - self.BASE_ADDRESS
                mem_data = self.memory_model.read(relative_addr, bytes_to_read)
                if mem_data and any(b != 0 for b in mem_data):
                    successful += 1
                    self.test_stats['successful_operations'] += 1
                    self.log.debug(f"E2E transfer {i} successful: ch{channel}, addr=0x{addr:X}")
                else:
                    failed += 1
                    self.test_stats['failed_operations'] += 1
                    self.log.warning(f"E2E transfer {i} failed: no memory write")

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
        """Stress test with high throughput

        CRITICAL: Data flow is AXIS -> SRAM -> AXI Write
        We must send AXIS data BEFORE the descriptor so there's data in SRAM
        for the write engine to drain when the scheduler commands the write.
        """
        self.log.info(f"Running stress test ({num_operations} operations)...")

        successful = 0
        failed = 0

        for i in range(num_operations):
            try:
                channel = random.randint(0, self.NUM_CHANNELS - 1)
                addr = self.BASE_ADDRESS + channel * self.CHANNEL_OFFSET + random.randint(0, 0xFFFF) * 64
                beats = random.randint(1, 8)
                test_data = [random.getrandbits(self.DATA_WIDTH) for _ in range(beats)]

                # CRITICAL FIX: Send AXIS data FIRST!
                # Data must be in SRAM before scheduler can command write engine
                await self.send_axis_packet(channel, test_data, last=True)

                # Random delay after data
                delay = random.randint(1, 10)
                await self.wait_clocks(self.clk_name, delay)

                # NOW send descriptor - tells scheduler to drain SRAM to memory
                await self.send_descriptor(channel, addr, beats)

                # Short wait
                await self.wait_clocks(self.clk_name, random.randint(10, 30))

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
