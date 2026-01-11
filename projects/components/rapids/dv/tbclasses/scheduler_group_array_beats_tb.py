# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BeatsSchedulerGroupArrayTB
# Purpose: RAPIDS Beats Scheduler Group Array Testbench - Phase 1 Macro Level
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_macro_beats
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Scheduler Group Array Testbench - Phase 1 Macro Level

Testbench for the scheduler_group_beats_array module which instantiates:
- 8x scheduler_group_beats instances (each with descriptor_engine + scheduler)
- Shared AXI4 descriptor read interface with round-robin arbitration
- Aggregated MonBus output from all 8 groups + arbiter (9 sources total)

This is a simplified RAPIDS architecture for Phase 1:
- No program engine (direct APB config)
- No control read/write engines
- Simplified data path interface
- 8 channels (vs 32 in full RAPIDS)

Features tested:
- Single channel operation
- Multi-channel concurrent operations
- AXI arbitration behavior
- MonBus aggregation
- All channels sequential
- Stress testing
"""

import os
import random
import cocotb
from typing import Dict, List, Tuple, Any, Optional
from cocotb.triggers import RisingEdge, Timer

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel


class SchedulerGroupArrayBeatsTB(TBBase):
    """
    RAPIDS Beats Scheduler Group Array testbench.

    Tests array functionality for 8 scheduler groups:
    - APB programming interface for descriptor fetch kick-off (per channel)
    - Shared descriptor AXI interface with round-robin arbitration
    - Per-channel scheduler data path command interfaces
    - Completion strobe handling
    - MonBus event aggregation from all sources
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.TEST_AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('CHANNEL_COUNT', '8'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.clk = clk if clk else dut.clk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'clk'
        self.rst_n = rst_n if rst_n else dut.rst_n

        # Calculated parameters
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1

        # Aliases for parameter access (used by helper methods)
        self.ADDR_WIDTH = self.TEST_ADDR_WIDTH
        self.DATA_WIDTH = self.TEST_DATA_WIDTH

        # Test tracking - per channel
        self.apb_requests = [0] * self.NUM_CHANNELS
        self.descriptors_served = [0] * self.NUM_CHANNELS
        self.rd_commands_received = [0] * self.NUM_CHANNELS
        self.wr_commands_received = [0] * self.NUM_CHANNELS
        self.completions_sent = [0] * self.NUM_CHANNELS
        self.mon_packets_received = 0
        self.test_errors = []

        # Memory model for descriptor storage
        self.descriptor_memory = None

        # Descriptor lookup table: address → data (for AXI responder)
        # This allows the responder to return correct data regardless of arbitration order
        self.descriptor_lookup = {}

        self.log.info(f"BeatsSchedulerGroupArrayTB initialized: "
                     f"{self.NUM_CHANNELS} channels, "
                     f"{self.TEST_ADDR_WIDTH}-bit addr, {self.TEST_DATA_WIDTH}-bit data")

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks AND performs reset sequence"""
        # Start clock
        await self.start_clock(self.clk_name, freq=self.TEST_CLK_PERIOD, units='ns')

        # Set configuration signals BEFORE reset (important for proper initialization)
        # Per-channel configuration
        self.dut.cfg_channel_enable.value = (1 << self.NUM_CHANNELS) - 1  # Enable all channels
        self.dut.cfg_channel_reset.value = 0

        # Global scheduler configuration
        self.dut.cfg_sched_enable.value = 1
        self.dut.cfg_sched_timeout_cycles.value = 1000
        self.dut.cfg_sched_timeout_enable.value = 1
        self.dut.cfg_sched_err_enable.value = 1
        self.dut.cfg_sched_compl_enable.value = 1
        self.dut.cfg_sched_perf_enable.value = 0

        # Global descriptor engine configuration
        self.dut.cfg_desceng_enable.value = 1
        self.dut.cfg_desceng_prefetch.value = 1
        self.dut.cfg_desceng_fifo_thresh.value = 4
        self.dut.cfg_desceng_addr0_base.value = 0
        self.dut.cfg_desceng_addr0_limit.value = 0xFFFF_FFFF_FFFF_FFFF
        self.dut.cfg_desceng_addr1_base.value = 0
        self.dut.cfg_desceng_addr1_limit.value = 0xFFFF_FFFF_FFFF_FFFF

        # Descriptor AXI monitor configuration
        self.dut.cfg_desc_mon_enable.value = 1
        self.dut.cfg_desc_mon_err_enable.value = 1
        self.dut.cfg_desc_mon_perf_enable.value = 0
        self.dut.cfg_desc_mon_timeout_enable.value = 1
        self.dut.cfg_desc_mon_timeout_cycles.value = 1000
        self.dut.cfg_desc_mon_latency_thresh.value = 100
        self.dut.cfg_desc_mon_pkt_mask.value = 0xFFFF
        self.dut.cfg_desc_mon_err_select.value = 0
        self.dut.cfg_desc_mon_err_mask.value = 0xFF
        self.dut.cfg_desc_mon_timeout_mask.value = 0xFF
        self.dut.cfg_desc_mon_compl_mask.value = 0xFF
        self.dut.cfg_desc_mon_thresh_mask.value = 0xFF
        self.dut.cfg_desc_mon_perf_mask.value = 0xFF
        self.dut.cfg_desc_mon_addr_mask.value = 0xFF
        self.dut.cfg_desc_mon_debug_mask.value = 0xFF

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

    async def assert_reset(self):
        """Assert reset signal"""
        self.mark_progress("assert_reset")
        self.rst_n.value = 0

        # Clear inputs during reset
        # Verilator flattens most multi-dimensional arrays to single registers
        # so we just set them to 0 as whole values

        # APB interface - simple packed arrays
        self.dut.apb_valid.value = 0
        # apb_addr is flattened by Verilator - set to 0
        self.dut.apb_addr.value = 0

        # Descriptor AXI interface (shared)
        self.dut.desc_axi_arready.value = 0
        self.dut.desc_axi_rvalid.value = 0
        self.dut.desc_axi_rdata.value = 0
        self.dut.desc_axi_rresp.value = 0
        self.dut.desc_axi_rlast.value = 0
        self.dut.desc_axi_rid.value = 0

        # Per-channel scheduler write interface ready - packed array
        self.dut.sched_wr_ready.value = (1 << self.NUM_CHANNELS) - 1  # All channels ready

        # Per-channel completion strobes - packed arrays
        self.dut.sched_rd_done_strobe.value = 0
        self.dut.sched_wr_done_strobe.value = 0
        self.dut.sched_rd_error.value = 0
        self.dut.sched_wr_error.value = 0

        # Per-channel beats done - flattened by Verilator
        self.dut.sched_rd_beats_done.value = 0
        self.dut.sched_wr_beats_done.value = 0

        # MonBus ready
        self.dut.mon_ready.value = 1

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.mark_progress("deassert_reset")
        self.rst_n.value = 1
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset deasserted")

    async def initialize_test(self):
        """Initialize test environment"""
        self.log.info("=== Initializing Beats Scheduler Group Array Test ===")
        self.log.info(f"  NUM_CHANNELS: {self.NUM_CHANNELS}")
        self.log.info(f"  ADDR_WIDTH: {self.TEST_ADDR_WIDTH}")
        self.log.info(f"  DATA_WIDTH: {self.TEST_DATA_WIDTH}")

        # Create memory model for descriptor storage (256-bit descriptors)
        self.descriptor_memory = MemoryModel(
            num_lines=4096,
            bytes_per_line=32,  # 256 bits = 32 bytes
            log=self.log
        )

        # Set default ready signals
        # desc_axi_arready is controlled by respond_to_descriptor_read - start low
        self.dut.desc_axi_arready.value = 0
        # sched_wr_ready is a packed array - set all channels ready
        self.dut.sched_wr_ready.value = (1 << self.NUM_CHANNELS) - 1
        self.dut.mon_ready.value = 1

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Beats scheduler group array initialization completed")

    # ==========================================================================
    # INTERFACE METHODS
    # ==========================================================================

    def _set_packed_bit(self, signal, bit_index: int, value: int):
        """Set a single bit in a packed array signal using read-modify-write."""
        current = int(signal.value)
        if value:
            current |= (1 << bit_index)
        else:
            current &= ~(1 << bit_index)
        signal.value = current

    def _get_packed_bit(self, signal, bit_index: int) -> int:
        """Get a single bit from a packed array signal."""
        return (int(signal.value) >> bit_index) & 1

    def _set_array_element(self, signal, element_index: int, element_width: int, value: int):
        """Set an element in a flattened array signal using read-modify-write.

        Verilator flattens [N-1:0][M-1:0] arrays into single wide registers.
        This method sets element[element_index] which occupies bits [element_index*element_width +: element_width].

        Args:
            signal: The flattened DUT signal
            element_index: Which element to set (0 to N-1)
            element_width: Width of each element in bits
            value: Value to write to this element
        """
        current = int(signal.value)
        bit_offset = element_index * element_width
        mask = ((1 << element_width) - 1) << bit_offset
        current = (current & ~mask) | ((value & ((1 << element_width) - 1)) << bit_offset)
        signal.value = current

    def _get_array_element(self, signal, element_index: int, element_width: int) -> int:
        """Get an element from a flattened array signal.

        Args:
            signal: The flattened DUT signal
            element_index: Which element to get (0 to N-1)
            element_width: Width of each element in bits

        Returns:
            The value of the specified element
        """
        current = int(signal.value)
        bit_offset = element_index * element_width
        return (current >> bit_offset) & ((1 << element_width) - 1)

    async def send_apb_request(self, channel: int, addr: int) -> bool:
        """Send APB descriptor fetch request to specific channel.

        Args:
            channel: Channel number (0-7)
            addr: Descriptor address to fetch

        Returns:
            True if request accepted, False on timeout
        """
        if channel >= self.NUM_CHANNELS:
            self.log.error(f"Invalid channel {channel}, max is {self.NUM_CHANNELS-1}")
            return False

        # Set apb_valid bit for this channel (packed array)
        self._set_packed_bit(self.dut.apb_valid, channel, 1)
        # Set apb_addr for this channel (flattened array: [NUM_CHANNELS-1:0][ADDR_WIDTH-1:0])
        self._set_array_element(self.dut.apb_addr, channel, self.ADDR_WIDTH, addr)

        # Wait for ready handshake
        for _ in range(100):
            if self._get_packed_bit(self.dut.apb_ready, channel) == 1:
                await self.wait_clocks(self.clk_name, 1)
                self.apb_requests[channel] += 1
                self.log.info(f"APB request sent: channel={channel}, addr=0x{addr:X}")
                self._set_packed_bit(self.dut.apb_valid, channel, 0)
                return True
            await self.wait_clocks(self.clk_name, 1)

        self.log.warning(f"APB request timeout on channel {channel}: addr=0x{addr:X}")
        self._set_packed_bit(self.dut.apb_valid, channel, 0)
        return False

    def register_descriptor(self, addr: int, data: int):
        """Register a descriptor in the lookup table for AXI responder.

        Args:
            addr: Descriptor address (where it will be fetched from)
            data: 256-bit descriptor data
        """
        self.descriptor_lookup[addr] = data
        self.log.debug(f"Registered descriptor at addr=0x{addr:X}")

    def clear_descriptor_lookup(self):
        """Clear the descriptor lookup table."""
        self.descriptor_lookup.clear()

    async def respond_to_descriptor_read(self, data: int = None) -> bool:
        """Respond to shared descriptor AXI read request.

        When 'data' is provided explicitly, uses that data (backward compatible).
        When 'data' is None, looks up the response data from descriptor_lookup
        table based on the actual request address - this handles arbitration
        order correctly in multi-channel scenarios.

        Args:
            data: 256-bit descriptor data to return (None = use lookup table)

        Returns:
            True if response sent, False on timeout
        """
        # Hold AR ready low until we're ready to process
        self.dut.desc_axi_arready.value = 0

        # Wait for AR valid (increased timeout for multi-channel scenarios where
        # arbiter needs time to cycle through all pending requests)
        for i in range(200):
            ar_valid = int(self.dut.desc_axi_arvalid.value)
            if ar_valid == 1:
                # Capture request info before acknowledging
                ar_addr = int(self.dut.desc_axi_araddr.value)
                ar_id = int(self.dut.desc_axi_arid.value)
                # Now assert ready to complete handshake
                self.dut.desc_axi_arready.value = 1
                await self.wait_clocks(self.clk_name, 1)
                self.dut.desc_axi_arready.value = 0  # De-assert for next request
                self.log.info(f"AR handshake at cycle {i}")
                break
            await self.wait_clocks(self.clk_name, 1)
        else:
            self.log.warning("AR handshake timeout - no AR valid in 200 cycles")
            self.dut.desc_axi_arready.value = 1  # Restore default
            return False

        # Determine response data
        if data is None:
            # Use lookup table based on actual request address
            if ar_addr in self.descriptor_lookup:
                response_data = self.descriptor_lookup[ar_addr]
                self.log.info(f"Lookup hit: addr=0x{ar_addr:X}")
            else:
                self.log.error(f"Descriptor lookup miss: addr=0x{ar_addr:X} not registered")
                self.log.error(f"Registered addresses: {[hex(a) for a in self.descriptor_lookup.keys()]}")
                return False
        else:
            # Use explicitly provided data (backward compatible)
            response_data = data

        await self.wait_clocks(self.clk_name, 2)

        # Send read response (single beat for 256-bit descriptor)
        self.dut.desc_axi_rvalid.value = 1
        self.dut.desc_axi_rdata.value = response_data
        self.dut.desc_axi_rresp.value = 0  # OKAY
        self.dut.desc_axi_rlast.value = 1
        self.dut.desc_axi_rid.value = ar_id

        # Wait for ready
        await Timer(0, units='ns')

        for i in range(50):
            r_ready = int(self.dut.desc_axi_rready.value)

            if r_ready == 1:
                await self.wait_clocks(self.clk_name, 1)
                # Extract channel from ID (lower bits)
                channel = ar_id & ((1 << 3) - 1)  # 3 bits for 8 channels
                if channel < self.NUM_CHANNELS:
                    self.descriptors_served[channel] += 1
                self.log.info(f"Descriptor served: channel={channel}, addr=0x{ar_addr:X}")
                self.dut.desc_axi_rvalid.value = 0
                return True

            await self.wait_clocks(self.clk_name, 1)
            await Timer(0, units='ns')

        self.log.error(f"R channel timeout: r_ready never asserted")
        self.dut.desc_axi_rvalid.value = 0
        return False

    async def wait_for_rd_command(self, channel: int, timeout: int = 100) -> Optional[Tuple[int, int]]:
        """Wait for scheduler read command on specific channel.

        Returns:
            Tuple of (addr, beats) if command received, None on timeout
        """
        for _ in range(timeout):
            # sched_rd_valid is a packed array
            if self._get_packed_bit(self.dut.sched_rd_valid, channel) == 1:
                # sched_rd_addr and sched_rd_beats are flattened arrays
                addr = self._get_array_element(self.dut.sched_rd_addr, channel, self.ADDR_WIDTH)
                beats = self._get_array_element(self.dut.sched_rd_beats, channel, 32)
                self.rd_commands_received[channel] += 1
                self.log.info(f"RD command: channel={channel}, addr=0x{addr:X}, beats={beats}")
                return (addr, beats)
            await self.wait_clocks(self.clk_name, 1)
        return None

    async def wait_for_wr_command(self, channel: int, timeout: int = 100) -> Optional[Tuple[int, int]]:
        """Wait for scheduler write command on specific channel.

        Returns:
            Tuple of (addr, beats) if command received, None on timeout
        """
        for _ in range(timeout):
            # sched_wr_valid is a packed array
            if self._get_packed_bit(self.dut.sched_wr_valid, channel) == 1:
                # sched_wr_addr and sched_wr_beats are flattened arrays
                addr = self._get_array_element(self.dut.sched_wr_addr, channel, self.ADDR_WIDTH)
                beats = self._get_array_element(self.dut.sched_wr_beats, channel, 32)
                await self.wait_clocks(self.clk_name, 1)
                self.wr_commands_received[channel] += 1
                self.log.info(f"WR command: channel={channel}, addr=0x{addr:X}, beats={beats}")
                return (addr, beats)
            await self.wait_clocks(self.clk_name, 1)
        return None

    async def send_rd_completion(self, channel: int, beats_done: int):
        """Send read completion strobe for specific channel."""
        # sched_rd_done_strobe is a packed array
        self._set_packed_bit(self.dut.sched_rd_done_strobe, channel, 1)
        # sched_rd_beats_done is a flattened array
        self._set_array_element(self.dut.sched_rd_beats_done, channel, 32, beats_done)
        await self.wait_clocks(self.clk_name, 1)
        self._set_packed_bit(self.dut.sched_rd_done_strobe, channel, 0)
        self.completions_sent[channel] += 1
        self.log.info(f"RD completion: channel={channel}, beats={beats_done}")

    async def send_wr_completion(self, channel: int, beats_done: int):
        """Send write completion strobe for specific channel."""
        # sched_wr_done_strobe is a packed array
        self._set_packed_bit(self.dut.sched_wr_done_strobe, channel, 1)
        # sched_wr_beats_done is a flattened array
        self._set_array_element(self.dut.sched_wr_beats_done, channel, 32, beats_done)
        await self.wait_clocks(self.clk_name, 1)
        self._set_packed_bit(self.dut.sched_wr_done_strobe, channel, 0)
        self.completions_sent[channel] += 1
        self.log.info(f"WR completion: channel={channel}, beats={beats_done}")

    async def check_monbus_packet(self, timeout: int = 50) -> Optional[int]:
        """Check for monitor bus packet.

        Returns:
            64-bit packet data if available, None on timeout
        """
        for _ in range(timeout):
            if int(self.dut.mon_valid.value) == 1 and int(self.dut.mon_ready.value) == 1:
                packet = int(self.dut.mon_packet.value)
                self.mon_packets_received += 1
                return packet
            await self.wait_clocks(self.clk_name, 1)
        return None

    # ==========================================================================
    # STATUS METHODS
    # ==========================================================================

    def is_scheduler_idle(self, channel: int) -> bool:
        """Check if scheduler on specific channel is idle."""
        # scheduler_idle is a packed array
        return self._get_packed_bit(self.dut.scheduler_idle, channel) == 1

    def is_descriptor_engine_idle(self, channel: int) -> bool:
        """Check if descriptor engine on specific channel is idle."""
        # descriptor_engine_idle is a packed array
        return self._get_packed_bit(self.dut.descriptor_engine_idle, channel) == 1

    def get_scheduler_state(self, channel: int) -> int:
        """Get scheduler state (7-bit one-hot) for specific channel."""
        # scheduler_state is a flattened array [NUM_CHANNELS-1:0][6:0]
        return self._get_array_element(self.dut.scheduler_state, channel, 7)

    def has_scheduler_error(self, channel: int) -> bool:
        """Check for scheduler error on specific channel."""
        # sched_error is a packed array
        return self._get_packed_bit(self.dut.sched_error, channel) == 1

    def all_schedulers_idle(self) -> bool:
        """Check if all schedulers are idle."""
        # Check if all bits in the packed array are 1
        idle_mask = (1 << self.NUM_CHANNELS) - 1
        return int(self.dut.scheduler_idle.value) == idle_mask

    # ==========================================================================
    # HELPER METHODS
    # ==========================================================================

    def create_descriptor(self, src_addr: int, dst_addr: int, length: int,
                         next_ptr: int = 0, valid: int = 1,
                         gen_irq: int = 0, last: int = 1) -> int:
        """Create 256-bit descriptor data.

        RAPIDS Descriptor Format:
          [63:0]    - src_addr     (64 bits) - Source address
          [127:64]  - dst_addr     (64 bits) - Destination address
          [159:128] - length       (32 bits) - Transfer length in beats
          [191:160] - next_ptr     (32 bits) - Next descriptor pointer (0=none)
          [192]     - valid        (1 bit)   - Descriptor valid flag
          [193]     - gen_irq      (1 bit)   - Generate IRQ on completion
          [194]     - last         (1 bit)   - Last descriptor in chain
        """
        desc_data = (src_addr & ((1 << 64) - 1))
        desc_data |= ((dst_addr & ((1 << 64) - 1)) << 64)
        desc_data |= ((length & ((1 << 32) - 1)) << 128)
        desc_data |= ((next_ptr & ((1 << 32) - 1)) << 160)
        desc_data |= (valid << 192)
        desc_data |= (gen_irq << 193)
        desc_data |= (last << 194)
        return desc_data

    # ==========================================================================
    # TEST METHODS
    # ==========================================================================

    async def test_single_channel_operation(self, channel: int = 0) -> Tuple[bool, Dict[str, Any]]:
        """Test basic operation on a single channel.

        Args:
            channel: Channel to test (0-7)

        Returns:
            Tuple of (success, stats_dict)
        """
        self.log.info(f"=== Single Channel Operation Test: channel={channel} ===")

        errors = 0
        stats = {'channel': channel, 'apb_sent': 0, 'desc_received': 0, 'commands': 0}

        # Create descriptor
        src_addr = random.randint(0x1000, 0xFFFF) * 0x100
        dst_addr = random.randint(0x2000, 0xFFFF) * 0x100
        length = random.randint(1, 64)
        desc_data = self.create_descriptor(src_addr, dst_addr, length)
        desc_addr = 32  # Non-zero, 32-byte aligned

        self.log.info(f"Descriptor: src=0x{src_addr:X}, dst=0x{dst_addr:X}, len={length}")

        # Send APB request
        if await self.send_apb_request(channel, desc_addr):
            stats['apb_sent'] = 1
        else:
            self.log.error(f"APB request failed on channel {channel}")
            errors += 1

        # Respond to AXI read
        if await self.respond_to_descriptor_read(desc_data):
            stats['desc_received'] = 1
        else:
            self.log.error(f"Descriptor AXI response failed on channel {channel}")
            errors += 1

        # Wait for scheduler command
        await self.wait_clocks(self.clk_name, 20)

        rd_cmd = await self.wait_for_rd_command(channel, timeout=50)
        if rd_cmd:
            stats['commands'] += 1
            addr, beats = rd_cmd
            await self.wait_clocks(self.clk_name, 10)
            await self.send_rd_completion(channel, beats)

        wr_cmd = await self.wait_for_wr_command(channel, timeout=50)
        if wr_cmd:
            stats['commands'] += 1
            addr, beats = wr_cmd
            await self.wait_clocks(self.clk_name, 10)
            await self.send_wr_completion(channel, beats)

        await self.wait_clocks(self.clk_name, 20)

        success = errors == 0 and stats['commands'] > 0
        self.log.info(f"Single channel test: {'PASSED' if success else 'FAILED'}")
        return (success, stats)

    async def test_multi_channel_concurrent(self, channels: List[int]) -> Tuple[bool, Dict[str, Any]]:
        """Test concurrent operations on multiple channels.

        Args:
            channels: List of channel numbers to test

        Returns:
            Tuple of (success, stats_dict)
        """
        self.log.info(f"=== Multi-Channel Concurrent Test: channels={channels} ===")

        errors = 0
        stats = {'channels': channels, 'apb_sent': 0, 'desc_received': 0, 'commands': 0}

        # Clear lookup table from any previous test
        self.clear_descriptor_lookup()

        # Create descriptors for each channel and register in lookup table
        descriptors = {}
        for ch in channels:
            src_addr = random.randint(0x1000, 0xFFFF) * 0x100
            dst_addr = random.randint(0x2000, 0xFFFF) * 0x100
            length = random.randint(1, 32)
            desc_data = self.create_descriptor(src_addr, dst_addr, length)
            desc_addr = (ch + 1) * 32  # Unique address per channel
            descriptors[ch] = {'data': desc_data, 'addr': desc_addr, 'length': length}
            # Register in lookup table - allows responder to return correct data
            # regardless of arbitration order
            self.register_descriptor(desc_addr, desc_data)

        # Send APB requests to all channels
        for ch in channels:
            if await self.send_apb_request(ch, descriptors[ch]['addr']):
                stats['apb_sent'] += 1
            else:
                errors += 1

        # Respond to AXI reads using lookup table
        # The round-robin arbiter may serve channels in any order - the lookup
        # table ensures each channel gets its correct descriptor data
        for _ in channels:
            if await self.respond_to_descriptor_read():  # Uses lookup table
                stats['desc_received'] += 1
            else:
                errors += 1

        # Wait for and handle scheduler commands
        await self.wait_clocks(self.clk_name, 50)

        for ch in channels:
            rd_cmd = await self.wait_for_rd_command(ch, timeout=50)
            if rd_cmd:
                stats['commands'] += 1
                await self.send_rd_completion(ch, rd_cmd[1])

            wr_cmd = await self.wait_for_wr_command(ch, timeout=50)
            if wr_cmd:
                stats['commands'] += 1
                await self.send_wr_completion(ch, wr_cmd[1])

        await self.wait_clocks(self.clk_name, 50)

        success = errors == 0 and stats['commands'] >= len(channels)
        self.log.info(f"Multi-channel concurrent test: {'PASSED' if success else 'FAILED'}")
        return (success, stats)

    async def test_multi_channel_concurrent_operation(self, num_channels_active: int = 4,
                                                      ops_per_channel: int = 2,
                                                      test_level: int = 0) -> Tuple[bool, Dict[str, Any]]:
        """Test concurrent operations on multiple channels with configurable operations.

        Args:
            num_channels_active: Number of channels to activate
            ops_per_channel: Operations per channel
            test_level: Test intensity level (0=basic, 1=medium, 2=full)

        Returns:
            Tuple of (success, stats_dict)
        """
        channels = list(range(min(num_channels_active, self.NUM_CHANNELS)))
        return await self.test_multi_channel_concurrent(channels)

    async def test_axi_arbitration(self, num_operations: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test AXI arbitration behavior with multiple channels.

        Args:
            num_operations: Number of operations to perform

        Returns:
            Tuple of (success, stats_dict)
        """
        self.log.info(f"=== AXI Arbitration Test: {num_operations} operations ===")

        stats = {'operations': num_operations, 'channels_served': [0] * self.NUM_CHANNELS}
        errors = 0

        # Send requests from multiple channels simultaneously
        channels_to_test = list(range(min(num_operations, self.NUM_CHANNELS)))

        for ch in channels_to_test:
            src_addr = random.randint(0x1000, 0xFFFF) * 0x100
            dst_addr = random.randint(0x2000, 0xFFFF) * 0x100
            desc_data = self.create_descriptor(src_addr, dst_addr, 16)
            desc_addr = (ch + 1) * 32

            if await self.send_apb_request(ch, desc_addr):
                if await self.respond_to_descriptor_read(desc_data):
                    stats['channels_served'][ch] += 1
                else:
                    errors += 1
            else:
                errors += 1

        await self.wait_clocks(self.clk_name, 100)

        success = errors == 0
        self.log.info(f"AXI arbitration test: {'PASSED' if success else 'FAILED'}")
        return (success, stats)

    async def test_all_channels_sequential(self, descriptors_per_channel: int = 1) -> Tuple[bool, Dict[str, Any]]:
        """Test all 8 channels sequentially.

        Args:
            descriptors_per_channel: Number of descriptors per channel

        Returns:
            Tuple of (success, stats_dict)
        """
        self.log.info(f"=== All Channels Sequential Test: {descriptors_per_channel} desc/channel ===")

        errors = 0
        stats = {'channels_tested': 0, 'total_operations': 0}

        for ch in range(self.NUM_CHANNELS):
            self.log.info(f"Testing channel {ch}...")

            for op in range(descriptors_per_channel):
                src_addr = random.randint(0x1000, 0xFFFF) * 0x100
                dst_addr = random.randint(0x2000, 0xFFFF) * 0x100
                length = random.randint(1, 32)
                desc_data = self.create_descriptor(src_addr, dst_addr, length)
                desc_addr = (ch * 16 + op + 1) * 32

                if await self.send_apb_request(ch, desc_addr):
                    if await self.respond_to_descriptor_read(desc_data):
                        stats['total_operations'] += 1

                        # Handle commands
                        await self.wait_clocks(self.clk_name, 20)
                        rd_cmd = await self.wait_for_rd_command(ch, timeout=50)
                        if rd_cmd:
                            await self.send_rd_completion(ch, rd_cmd[1])

                        wr_cmd = await self.wait_for_wr_command(ch, timeout=50)
                        if wr_cmd:
                            await self.send_wr_completion(ch, wr_cmd[1])
                    else:
                        errors += 1
                else:
                    errors += 1

            stats['channels_tested'] += 1
            await self.wait_clocks(self.clk_name, 20)

        success = errors == 0
        self.log.info(f"All channels sequential test: {'PASSED' if success else 'FAILED'}")
        return (success, stats)

    async def test_monitor_bus_aggregation(self, num_events: int = 2) -> Tuple[bool, Dict[str, Any]]:
        """Test MonBus aggregation from all sources.

        Args:
            num_events: Number of events to wait for

        Returns:
            Tuple of (success, stats_dict)
        """
        self.log.info(f"=== MonBus Aggregation Test ===")

        initial_count = self.mon_packets_received
        stats = {'events_received': 0}

        # Check for monitor packets
        for _ in range(num_events * 10):
            packet = await self.check_monbus_packet(timeout=20)
            if packet is not None:
                stats['events_received'] += 1
                self.log.info(f"  MonBus packet received: 0x{packet:016X}")
                if stats['events_received'] >= num_events:
                    break

        success = stats['events_received'] > 0
        self.log.info(f"MonBus aggregation test: {stats['events_received']} events received")
        return (success, stats)

    async def stress_test(self, num_operations: int = 10) -> Tuple[bool, Dict[str, Any]]:
        """Stress test with sequential channel selection.

        Uses round-robin channel selection to ensure each channel completes
        its operation before receiving another request.

        Note: This testbench only simulates the APB→descriptor path, not
        the full data path (RD/WR commands and completions). Without full
        data path simulation, channels remain busy after descriptor fetch.
        Therefore, num_operations is limited to NUM_CHANNELS to ensure
        each channel only receives one request.

        Args:
            num_operations: Total number of operations (limited to NUM_CHANNELS)

        Returns:
            Tuple of (success, stats_dict)
        """
        # Limit operations to number of channels since we don't simulate
        # the full data path that would release channels for reuse
        effective_ops = min(num_operations, self.NUM_CHANNELS)
        if num_operations > self.NUM_CHANNELS:
            self.log.info(f"Limiting stress test to {effective_ops} ops (one per channel) - "
                         f"full data path simulation not implemented")

        self.log.info(f"=== Stress Test: {effective_ops} operations ===")

        stats = {'operations_attempted': 0, 'operations_completed': 0,
                 'errors': 0, 'success_rate': 0}

        # Clear lookup table
        self.clear_descriptor_lookup()

        for i in range(effective_ops):
            # Use round-robin channel selection (not random) to avoid
            # sending to busy channels.
            channel = i % self.NUM_CHANNELS
            src_addr = random.randint(0x1000, 0xFFFF) * 0x100
            dst_addr = random.randint(0x2000, 0xFFFF) * 0x100
            length = random.randint(1, 64)
            desc_data = self.create_descriptor(src_addr, dst_addr, length)
            desc_addr = (i + 1) * 32

            # Register descriptor in lookup table
            self.register_descriptor(desc_addr, desc_data)

            stats['operations_attempted'] += 1

            if await self.send_apb_request(channel, desc_addr):
                if await self.respond_to_descriptor_read():  # Uses lookup table
                    stats['operations_completed'] += 1
                else:
                    stats['errors'] += 1
            else:
                stats['errors'] += 1

        await self.wait_clocks(self.clk_name, 100)

        stats['success_rate'] = (stats['operations_completed'] / stats['operations_attempted']
                                  if stats['operations_attempted'] > 0 else 0)

        success = stats['success_rate'] >= 0.9
        self.log.info(f"Stress test: {stats['success_rate']*100:.1f}% success rate")
        return (success, stats)

    # ==========================================================================
    # SUMMARY AND REPORTING
    # ==========================================================================

    def finalize_test(self):
        """Finalize test and clean up."""
        self.log.info("Finalizing beats scheduler group array test")

    def print_test_summary(self):
        """Print comprehensive test summary."""
        self.log.info("\n" + "=" * 60)
        self.log.info("BEATS SCHEDULER GROUP ARRAY TEST SUMMARY")
        self.log.info("=" * 60)

        total_apb = sum(self.apb_requests)
        total_desc = sum(self.descriptors_served)
        total_rd = sum(self.rd_commands_received)
        total_wr = sum(self.wr_commands_received)
        total_compl = sum(self.completions_sent)

        self.log.info(f"Total APB requests: {total_apb}")
        self.log.info(f"Total descriptors served: {total_desc}")
        self.log.info(f"Total RD commands: {total_rd}")
        self.log.info(f"Total WR commands: {total_wr}")
        self.log.info(f"Total completions: {total_compl}")
        self.log.info(f"MonBus packets: {self.mon_packets_received}")

        self.log.info("\nPer-channel statistics:")
        for ch in range(self.NUM_CHANNELS):
            self.log.info(f"  Channel {ch}: APB={self.apb_requests[ch]}, "
                         f"DESC={self.descriptors_served[ch]}, "
                         f"RD={self.rd_commands_received[ch]}, "
                         f"WR={self.wr_commands_received[ch]}")

        if self.test_errors:
            self.log.error(f"\nTest errors ({len(self.test_errors)}):")
            for error in self.test_errors:
                self.log.error(f"  - {error}")

        self.log.info("=" * 60)
