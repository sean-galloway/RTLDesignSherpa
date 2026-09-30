# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BeatsSchedulerGroupArrayTB
# Purpose: RAPIDS Beats Scheduler Group Array Testbench - Phase 1 Macro Level
#
# Documentation: projects/components/dma-ip/rapids/PRD.md
# Subsystem: rapids_macro
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Scheduler Group Array Testbench - Phase 1 Macro Level

Testbench for the scheduler_group_array module which instantiates:
- 8x scheduler_group instances (each with descriptor_engine + scheduler)
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
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr


class SchedulerGroupArrayTB(TBBase):
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
        # Profile-driven delay injector for the APB descriptor kick. The array's
        # apb_valid/apb_addr are packed per-channel buses (driven via bit-slice
        # helpers), which GAXI BFMs can't own; instead the timing profile feeds a
        # FlexRandomizer whose valid_delay gates each per-channel request.
        self._apb_rnd = None
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
        self.dut.cfg_sched_timeout_limit.value = 1  # escalate after one window (legacy timeout->error)
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

        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Select a timing profile for APB descriptor-kick injection.

        The packed per-channel apb bus can't be owned by a GAXI master, so the
        profile's master valid_delay distribution is applied as an inter-request
        delay in send_apb_request (see _apb_rnd)."""
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', using 'backtoback'")
            profile_name = 'backtoback'
        cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]
        self._apb_rnd = FlexRandomizer(cfg['master'])
        self.log.info(f"GAXI scheduler_group_array APB-kick timing profile: {profile_name}")

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
        self.dut.sched_wr_ready.value = (1 << self.NUM_CHANNELS) - 1
        # byte-granular scheduler (TASK-019): packet-record consumers always ready here
        self.dut.sched_rd_pkt_ready.value = (1 << self.NUM_CHANNELS) - 1
        self.dut.sched_wr_pkt_ready.value = (1 << self.NUM_CHANNELS) - 1  # All channels ready

        # Per-channel completion strobes - packed arrays
        self.dut.sched_rd_done_strobe.value = 0
        self.dut.sched_wr_done_strobe.value = 0
        self.dut.sched_wr_commit_strobe.value = 0
        self.dut.sched_rd_error.value = 0
        self.dut.sched_wr_error.value = 0

        # Per-channel beats done - flattened by Verilator
        self.dut.sched_rd_beats_done.value = 0
        self.dut.sched_wr_beats_done.value = 0
        self.dut.sched_wr_commit_beats.value = 0

        # Shared control AXI masters + config (Phase 2) - scalar (not per-channel)
        self.dut.ctrlrd_axi_arready.value = 0
        self.dut.ctrlrd_axi_rvalid.value = 0
        self.dut.ctrlrd_axi_rdata.value = 0
        self.dut.ctrlrd_axi_rid.value = 0
        self.dut.ctrlrd_axi_rresp.value = 0
        self.dut.ctrlrd_axi_rlast.value = 0
        self.dut.ctrlwr_axi_awready.value = 0
        self.dut.ctrlwr_axi_wready.value = 0
        self.dut.ctrlwr_axi_bvalid.value = 0
        self.dut.ctrlwr_axi_bid.value = 0
        self.dut.ctrlwr_axi_bresp.value = 0
        self.dut.cfg_ctrlrd_max_try.value = 16
        self.dut.tick_1us.value = 0

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

        # Framework slaves own the three shared AXI masters' ports (rapids
        # TASK-013; the TB used to drive AR/R, AW/W/B by hand):
        #   desc_axi_*   256-bit read slave backed by descriptor_memory
        #   ctrlrd_axi_* 32-bit read slave backed by ctrlrd_memory (poll values)
        #   ctrlwr_axi_* 32-bit write slave backed by ctrlwr_memory (doorbells)
        self.ctrlrd_memory = MemoryModel(num_lines=4096, bytes_per_line=4, log=self.log)
        self.ctrlwr_memory = MemoryModel(num_lines=4096, bytes_per_line=4, log=self.log)
        self.desc_fetches, self._desc_fetch_seen = 0, 0
        self.ctrlwr_doorbells, self._ctrlwr_pending_aw = [], []
        self.ctrlrd_reads = []
        self.desc_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="desc_axi_", log=self.log,
            data_width=256, id_width=self.TEST_AXI_ID_WIDTH, addr_width=self.ADDR_WIDTH,
            user_width=1, multi_sig=True, memory_model=self.descriptor_memory)
        self.ctrlrd_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="ctrlrd_axi_", log=self.log,
            data_width=32, id_width=self.TEST_AXI_ID_WIDTH, addr_width=self.ADDR_WIDTH,
            user_width=1, multi_sig=True, memory_model=self.ctrlrd_memory)
        self.ctrlwr_slave = create_axi4_slave_wr(
            dut=self.dut, clock=self.clk, prefix="ctrlwr_axi_", log=self.log,
            data_width=32, id_width=self.TEST_AXI_ID_WIDTH, addr_width=self.ADDR_WIDTH,
            user_width=1, multi_sig=True, memory_model=self.ctrlwr_memory)
        for comp in (self.desc_slave['AR'], self.desc_slave['R'], self.ctrlrd_slave['AR'],
                     self.ctrlrd_slave['R'], self.ctrlwr_slave['AW'], self.ctrlwr_slave['W'],
                     self.ctrlwr_slave['B']):
            await comp.reset_bus()
        self.desc_slave['AR'].add_callback(self._on_desc_ar)
        self.ctrlrd_slave['AR'].add_callback(self._on_ctrlrd_ar)
        self.ctrlwr_slave['AW'].add_callback(self._on_ctrlwr_aw)
        self.ctrlwr_slave['W'].add_callback(self._on_ctrlwr_w)

        # sched_wr_ready is a packed array - set all channels ready
        self.dut.sched_wr_ready.value = (1 << self.NUM_CHANNELS) - 1
        # byte-granular scheduler (TASK-019): packet-record consumers always ready here
        self.dut.sched_rd_pkt_ready.value = (1 << self.NUM_CHANNELS) - 1
        self.dut.sched_wr_pkt_ready.value = (1 << self.NUM_CHANNELS) - 1
        self.dut.mon_ready.value = 1
        # Capture MonBus packets in the background from here on: the aggregation
        # test used to poll only after the activity that produced them (rapids TASK-003).
        cocotb.start_soon(self._capture_monbus())

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

        # Profile-driven injection delay (varies descriptor-request timing).
        if self._apb_rnd is not None:
            delay = int(self._apb_rnd.get_delay('valid_delay'))
            if delay > 0:
                await self.wait_clocks(self.clk_name, delay)

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
        self.descriptor_memory.write(addr, bytearray((data & ((1 << 256) - 1)).to_bytes(32, 'little')))
        self.log.debug(f"Registered descriptor at addr=0x{addr:X}")

    def clear_descriptor_lookup(self):
        """Clear the descriptor lookup table."""
        self.descriptor_lookup.clear()

    # -- framework-slave hooks (AR/AW/W monitor callbacks) ---------------------
    def _on_desc_ar(self, pkt):
        self.desc_fetches += 1
        ar_id = int(getattr(pkt, 'id', 0))
        channel = ar_id & (self.NUM_CHANNELS - 1)
        self.descriptors_served[channel] += 1
        self.log.info(f"descriptor fetch #{self.desc_fetches}: channel={channel} "
                      f"addr=0x{int(getattr(pkt, 'addr', 0)):X}")

    def _on_ctrlrd_ar(self, pkt):
        self.ctrlrd_reads.append((int(getattr(pkt, 'id', 0)) & (self.NUM_CHANNELS - 1),
                                  int(getattr(pkt, 'addr', 0))))

    def _on_ctrlwr_aw(self, pkt):
        self._ctrlwr_pending_aw.append((int(getattr(pkt, 'id', 0)) & (self.NUM_CHANNELS - 1),
                                        int(getattr(pkt, 'addr', 0))))

    def _on_ctrlwr_w(self, pkt):
        ch, addr = self._ctrlwr_pending_aw.pop(0) if self._ctrlwr_pending_aw else (None, None)
        self.ctrlwr_doorbells.append((ch, addr, int(getattr(pkt, 'data', 0)) & 0xFFFFFFFF))

    async def respond_to_descriptor_read(self, data: int = None) -> bool:
        """Wait for the desc_axi_* read slave to serve the next descriptor fetch.

        The slave answers from descriptor_memory, so the descriptor must be
        register_descriptor()'d BEFORE the kick; `data` is accepted only for
        call compatibility and is ignored (rapids TASK-013).
        """
        for _ in range(200):
            if self.desc_fetches > self._desc_fetch_seen:
                self._desc_fetch_seen += 1
                return True
            await self.wait_clocks(self.clk_name, 1)
        self.log.warning("AR handshake timeout - no descriptor fetch in 200 cycles")
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
        """Send write completion strobes (issue + commit) for a specific channel.

        commit_strobe now gates scheduler completion, so pulse it alongside the
        issue done_strobe (this simulator models issue and commit together).
        """
        # sched_wr_done_strobe / sched_wr_commit_strobe are packed arrays
        self._set_packed_bit(self.dut.sched_wr_done_strobe, channel, 1)
        self._set_packed_bit(self.dut.sched_wr_commit_strobe, channel, 1)
        # sched_wr_beats_done / sched_wr_commit_beats are flattened arrays
        self._set_array_element(self.dut.sched_wr_beats_done, channel, 32, beats_done)
        self._set_array_element(self.dut.sched_wr_commit_beats, channel, 32, beats_done)
        await self.wait_clocks(self.clk_name, 1)
        self._set_packed_bit(self.dut.sched_wr_done_strobe, channel, 0)
        self._set_packed_bit(self.dut.sched_wr_commit_strobe, channel, 0)
        self.completions_sent[channel] += 1
        self.log.info(f"WR completion: channel={channel}, beats={beats_done}")

    async def _capture_monbus(self):
        """Count and keep every packet the array's aggregated MonBus hands over."""
        from TBClasses.monbus import parse
        self.mon_packets = []
        while True:
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.mon_valid.value) == 1 and int(self.dut.mon_ready.value) == 1:
                raw = int(self.dut.mon_packet.value)
                self.mon_packets.append(parse(raw))
                self.mon_packets_received += 1

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
                         gen_irq: int = 0, last: int = 1, opcode: int = 0) -> int:
        """Create 256-bit descriptor data.

        RAPIDS Descriptor Format:
          [63:0]    - src_addr     (64 bits) - Source address
          [127:64]  - dst_addr     (64 bits) - Destination address
          [159:128] - length       (32 bits) - Transfer length in beats
          [191:160] - next_ptr     (32 bits) - Next descriptor pointer (0=none)
          [192]     - valid        (1 bit)   - Descriptor valid flag
          [193]     - gen_irq      (1 bit)   - Generate IRQ on completion
          [194]     - last         (1 bit)   - Last descriptor in chain
          [209:208] - opcode       (2 bits)  - 0=DATA, 1=CTRL_READ, 2=CTRL_WRITE
                        For control descriptors: addr=src[63:0], data=dst[31:0],
                        mask=dst[63:32].
        """
        desc_data = (src_addr & ((1 << 64) - 1))
        desc_data |= ((dst_addr & ((1 << 64) - 1)) << 64)
        # byte-granular scheduler (TASK-019): DATA lengths are BYTES (length here is beats)
        nbytes = length * (self.DATA_WIDTH // 8) if opcode == 0 else length
        desc_data |= ((nbytes & ((1 << 32) - 1)) << 128)
        desc_data |= ((next_ptr & ((1 << 32) - 1)) << 160)
        desc_data |= (valid << 192)
        desc_data |= (gen_irq << 193)
        desc_data |= (last << 194)
        desc_data |= ((opcode & 0x3) << 208)
        return desc_data

    # ==========================================================================
    # CONTROL-DESCRIPTOR SUPPORT (Phase 2 - shared masters, arbitration proof)
    # ==========================================================================

    async def _wait_busy_then_idle(self, channels, start_cycles: int = 300, timeout: int = 800) -> bool:
        """Each channel must LEAVE idle (its descriptor arrived) and then return
        to idle. Polling for idle alone right after the fetch returned true while
        the scheduler had not yet seen the descriptor (rapids TASK-013 bring-up)."""
        pending = set(channels)
        for _ in range(start_cycles):
            pending = {ch for ch in pending if self.is_scheduler_idle(ch)}
            if not pending:
                break
            await self.wait_clocks(self.clk_name, 1)
        if pending:
            self.log.error(f"channels {sorted(pending)} never left idle after their kick")
            return False
        for _ in range(timeout):
            if all(self.is_scheduler_idle(ch) for ch in channels):
                return True
            await self.wait_clocks(self.clk_name, 1)
        return False

    def _arm_ctrlwr_capture(self):
        """Start a fresh doorbell capture: (channel_from_awid, addr, data) per
        write the ctrlwr_axi_* slave accepts. B is routed back by ID by the slave."""
        self.ctrlwr_doorbells = []
        self._ctrlwr_pending_aw = []

    def _arm_ctrlrd_capture(self, match_value: int, addrs):
        """Preload match_value at every poll address the ctrlrd_axi_* slave will
        serve and start a fresh (channel_from_arid, addr) capture."""
        for a in addrs:
            self.ctrlrd_memory.write(a, bytearray((match_value & 0xFFFFFFFF).to_bytes(4, 'little')))
        self.ctrlrd_reads = []

    async def test_ctrl_multi_channel_doorbell(self, channels: List[int] = None) -> Tuple[bool, Dict[str, Any]]:
        """Multiple channels issue CTRL_WRITE doorbells through the SINGLE shared
        ctrlwr master; verify each lands with correct per-channel addr/data + channel
        ID (proves the write serializer + B demux)."""
        if channels is None:
            channels = [0, 1]
        self.log.info(f"=== Control Multi-Channel Doorbell Test: channels={channels} ===")
        self.clear_descriptor_lookup()
        self._arm_ctrlwr_capture()
        try:
            expected = {}
            for ch in channels:
                addr = 0x2000 + ch * 0x100
                data = 0xD00D0000 + ch
                desc = self.create_descriptor(src_addr=addr, dst_addr=data, length=1, opcode=2)
                self.register_descriptor(32 * (ch + 1), desc)
                expected[ch] = (addr, data)
                await self.send_apb_request(ch, 32 * (ch + 1))
            for _ in channels:
                await self.respond_to_descriptor_read()
            for _ in range(800):
                await self.wait_clocks(self.clk_name, 1)
                if len(self.ctrlwr_doorbells) >= len(channels):
                    break
            got = {ch: (a, d) for (ch, a, d) in self.ctrlwr_doorbells}
            errors = 0
            for ch in channels:
                if ch not in got or got[ch] != expected[ch]:
                    self.log.error(f"ch{ch} doorbell mismatch: got {got.get(ch)}, expected {expected[ch]}")
                    errors += 1
                else:
                    self.log.info(f"  OK ch{ch} doorbell: addr=0x{got[ch][0]:X} data=0x{got[ch][1]:X}")
            success = (errors == 0) and (len(self.ctrlwr_doorbells) == len(channels))
            self.log.info(f"Multi-channel doorbell test: {'PASSED' if success else 'FAILED'}")
            return (success, {'doorbells': len(self.ctrlwr_doorbells)})
        finally:
            self._ctrl_resp_active = False
            await self.wait_clocks(self.clk_name, 3)

    async def test_ctrl_multi_channel_gate(self, channels: List[int] = None) -> Tuple[bool, Dict[str, Any]]:
        """Multiple channels issue CTRL_READ gates through the SINGLE shared ctrlrd
        master; the responder returns a matching value so each gate opens. Verifies
        arbitration + R demux (each channel's scheduler completes)."""
        if channels is None:
            channels = [0, 1]
        self.log.info(f"=== Control Multi-Channel Gate Test: channels={channels} ===")
        self.clear_descriptor_lookup()
        self._arm_ctrlrd_capture(0x1, [0x3000 + ch * 0x100 for ch in channels])
        try:
            for ch in channels:
                poll_addr = 0x3000 + ch * 0x100
                desc = self.create_descriptor(src_addr=poll_addr,
                                              dst_addr=((0x1 << 32) | 0x1),  # mask=1, expected=1
                                              length=1, opcode=1)
                self.register_descriptor(32 * (ch + 1), desc)
                await self.send_apb_request(ch, 32 * (ch + 1))
            for _ in channels:
                await self.respond_to_descriptor_read()
            await self._wait_busy_then_idle(channels)
            errors = 0
            for ch in channels:
                if not self.is_scheduler_idle(ch):
                    self.log.error(f"ch{ch} scheduler not idle (gate did not open)")
                    errors += 1
            served = {ch for (ch, _a) in self.ctrlrd_reads}
            for ch in channels:
                if ch not in served:
                    self.log.error(f"ch{ch} never issued a ctrlrd poll")
                    errors += 1
            success = errors == 0
            self.log.info(f"Multi-channel gate test: {'PASSED' if success else 'FAILED'} "
                          f"(reads={len(self.ctrlrd_reads)})")
            return (success, {'reads': len(self.ctrlrd_reads)})
        finally:
            self._ctrl_resp_active = False
            await self.wait_clocks(self.clk_name, 3)

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
        self.register_descriptor(desc_addr, desc_data)

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
            self.register_descriptor(desc_addr, desc_data)

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
                self.register_descriptor(desc_addr, desc_data)

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

        # Packets have been captured since initialize_test(); the activity that
        # produced them ran before this call. Give stragglers a moment.
        await self.wait_clocks(self.clk_name, 50)
        pkts = list(getattr(self, 'mon_packets', []))
        kinds = [p.get_packet_type_name() for p in pkts]
        stats = {'events_received': len(pkts), 'kinds': sorted(set(kinds))}
        self.log.info(f"  MonBus packets captured: {len(pkts)} {stats['kinds']}")
        success = len(pkts) >= num_events and 'PktTypeCompletion' in kinds
        if not success:
            self.log.error(f"MonBus aggregation: expected >= {num_events} packets incl. a completion, got {len(pkts)} {kinds[:8]}")
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
