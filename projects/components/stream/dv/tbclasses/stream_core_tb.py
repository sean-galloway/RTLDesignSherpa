"""
Stream Core Testbench - Complete STREAM DMA Engine Integration

This testbench follows the datapath test pattern:
- AXI slave responders backed by memory models
- Descriptor memory loaded with test descriptors
- APB kick-off interface to start transfers
- Full data verification

Author: RTL Design Sherpa
Date: 2025-11-08
"""

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
import sys
import os

# Add repository root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr
from projects.components.stream.dv.tbclasses.descriptor_packet_builder import DescriptorPacketBuilder


class StreamCoreTB(TBBase):
    """
    Testbench for stream_core - Complete STREAM DMA integration.

    Follows datapath test pattern:
    - Memory models for descriptor/source/destination
    - AXI slaves respond from memory models
    - APB kick-off interface
    - Full verification

    Attributes:
        num_channels: Number of DMA channels (1-8)
        addr_width: Address bus width (default 64)
        data_width: Data bus width (default 512)
        axi_id_width: AXI ID width (default 8)
        fifo_depth: Internal FIFO depth (default 512)
    """

    def __init__(self, dut,
                 num_channels=4,
                 addr_width=64,
                 data_width=512,
                 axi_id_width=8,
                 fifo_depth=512,
                 **kwargs):
        """Initialize stream_core testbench"""
        super().__init__(dut)

        # Save parameters
        self.num_channels = num_channels
        self.addr_width = addr_width
        self.data_width = data_width
        self.axi_id_width = axi_id_width
        self.fifo_depth = fifo_depth
        self.data_bytes = data_width // 8

        # Clock/reset
        self.clk = dut.clk
        self.rst_n = dut.rst_n
        self.clk_name = 'clk'

        # Memory maps
        # NOTE: Descriptor base must be non-zero (address 0 is invalid/error)
        self.desc_mem_base = 0x0001_0000  # Start at 64KB (address 0 reserved as invalid)
        self.desc_mem_size = 0x0001_0000  # 64KB
        self.src_mem_base = 0x8000_0000
        self.src_mem_size = 0x1000_0000   # 256MB
        self.dst_mem_base = 0x9000_0000
        self.dst_mem_size = 0x1000_0000   # 256MB

        # Memory models (MemoryModel objects - initialized in setup)
        self.desc_memory_model = None  # Descriptor memory (256-bit read)
        self.src_memory_model = None   # Source data memory
        self.dst_memory_model = None   # Destination data memory

        # BFM components (initialized in setup)
        self.desc_axi_slave = None  # AXI4 slave dict for descriptor fetches (256-bit)
        self.rd_axi_slave = None    # AXI4 slave dict for data reads (parameterizable)
        self.wr_axi_slave = None    # AXI4 slave dict for data writes (parameterizable)
        self.desc_slave = None      # R channel from desc_axi_slave
        self.rd_slave = None        # R channel from rd_axi_slave
        self.wr_slave = None        # W+B channels from wr_axi_slave

        # Descriptor builder
        self.desc_builder = DescriptorPacketBuilder()

        # MonBus packet capture
        self.mon_packets = []

        # Performance tracking
        self.transfer_start_time = {}
        self.transfer_end_time = {}

        # Interface monitoring - queues for captured transactions
        self.apb_transactions = []        # APB → Descriptor
        self.datard_requests = []         # Scheduler → Read Engine
        self.datawr_requests = []         # Scheduler → Write Engine
        self.datard_completions = []      # Read Engine → Scheduler
        self.datawr_completions = []      # Write Engine → Scheduler

    async def setup_clocks_and_reset(self, xfer_beats=16):
        """
        Complete initialization following datapath pattern.

        Args:
            xfer_beats: AXI transfer size in beats (default 16)
        """
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize configuration signals before reset
        self._init_config_signals(xfer_beats)

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        # Initialize AXI slave responders after reset
        await self._init_bfm_components()

        # Start background monitors
        cocotb.start_soon(self._monitor_monbus())
        cocotb.start_soon(self._monitor_apb_to_desc())
        cocotb.start_soon(self._monitor_datard_interface())
        cocotb.start_soon(self._monitor_datawr_interface())
        cocotb.start_soon(self._monitor_datard_completions())
        cocotb.start_soon(self._monitor_datawr_completions())

        self.log.info(f"stream_core TB initialized: {self.num_channels} channels, "
                     f"{self.data_width}-bit data, {self.fifo_depth}-deep FIFO")
        self.log.info("Background monitors started for APB, datard, datawr interfaces")

    async def assert_reset(self):
        """Assert reset signal"""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.rst_n.value = 1

    def _init_config_signals(self, xfer_beats):
        """Initialize configuration signals before reset"""
        # Save xfer_beats for test use
        self.xfer_beats = xfer_beats

        # Configure transfer sizes
        self.dut.cfg_axi_rd_xfer_beats.value = xfer_beats
        self.dut.cfg_axi_wr_xfer_beats.value = xfer_beats

        # Enable all channels (vectored signal)
        channel_enable_mask = (1 << self.num_channels) - 1  # All channels enabled
        self.dut.cfg_channel_enable.value = channel_enable_mask

        # Scheduler configuration
        self.dut.cfg_sched_timeout_enable.value = 1
        self.dut.cfg_sched_timeout_cycles.value = 1000
        self.dut.cfg_sched_err_enable.value = 1
        self.dut.cfg_sched_compl_enable.value = 1
        self.dut.cfg_sched_perf_enable.value = 1

        # Descriptor engine configuration
        self.dut.cfg_desceng_enable.value = 1
        self.dut.cfg_desceng_prefetch.value = 1
        self.dut.cfg_desceng_fifo_thresh.value = 12  # 4-bit signal, max = 15
        # Note: Address limits not enabled by default
        self.dut.cfg_desceng_addr0_base.value = 0
        self.dut.cfg_desceng_addr0_limit.value = 0xFFFFFFFF
        self.dut.cfg_desceng_addr1_base.value = 0
        self.dut.cfg_desceng_addr1_limit.value = 0xFFFFFFFF

        self.log.info(f"Configured AXI transfer size: {xfer_beats} beats")

    async def _init_bfm_components(self):
        """Initialize AXI slave BFMs after reset"""

        # Create memory models
        self.desc_memory_model = MemoryModel(
            num_lines=16384,   # 512KB (16384 * 32 bytes)
            bytes_per_line=32, # 256-bit descriptors
            log=self.log
        )

        self.src_memory_model = MemoryModel(
            num_lines=262144,  # 16MB (262144 * data_bytes)
            bytes_per_line=self.data_bytes,
            log=self.log
        )

        self.dst_memory_model = MemoryModel(
            num_lines=262144,  # 16MB
            bytes_per_line=self.data_bytes,
            log=self.log
        )

        # Descriptor AXI slave (256-bit read-only)
        # NOTE: Pass base_addr so AXI slave subtracts it from incoming addresses
        # (RTL sends abs addr 0x10000, memory model expects offset 0)
        self.desc_axi_slave = create_axi4_slave_rd(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axi_desc",
            log=self.log,
            data_width=256,
            id_width=self.axi_id_width,
            addr_width=self.addr_width,
            user_width=1,
            multi_sig=True,
            memory_model=self.desc_memory_model,
            base_addr=self.desc_mem_base  # ← FIX: Subtract base from AXI addresses
        )
        self.desc_slave = self.desc_axi_slave['R']

        # Data read AXI slave (parameterizable width)
        self.rd_axi_slave = create_axi4_slave_rd(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axi_rd",
            log=self.log,
            data_width=self.data_width,
            id_width=self.axi_id_width,
            addr_width=self.addr_width,
            user_width=1,
            multi_sig=True,
            memory_model=self.src_memory_model,
            base_addr=self.src_mem_base  # ← FIX: Subtract base from AXI addresses
        )
        self.rd_slave = self.rd_axi_slave['R']

        # Data write AXI slave (parameterizable width)
        self.wr_axi_slave = create_axi4_slave_wr(
            dut=self.dut,
            clock=self.clk,
            prefix="m_axi_wr",
            log=self.log,
            data_width=self.data_width,
            id_width=self.axi_id_width,
            addr_width=self.addr_width,
            user_width=1,
            multi_sig=True,
            memory_model=self.dst_memory_model,
            base_addr=self.dst_mem_base  # ← FIX: Subtract base from AXI addresses
        )
        self.wr_slave = self.wr_axi_slave['W']

        self.log.info("Initialized AXI slave responders with memory models")

    async def _monitor_monbus(self):
        """Monitor MonBus packets"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            if hasattr(self.dut, 'mon_valid'):
                if int(self.dut.mon_valid.value) == 1:
                    pkt_data = int(self.dut.mon_packet.value)
                    self.mon_packets.append(pkt_data)
                    # TODO: Decode packet fields

    async def _monitor_apb_to_desc(self):
        """Monitor APB → Descriptor interface (channel kick-offs)"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            apb_valid = int(self.dut.apb_valid.value)
            apb_ready = int(self.dut.apb_ready.value)

            # Check each channel
            for ch in range(self.num_channels):
                if ((apb_valid >> ch) & 1) and ((apb_ready >> ch) & 1):
                    # Extract address for this channel
                    apb_addr_val = int(self.dut.apb_addr.value)
                    addr = (apb_addr_val >> (ch * self.addr_width)) & ((1 << self.addr_width) - 1)

                    txn = {
                        'time_ns': cocotb.utils.get_sim_time('ns'),
                        'channel': ch,
                        'addr': addr
                    }
                    self.apb_transactions.append(txn)
                    self.log.info(f"[APB→DESC] CH{ch}: Descriptor @ 0x{addr:08x}")

    async def _monitor_datard_interface(self):
        """Monitor Scheduler → Read Engine interface (datard)"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            # Access internal signals
            if not hasattr(self.dut, 'sched_rd_valid'):
                continue

            sched_rd_valid = int(self.dut.sched_rd_valid.value)
            sched_rd_ready = int(self.dut.sched_rd_ready.value)

            # Check each channel
            for ch in range(self.num_channels):
                if ((sched_rd_valid >> ch) & 1) and ((sched_rd_ready >> ch) & 1):
                    # Extract address and beats for this channel
                    addr_val = int(self.dut.sched_rd_addr.value)
                    beats_val = int(self.dut.sched_rd_beats.value)

                    addr = (addr_val >> (ch * self.addr_width)) & ((1 << self.addr_width) - 1)
                    beats = (beats_val >> (ch * 32)) & 0xFFFFFFFF

                    txn = {
                        'time_ns': cocotb.utils.get_sim_time('ns'),
                        'channel': ch,
                        'addr': addr,
                        'beats': beats
                    }
                    self.datard_requests.append(txn)
                    self.log.info(f"[DATARD_REQ] CH{ch}: addr=0x{addr:08x}, beats={beats}")

    async def _monitor_datawr_interface(self):
        """Monitor Scheduler → Write Engine interface (datawr)"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            # Access internal signals
            if not hasattr(self.dut, 'sched_wr_valid'):
                continue

            sched_wr_valid = int(self.dut.sched_wr_valid.value)
            sched_wr_ready = int(self.dut.sched_wr_ready.value)

            # Check each channel
            for ch in range(self.num_channels):
                if ((sched_wr_valid >> ch) & 1) and ((sched_wr_ready >> ch) & 1):
                    # Extract address and beats for this channel
                    addr_val = int(self.dut.sched_wr_addr.value)
                    beats_val = int(self.dut.sched_wr_beats.value)

                    addr = (addr_val >> (ch * self.addr_width)) & ((1 << self.addr_width) - 1)
                    beats = (beats_val >> (ch * 32)) & 0xFFFFFFFF

                    txn = {
                        'time_ns': cocotb.utils.get_sim_time('ns'),
                        'channel': ch,
                        'addr': addr,
                        'beats': beats
                    }
                    self.datawr_requests.append(txn)
                    self.log.info(f"[DATAWR_REQ] CH{ch}: addr=0x{addr:08x}, beats={beats}")

    async def _monitor_datard_completions(self):
        """Monitor Read Engine → Scheduler completions"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            # Access internal signals
            if not hasattr(self.dut, 'sched_rd_done_strobe'):
                continue

            done_strobe = int(self.dut.sched_rd_done_strobe.value)

            # Check each channel
            for ch in range(self.num_channels):
                if (done_strobe >> ch) & 1:
                    # Extract beats done for this channel
                    beats_done_val = int(self.dut.sched_rd_beats_done.value)
                    beats_done = (beats_done_val >> (ch * 32)) & 0xFFFFFFFF

                    txn = {
                        'time_ns': cocotb.utils.get_sim_time('ns'),
                        'channel': ch,
                        'beats_done': beats_done
                    }
                    self.datard_completions.append(txn)
                    self.log.info(f"[DATARD_DONE] CH{ch}: beats_done={beats_done}")

    async def _monitor_datawr_completions(self):
        """Monitor Write Engine → Scheduler completions"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            # Access internal signals
            if not hasattr(self.dut, 'sched_wr_done_strobe'):
                continue

            done_strobe = int(self.dut.sched_wr_done_strobe.value)

            # Check each channel
            for ch in range(self.num_channels):
                if (done_strobe >> ch) & 1:
                    # Extract beats done for this channel
                    beats_done_val = int(self.dut.sched_wr_beats_done.value)
                    beats_done = (beats_done_val >> (ch * 32)) & 0xFFFFFFFF

                    txn = {
                        'time_ns': cocotb.utils.get_sim_time('ns'),
                        'channel': ch,
                        'beats_done': beats_done
                    }
                    self.datawr_completions.append(txn)
                    self.log.info(f"[DATAWR_DONE] CH{ch}: beats_done={beats_done}")

    # =========================================================================
    # Descriptor Management
    # =========================================================================

    def write_descriptor(self, addr, src_addr, dst_addr, length,
                        next_ptr=0, priority=0, last=False, channel_id=0):
        """
        Write a descriptor to descriptor memory.

        Args:
            addr: Descriptor address (absolute address in descriptor memory region)
            src_addr: Source data address
            dst_addr: Destination data address
            length: Transfer length in BEATS
            next_ptr: Next descriptor address (0 = last)
            priority: Descriptor priority (0-7)
            last: Last descriptor flag
            channel_id: Channel ID (0-7)
        """
        # Build descriptor packet using builder
        packet = self.desc_builder.build_descriptor_packet(
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=length,
            next_ptr=next_ptr,
            valid=True,
            last=last,
            channel_id=channel_id,
            priority=priority
        )

        # Convert absolute address to memory model offset
        offset = addr - self.desc_mem_base

        # Write 256-bit descriptor to memory (32 bytes, little-endian)
        data_bytes = bytearray(packet.to_bytes(32, byteorder='little'))
        self.desc_memory_model.write(offset, data_bytes)

        # Debug: Verify write by reading back
        readback = self.desc_memory_model.read(offset, 32)
        readback_packet = int.from_bytes(bytes(readback), byteorder='little')

        self.log.info(f"Wrote descriptor @ abs_addr=0x{addr:08x} (offset=0x{offset:08x}): "
                     f"src=0x{src_addr:08x}, dst=0x{dst_addr:08x}, "
                     f"len={length} beats, next=0x{next_ptr:08x}, "
                     f"last={last}, ch={channel_id}")
        self.log.debug(f"  Written packet: 0x{packet:064X}")
        self.log.debug(f"  Readback packet: 0x{readback_packet:064X}")
        if packet != readback_packet:
            self.log.error(f"  MISMATCH! Write/read mismatch in descriptor memory!")

    def write_source_data(self, addr, data, num_bytes):
        """
        Write data to source memory.

        Args:
            addr: Starting address (absolute address in source memory region)
            data: Integer data value
            num_bytes: Number of bytes to write
        """
        # Convert absolute address to memory model offset
        offset = addr - self.src_mem_base

        data_bytes = bytearray(data.to_bytes(num_bytes, byteorder='little'))
        self.src_memory_model.write(offset, data_bytes)

    def read_dest_data(self, addr, num_bytes):
        """
        Read data from destination memory.

        Args:
            addr: Starting address (absolute address in destination memory region)
            num_bytes: Number of bytes to read

        Returns:
            int: Data value read from memory
        """
        # Convert absolute address to memory model offset
        offset = addr - self.dst_mem_base

        data_bytes = self.dst_memory_model.read(offset, num_bytes)
        data = int.from_bytes(bytes(data_bytes), byteorder='little')
        return data

    def verify_transfer(self, src_addr, dst_addr, num_beats):
        """
        Verify that destination data matches source data.

        Args:
            src_addr: Source address (absolute address in source memory region)
            dst_addr: Destination address (absolute address in destination memory region)
            num_beats: Number of beats to verify

        Returns:
            bool: True if all data matches
        """
        errors = 0
        for beat in range(num_beats):
            beat_src_addr = src_addr + (beat * self.data_bytes)
            beat_dst_addr = dst_addr + (beat * self.data_bytes)

            # Convert absolute addresses to memory model offsets
            src_offset = beat_src_addr - self.src_mem_base
            dst_offset = beat_dst_addr - self.dst_mem_base

            # Read entire beat from source and destination
            src_data_bytes = self.src_memory_model.read(src_offset, self.data_bytes)
            dst_data_bytes = self.dst_memory_model.read(dst_offset, self.data_bytes)

            src_data = int.from_bytes(bytes(src_data_bytes), byteorder='little')
            dst_data = int.from_bytes(bytes(dst_data_bytes), byteorder='little')

            if src_data != dst_data:
                self.log.error(f"Mismatch at beat {beat}: "
                              f"src=0x{src_data:0{self.data_bytes*2}x}, "
                              f"dst=0x{dst_data:0{self.data_bytes*2}x}")
                errors += 1

        if errors == 0:
            self.log.info(f"Verified {num_beats} beats: all data matches")
            return True
        else:
            self.log.error(f"Verification failed: {errors} mismatches out of {num_beats} beats")
            return False

    # =========================================================================
    # Channel Control
    # =========================================================================

    async def kick_off_channel(self, channel, descriptor_addr):
        """
        Kick off a DMA transfer on specified channel via per-channel control interface.

        Args:
            channel: Channel number (0 to num_channels-1)
            descriptor_addr: Address of first descriptor in chain
        """
        if channel >= self.num_channels:
            self.log.error(f"Invalid channel {channel}, max is {self.num_channels-1}")
            return

        # stream_core uses per-channel control signals (not standard APB)
        # Drive descriptor address with valid pulse

        await RisingEdge(self.clk)

        # Set channel's address and assert valid
        # Note: apb_addr, apb_valid, apb_ready are vectored per-channel
        current_apb_addr = self.dut.apb_addr.value
        current_apb_valid = self.dut.apb_valid.value

        # Create mutable copy
        apb_addr_list = [int((current_apb_addr >> (i * self.addr_width)) & ((1 << self.addr_width) - 1))
                        for i in range(self.num_channels)]
        apb_valid_list = [(current_apb_valid >> i) & 1 for i in range(self.num_channels)]

        # Update target channel
        apb_addr_list[channel] = descriptor_addr
        apb_valid_list[channel] = 1

        # Pack back into concatenated value
        new_apb_addr = 0
        for i in range(self.num_channels):
            new_apb_addr |= (apb_addr_list[i] << (i * self.addr_width))
        new_apb_valid = sum(bit << i for i, bit in enumerate(apb_valid_list))

        self.dut.apb_addr.value = new_apb_addr
        self.dut.apb_valid.value = new_apb_valid

        # Wait for ready
        for _ in range(100):  # Timeout after 100 cycles
            await RisingEdge(self.clk)
            await ReadOnly()
            apb_ready = self.dut.apb_ready.value
            if (apb_ready >> channel) & 1:
                break

        # Deassert valid
        await RisingEdge(self.clk)
        self.dut.apb_valid.value = current_apb_valid  # Restore previous value

        self.log.info(f"Kicked off channel {channel} with descriptor @ 0x{descriptor_addr:08x}")
        self.transfer_start_time[channel] = cocotb.utils.get_sim_time('ns')

    async def wait_for_channel_idle(self, channel, timeout_us=10000):
        """
        Wait for channel to return to idle state.

        Args:
            channel: Channel number
            timeout_us: Timeout in microseconds

        Returns:
            bool: True if channel idle, False on timeout
        """
        timeout_ns = timeout_us * 1000
        start_time = cocotb.utils.get_sim_time('ns')

        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            # Check channel status register via APB
            # TODO: Implement APB read when BFM available
            # For now, check internal signals if available

            # Simple timeout check
            current_time = cocotb.utils.get_sim_time('ns')
            if (current_time - start_time) > timeout_ns:
                self.log.error(f"Channel {channel} timeout waiting for idle")
                return False

            # TODO: Add proper idle detection
            # For now, just wait fixed time
            if (current_time - start_time) > 1000:  # 1us minimum
                self.transfer_end_time[channel] = current_time
                return True

    # =========================================================================
    # Test Helpers
    # =========================================================================

    def create_test_pattern(self, beat_index, pattern_type='increment'):
        """
        Create test data pattern for a beat.

        Args:
            beat_index: Beat number
            pattern_type: 'increment', 'random', 'walking_ones', etc.

        Returns:
            int: Data pattern for this beat
        """
        if pattern_type == 'increment':
            # Each byte is beat_index & 0xFF
            byte_val = beat_index & 0xFF
            data = byte_val * self.data_bytes
            return data
        elif pattern_type == 'walking_ones':
            # Walking ones pattern
            bit_pos = beat_index % self.data_width
            return (1 << bit_pos)
        elif pattern_type == 'address':
            # Use beat index as data (useful for debugging)
            return beat_index
        else:
            return 0

    def get_performance_stats(self, channel):
        """Get performance statistics for a channel"""
        if channel not in self.transfer_start_time:
            return None

        start = self.transfer_start_time[channel]
        end = self.transfer_end_time.get(channel, cocotb.utils.get_sim_time('ns'))
        duration = end - start

        return {
            'start_ns': start,
            'end_ns': end,
            'duration_ns': duration,
            'duration_us': duration / 1000.0
        }

    # =========================================================================
    # Monitor Data Access
    # =========================================================================

    def get_apb_transactions(self, channel=None):
        """Get APB transactions, optionally filtered by channel"""
        if channel is None:
            return self.apb_transactions
        return [txn for txn in self.apb_transactions if txn['channel'] == channel]

    def get_datard_requests(self, channel=None):
        """Get data read requests, optionally filtered by channel"""
        if channel is None:
            return self.datard_requests
        return [txn for txn in self.datard_requests if txn['channel'] == channel]

    def get_datawr_requests(self, channel=None):
        """Get data write requests, optionally filtered by channel"""
        if channel is None:
            return self.datawr_requests
        return [txn for txn in self.datawr_requests if txn['channel'] == channel]

    def get_datard_completions(self, channel=None):
        """Get data read completions, optionally filtered by channel"""
        if channel is None:
            return self.datard_completions
        return [txn for txn in self.datard_completions if txn['channel'] == channel]

    def get_datawr_completions(self, channel=None):
        """Get data write completions, optionally filtered by channel"""
        if channel is None:
            return self.datawr_completions
        return [txn for txn in self.datawr_completions if txn['channel'] == channel]

    def print_transaction_summary(self, channel=None):
        """
        Print summary of all monitored transactions.

        Args:
            channel: Optional channel filter (None = all channels)
        """
        ch_str = f"Channel {channel}" if channel is not None else "All Channels"
        self.log.info(f"\n{'='*80}")
        self.log.info(f"Transaction Summary - {ch_str}")
        self.log.info(f"{'='*80}")

        apb_txns = self.get_apb_transactions(channel)
        self.log.info(f"\nAPB Transactions (APB→Descriptor): {len(apb_txns)}")
        for txn in apb_txns:
            self.log.info(f"  {txn['time_ns']:10.0f}ns: CH{txn['channel']} @ 0x{txn['addr']:08x}")

        datard_reqs = self.get_datard_requests(channel)
        self.log.info(f"\nData Read Requests (Sched→ReadEng): {len(datard_reqs)}")
        for txn in datard_reqs:
            self.log.info(f"  {txn['time_ns']:10.0f}ns: CH{txn['channel']} addr=0x{txn['addr']:08x} beats={txn['beats']}")

        datawr_reqs = self.get_datawr_requests(channel)
        self.log.info(f"\nData Write Requests (Sched→WriteEng): {len(datawr_reqs)}")
        for txn in datawr_reqs:
            self.log.info(f"  {txn['time_ns']:10.0f}ns: CH{txn['channel']} addr=0x{txn['addr']:08x} beats={txn['beats']}")

        datard_compl = self.get_datard_completions(channel)
        self.log.info(f"\nData Read Completions (ReadEng→Sched): {len(datard_compl)}")
        for txn in datard_compl:
            self.log.info(f"  {txn['time_ns']:10.0f}ns: CH{txn['channel']} beats_done={txn['beats_done']}")

        datawr_compl = self.get_datawr_completions(channel)
        self.log.info(f"\nData Write Completions (WriteEng→Sched): {len(datawr_compl)}")
        for txn in datawr_compl:
            self.log.info(f"  {txn['time_ns']:10.0f}ns: CH{txn['channel']} beats_done={txn['beats_done']}")

        self.log.info(f"\n{'='*80}\n")
