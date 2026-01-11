"""
Stream Top Testbench - STREAM DMA with APB Configuration Interface

This testbench extends StreamCoreTB to test the complete stream_top module
which includes APB configuration registers, kick-off interface, and the
stream_core datapath.

Features:
- APB4 master BFM for configuration access
- APB kick-off writes to start channels
- PeakRDL register access (when implemented)
- Reuses StreamCoreTB for datapath testing

Author: RTL Design Sherpa
Date: 2025-11-25
"""

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
import sys
import os

# Import framework utilities (PYTHONPATH includes bin/)
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr
from CocoTBFramework.components.apb.apb_factories import create_apb_master
from CocoTBFramework.components.apb.apb_packet import APBPacket
from projects.components.stream.dv.tbclasses.descriptor_packet_builder import DescriptorPacketBuilder
from projects.components.stream.rtl.stream_helper import StreamHelper


class StreamTopTB(TBBase):
    """
    Testbench for stream_top - Complete STREAM DMA with APB configuration.

    This testbench tests the full stream_top module including:
    - APB4 configuration interface
    - Channel kick-off via APB writes
    - PeakRDL register access (placeholder until generated)
    - Complete datapath (descriptor fetch, read data, write data)

    The testbench reuses patterns from StreamCoreTB but adds APB configuration
    layer on top.

    Attributes:
        num_channels: Number of DMA channels (1-8, default 8)
        addr_width: Address bus width (default 64)
        data_width: Data bus width (default 512)
        axi_id_width: AXI ID width (default 8)
        fifo_depth: Internal FIFO depth (default 4096)
        apb_addr_width: APB address width (default 12 for 4KB space)
        apb_data_width: APB data width (default 32)
    """

    def __init__(self, dut,
                 num_channels=8,
                 addr_width=64,
                 data_width=512,
                 axi_id_width=8,
                 fifo_depth=4096,
                 apb_addr_width=12,
                 apb_data_width=32,
                 **kwargs):
        """Initialize stream_top testbench"""
        super().__init__(dut)

        # Save parameters
        self.num_channels = num_channels
        self.addr_width = addr_width
        self.data_width = data_width
        self.axi_id_width = axi_id_width
        self.fifo_depth = fifo_depth
        self.apb_addr_width = apb_addr_width
        self.apb_data_width = apb_data_width
        self.data_bytes = data_width // 8
        # AXI user width must match channel encoding
        self.user_width = max(1, (num_channels - 1).bit_length()) if num_channels > 1 else 1

        # Clock/reset - stream_top uses both aclk/aresetn and pclk/presetn
        self.aclk = dut.aclk
        self.aresetn = dut.aresetn
        self.pclk = dut.pclk      # APB clock (may be same as aclk)
        self.presetn = dut.presetn # APB reset
        self.clk_name = 'aclk'

        # Memory maps (same as StreamCoreTB)
        self.desc_mem_base = 0x0001_0000  # Descriptor base (64KB offset)
        self.desc_mem_size = 0x0001_0000  # 64KB descriptor memory
        self.src_mem_base = 0x8000_0000   # Source data base
        self.src_mem_size = 0x0200_0000   # 32MB source memory
        self.dst_mem_base = 0x9000_0000   # Destination data base
        self.dst_mem_size = 0x0200_0000   # 32MB destination memory

        # APB address map (from stream_top_ch8.sv)
        self.apb_kickoff_base = 0x000  # 0x000-0x01F: Channel kick-off
        self.apb_regs_base = 0x100     # 0x100-0x3FF: Configuration registers

        # Memory models (MemoryModel objects - initialized in setup)
        self.desc_memory_model = None
        self.src_memory_model = None
        self.dst_memory_model = None

        # BFM components
        self.apb_master = None      # APB4 master for configuration
        self.desc_axi_slave = None  # AXI4 slave for descriptor fetches (256-bit)
        self.rd_axi_slave = None    # AXI4 slave for data reads
        self.wr_axi_slave = None    # AXI4 slave for data writes
        self.desc_slave = None      # R channel from desc_axi_slave
        self.rd_slave = None        # R channel from rd_axi_slave
        self.wr_slave = None        # W+B channels from wr_axi_slave

        # Descriptor builder
        self.desc_builder = DescriptorPacketBuilder()

        # StreamHelper for configuration (HPET methodology)
        self.stream_helper = None  # Initialized after logger is available

        # Performance tracking
        self.transfer_start_time = {}
        self.transfer_end_time = {}

        # Transaction capture
        self.apb_transactions = []
        self.apb_config_writes = []   # Track configuration register writes
        self.apb_kickoff_writes = []  # Track channel kick-off writes

    async def setup_clocks_and_reset(self, rd_xfer_beats=16, wr_xfer_beats=16):
        """
        Complete initialization for stream_top testbench.

        Sequence:
        1. Start clocks (aclk and pclk - may be same clock)
        2. Initialize configuration signals before reset
        3. Assert reset
        4. Deassert reset
        5. Initialize APB master and AXI slave responders
        6. Configure stream_top via APB registers

        Args:
            rd_xfer_beats: AXI read transfer size in beats (default 16)
            wr_xfer_beats: AXI write transfer size in beats (default 16)
        """
        # Start clocks
        await self.start_clock('aclk', freq=10, units='ns')
        # For now, assume pclk is same as aclk (can be extended for CDC testing)
        # If pclk is separate, start it here

        # Initialize configuration signals before reset (not driven by TB for stream_top)
        # stream_top gets config from internal PeakRDL registers

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

        # Initialize BFM components after reset
        await self._init_bfm_components(rd_xfer_beats, wr_xfer_beats)

        # Configure stream_top via APB (enable channels, set burst sizes, etc.)
        await self._configure_stream_top(rd_xfer_beats, wr_xfer_beats)

        # Start background monitors
        cocotb.start_soon(self._monitor_apb_transactions())
        cocotb.start_soon(self._monitor_interrupts())

        self.log.info(f"stream_top TB initialized: {self.num_channels} channels, "
                     f"{self.data_width}-bit data, {self.fifo_depth}-deep FIFO")
        self.log.info("APB configuration and AXI slave responders ready")

    async def assert_reset(self):
        """Assert both AXI and APB reset signals"""
        self.aresetn.value = 0
        self.presetn.value = 0

    async def deassert_reset(self):
        """Deassert both AXI and APB reset signals"""
        self.aresetn.value = 1
        self.presetn.value = 1

    async def _init_bfm_components(self, rd_xfer_beats=16, wr_xfer_beats=16):
        """
        Initialize APB master and AXI slave responders.

        Args:
            rd_xfer_beats: Read transfer size in beats
            wr_xfer_beats: Write transfer size in beats
        """
        # Create memory models
        self.desc_memory_model = MemoryModel(
            name="desc_mem",
            data_width=256,  # Descriptor fetch is always 256-bit
            size=self.desc_mem_size,
            log=self.log
        )

        self.src_memory_model = MemoryModel(
            name="src_mem",
            data_width=self.data_width,
            size=self.src_mem_size,
            log=self.log
        )

        self.dst_memory_model = MemoryModel(
            name="dst_mem",
            data_width=self.data_width,
            size=self.dst_mem_size,
            log=self.log
        )

        # Create APB master BFM using factory
        self.apb_master = create_apb_master(
            dut=self.dut,
            title="APB Master",
            prefix="s_apb",
            clock=self.pclk,
            addr_width=self.apb_addr_width,
            data_width=self.apb_data_width,
            log=self.log
        )

        # Create AXI slave responders (same pattern as StreamCoreTB)
        self.desc_axi_slave = create_axi4_slave_rd(
            dut=self.dut,
            prefix="m_axi_desc",
            clock=self.aclk,
            reset=self.aresetn,
            memory_model=self.desc_memory_model,
            base_addr=self.desc_mem_base,  # FIXED: base_addr not base_address
            data_width=256,  # Descriptor width
            addr_width=self.addr_width,
            id_width=self.axi_id_width,
            log=self.log
        )
        self.desc_slave = self.desc_axi_slave['r']

        self.rd_axi_slave = create_axi4_slave_rd(
            dut=self.dut,
            prefix="m_axi_rd",
            clock=self.aclk,
            reset=self.aresetn,
            memory_model=self.src_memory_model,
            base_addr=self.src_mem_base,  # FIXED: base_addr not base_address
            data_width=self.data_width,
            addr_width=self.addr_width,
            id_width=self.axi_id_width,
            log=self.log
        )
        self.rd_slave = self.rd_axi_slave['r']

        self.wr_axi_slave = create_axi4_slave_wr(
            dut=self.dut,
            prefix="m_axi_wr",
            clock=self.aclk,
            reset=self.aresetn,
            memory_model=self.dst_memory_model,
            base_addr=self.dst_mem_base,  # FIXED: base_addr not base_address
            data_width=self.data_width,
            addr_width=self.addr_width,
            id_width=self.axi_id_width,
            log=self.log
        )
        self.wr_slave = self.wr_axi_slave['w']

        self.log.info("BFM components initialized (APB master, AXI slaves)")

    async def _configure_stream_top(self, rd_xfer_beats=16, wr_xfer_beats=16):
        """
        Configure stream_top via APB registers using StreamHelper.

        Uses HPET-style methodology with StreamHelper for clean configuration.

        Args:
            rd_xfer_beats: Read transfer size in beats (ARLEN value)
            wr_xfer_beats: Write transfer size in beats (AWLEN value)
        """
        # Initialize StreamHelper
        self.stream_helper = StreamHelper(log=self.log)

        # Apply default configuration
        self.stream_helper.enable_global(True)
        self.stream_helper.enable_channels(0xFF)  # All 8 channels
        self.stream_helper.configure_scheduler(enable=True, timeout_en=True,
                                               err_en=True, compl_en=True)
        self.stream_helper.set_scheduler_timeout(1000)
        self.stream_helper.configure_descriptor_engine(enable=True, prefetch=False)
        self.stream_helper.set_address_range_0(0x00000000, 0xFFFFFFFF)
        self.stream_helper.set_address_range_1(0x00000000, 0xFFFFFFFF)
        self.stream_helper.configure_axi_transfers(rd_beats=rd_xfer_beats - 1,
                                                   wr_beats=wr_xfer_beats - 1)

        # Generate and send APB writes
        apb_cycles = self.stream_helper.generate_apb_cycles()
        for addr, data in apb_cycles:
            success, error = await self.apb_write(addr, data)
            if not success:
                self.log.error(f"APB write failed: addr=0x{addr:03X}, data=0x{data:08X}")

        self.log.info(f"stream_top configured via StreamHelper: "
                     f"rd_xfer={rd_xfer_beats}, wr_xfer={wr_xfer_beats}")

    async def apb_write(self, addr, data):
        """
        Write to APB register.

        Args:
            addr: APB address (12-bit)
            data: Write data (32-bit)

        Returns:
            (success, error) tuple
        """
        # Create APB write packet (match HPET pattern exactly)
        pkt = APBPacket(
            pwrite=1,  # Write operation
            paddr=addr,
            pwdata=data,
            pstrb=0xF,  # All 4 bytes enabled for 32-bit
            pprot=0,    # Protection signal
            data_width=self.apb_data_width,  # 32-bit
            addr_width=self.apb_addr_width,  # 12-bit
            strb_width=4  # 4-byte strobe width
        )

        # Send packet via APB master
        await self.apb_master.send(pkt)

        # Extract error status from packet after transaction completes
        error = pkt.fields.get('pslverr', 0)
        success = (error == 0)

        # Track configuration vs kick-off writes
        if addr >= self.apb_regs_base:
            self.apb_config_writes.append({'addr': addr, 'data': data, 'error': error})
        else:
            self.apb_kickoff_writes.append({'addr': addr, 'data': data, 'error': error})

        return success, error

    async def apb_read(self, addr):
        """
        Read from APB register.

        Args:
            addr: APB address (12-bit)

        Returns:
            (data, error) tuple
        """
        # Create APB read packet (match HPET pattern exactly)
        pkt = APBPacket(
            pwrite=0,  # Read operation
            paddr=addr,
            pwdata=0,  # Not used for reads, but included for consistency
            pstrb=0xF,  # All 4 bytes enabled for 32-bit
            pprot=0,    # Protection signal
            data_width=self.apb_data_width,  # 32-bit
            addr_width=self.apb_addr_width,  # 12-bit
            strb_width=4  # 4-byte strobe width
        )

        # Send packet via APB master
        await self.apb_master.send(pkt)

        # Extract read data and error status from packet after transaction completes
        data = pkt.fields.get('prdata', 0)
        error = pkt.fields.get('pslverr', 0)

        return data, error

    async def kick_off_channel(self, channel, desc_addr):
        """
        Kick off a DMA channel via APB write to kick-off register.

        Args:
            channel: Channel number (0-7)
            desc_addr: Descriptor address (64-bit, written as 2x 32-bit APB writes)
        """
        if channel >= self.num_channels:
            raise ValueError(f"Invalid channel {channel} (max {self.num_channels-1})")

        # APB kick-off address map (from apbtodescr.sv):
        # Channel N: Base + (N * 8)
        #   Offset +0: Lower 32 bits of descriptor address
        #   Offset +4: Upper 32 bits of descriptor address
        base_addr = self.apb_kickoff_base + (channel * 8)

        # Write lower 32 bits
        lower = desc_addr & 0xFFFFFFFF
        await self.apb_write(base_addr + 0, lower)

        # Write upper 32 bits
        upper = (desc_addr >> 32) & 0xFFFFFFFF
        await self.apb_write(base_addr + 4, upper)

        self.transfer_start_time[channel] = cocotb.utils.get_sim_time('ns')
        self.log.info(f"Channel {channel} kicked off: desc_addr=0x{desc_addr:016X}")

    async def wait_for_channel_idle(self, channel, timeout_us=10000):
        """
        Wait for channel to complete and return to idle.

        Note: This monitors the channel_interrupt signal from stream_top.
        When interrupt fires, channel has completed.

        Args:
            channel: Channel number (0-7)
            timeout_us: Timeout in microseconds
        """
        timeout_ns = timeout_us * 1000
        start_time = cocotb.utils.get_sim_time('ns')

        # Wait for interrupt signal to assert for this channel
        while True:
            await RisingEdge(self.aclk)
            await ReadOnly()

            # Check interrupt signal
            if self.dut.channel_interrupt.value & (1 << channel):
                self.transfer_end_time[channel] = cocotb.utils.get_sim_time('ns')
                self.log.info(f"Channel {channel} completed (interrupt fired)")
                break

            # Check timeout
            elapsed = cocotb.utils.get_sim_time('ns') - start_time
            if elapsed > timeout_ns:
                raise TimeoutError(f"Channel {channel} timeout after {timeout_us}us")

            # Check every 100 cycles to avoid excessive polling
            await self.wait_clocks('aclk', 100)

    def write_descriptor(self, addr, src_addr, dst_addr, length, next_ptr=0,
                        priority=0, last=False, interrupt=False):
        """
        Write descriptor to descriptor memory.

        Args:
            addr: Descriptor address in memory
            src_addr: Source address (64-bit)
            dst_addr: Destination address (64-bit)
            length: Transfer length in beats
            next_ptr: Next descriptor pointer (0 = last)
            priority: Descriptor priority (0-255)
            last: Last descriptor flag
            interrupt: Generate interrupt on completion
        """
        # Build descriptor using DescriptorPacketBuilder
        desc_data = self.desc_builder.build_descriptor(
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=length,
            next_descriptor_ptr=next_ptr,
            priority=priority,
            last=last,
            interrupt=interrupt,
            valid=True
        )

        # Write to descriptor memory (256 bits = 32 bytes)
        offset = addr - self.desc_mem_base
        self.desc_memory_model.write(offset, desc_data, 32)

        self.log.debug(f"Wrote descriptor @ 0x{addr:08X}: src=0x{src_addr:016X}, "
                      f"dst=0x{dst_addr:016X}, len={length}, next=0x{next_ptr:08X}")

    def write_source_data(self, addr, data, size):
        """
        Write data to source memory.

        Args:
            addr: Address in source memory
            data: Data value (integer)
            size: Size in bytes
        """
        offset = addr - self.src_mem_base
        self.src_memory_model.write(offset, data, size)

    def read_destination_data(self, addr, size):
        """
        Read data from destination memory.

        Args:
            addr: Address in destination memory
            size: Size in bytes

        Returns:
            Data value (integer)
        """
        offset = addr - self.dst_mem_base
        return self.dst_memory_model.read(offset, size)

    def verify_transfer(self, src_addr, dst_addr, num_beats):
        """
        Verify that data was correctly transferred from source to destination.

        Args:
            src_addr: Source address
            dst_addr: Destination address
            num_beats: Number of beats to verify

        Returns:
            True if all data matches, False otherwise
        """
        all_match = True

        for beat in range(num_beats):
            src_offset = (src_addr - self.src_mem_base) + (beat * self.data_bytes)
            dst_offset = (dst_addr - self.dst_mem_base) + (beat * self.data_bytes)

            src_data = self.src_memory_model.read(src_offset, self.data_bytes)
            dst_data = self.dst_memory_model.read(dst_offset, self.data_bytes)

            if src_data != dst_data:
                self.log.error(f"Mismatch at beat {beat}: src=0x{src_data:X}, dst=0x{dst_data:X}")
                all_match = False

        return all_match

    def get_performance_stats(self, channel):
        """
        Get performance statistics for a channel.

        Args:
            channel: Channel number

        Returns:
            Dictionary with start_time, end_time, duration
        """
        if channel not in self.transfer_start_time:
            return None

        start = self.transfer_start_time[channel]
        end = self.transfer_end_time.get(channel, cocotb.utils.get_sim_time('ns'))

        return {
            'start_time': start,
            'end_time': end,
            'duration_ns': end - start
        }

    async def _monitor_apb_transactions(self):
        """Background monitor for APB transactions"""
        while True:
            await RisingEdge(self.pclk)
            await ReadOnly()

            # Capture APB transactions (PSEL && PENABLE)
            if self.dut.s_apb_psel.value and self.dut.s_apb_penable.value:
                txn = {
                    'time': cocotb.utils.get_sim_time('ns'),
                    'addr': int(self.dut.s_apb_paddr.value),
                    'write': bool(self.dut.s_apb_pwrite.value),
                    'data': int(self.dut.s_apb_pwdata.value) if self.dut.s_apb_pwrite.value else None,
                    'rdata': int(self.dut.s_apb_prdata.value) if not self.dut.s_apb_pwrite.value else None,
                    'error': bool(self.dut.s_apb_pslverr.value)
                }
                self.apb_transactions.append(txn)

    async def _monitor_interrupts(self):
        """Background monitor for channel interrupts"""
        prev_interrupts = 0

        while True:
            await RisingEdge(self.aclk)
            await ReadOnly()

            curr_interrupts = int(self.dut.channel_interrupt.value)

            # Detect rising edges on interrupt bits
            rising = curr_interrupts & ~prev_interrupts

            if rising:
                for ch in range(self.num_channels):
                    if rising & (1 << ch):
                        self.log.info(f"Channel {ch} interrupt fired @ {cocotb.utils.get_sim_time('ns')}ns")

            prev_interrupts = curr_interrupts
