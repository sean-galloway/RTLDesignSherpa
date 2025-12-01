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


class StreamRegisterMap:
    """STREAM Register address definitions - PeakRDL generated registers."""

    # Channel kick-off registers (0x000-0x03F) - handled by apbtodescr.sv
    # These are NOT PeakRDL registers - used by existing kick_off_channel() method
    CH0_CTRL_LOW = 0x000
    CH0_CTRL_HIGH = 0x004
    # ... (repeat for channels 1-7, stride = 0x008)

    # Global Control and Status (0x100+) - PeakRDL registers
    GLOBAL_CTRL = 0x100
    GLOBAL_STATUS = 0x104
    VERSION = 0x108

    # Per-Channel Control (0x120+)
    CHANNEL_ENABLE = 0x120
    CHANNEL_RESET = 0x124

    # Per-Channel Status (0x140+) - must match stream_regs.rdl!
    CHANNEL_IDLE = 0x140      # CHANNEL_IDLE @ 0x140
    DESC_ENGINE_IDLE = 0x144  # DESC_ENGINE_IDLE @ 0x144
    SCHEDULER_IDLE = 0x148    # SCHEDULER_IDLE @ 0x148

    # Descriptor Engine Configuration (0x220+)
    DESCENG_CONFIG = 0x220
    DESCENG_ADDR0_BASE = 0x224   # Base address (lower 32 bits only)
    DESCENG_ADDR0_LIMIT = 0x228  # Limit address (lower 32 bits only)
    DESCENG_ADDR1_BASE = 0x22C
    DESCENG_ADDR1_LIMIT = 0x230

    # AXI Transfer Configuration (0x2A0)
    AXI_XFER_CONFIG = 0x2A0  # RD_XFER_BEATS[7:0], WR_XFER_BEATS[15:8]

    # Per-Channel State (0x160+)
    # CH_STATE is an array: 0x160 + (channel * 4)

    @classmethod
    def get_ch_ctrl_low_addr(cls, channel: int) -> int:
        """Get channel control low register address (kick-off)."""
        return 0x000 + (channel * 0x008)

    @classmethod
    def get_ch_ctrl_high_addr(cls, channel: int) -> int:
        """Get channel control high register address (kick-off)."""
        return 0x004 + (channel * 0x008)

    @classmethod
    def get_ch_state_addr(cls, channel: int) -> int:
        """Get channel state register address."""
        return 0x160 + (channel * 0x004)

    @classmethod
    def get_register_name(cls, addr: int) -> str:
        """Get human-readable register name."""
        if addr == cls.GLOBAL_CTRL:
            return "GLOBAL_CTRL"
        elif addr == cls.GLOBAL_STATUS:
            return "GLOBAL_STATUS"
        elif addr == cls.VERSION:
            return "VERSION"
        elif addr == cls.CHANNEL_ENABLE:
            return "CHANNEL_ENABLE"
        elif addr == cls.CHANNEL_RESET:
            return "CHANNEL_RESET"
        elif addr == cls.DESC_ENGINE_IDLE:
            return "DESC_ENGINE_IDLE"
        elif addr == cls.SCHEDULER_IDLE:
            return "SCHEDULER_IDLE"
        elif addr == cls.CHANNEL_IDLE:
            return "CHANNEL_IDLE"
        elif addr == cls.AXI_XFER_CONFIG:
            return "AXI_XFER_CONFIG"
        else:
            # Check if it's a channel-specific register
            for ch in range(8):
                if addr == cls.get_ch_ctrl_low_addr(ch):
                    return f"CH{ch}_CTRL_LOW"
                elif addr == cls.get_ch_ctrl_high_addr(ch):
                    return f"CH{ch}_CTRL_HIGH"
                elif addr == cls.get_ch_state_addr(ch):
                    return f"CH{ch}_STATE"
        return f"UNKNOWN_0x{addr:03X}"


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
        # AXI user width must match channel encoding (same as RTL)
        self.user_width = max(1, (num_channels - 1).bit_length()) if num_channels > 1 else 1

        # Clock/reset - auto-detect stream_core vs stream_top
        # stream_core: clk/rst_n
        # stream_top: aclk/aresetn (and pclk/presetn for APB)
        if hasattr(dut, 'clk'):
            # stream_core
            self.clk = dut.clk
            self.rst_n = dut.rst_n
            self.clk_name = 'clk'
            self.pclk = None
            self.presetn = None
        elif hasattr(dut, 'aclk'):
            # stream_top
            self.clk = dut.aclk
            self.rst_n = dut.aresetn
            self.clk_name = 'aclk'
            # Detect APB clock domain
            self.pclk = dut.pclk if hasattr(dut, 'pclk') else None
            self.presetn = dut.presetn if hasattr(dut, 'presetn') else None
        else:
            raise RuntimeError("DUT has neither 'clk' nor 'aclk' - unsupported module")

        # Memory maps
        # NOTE: Descriptor base must be non-zero (address 0 is invalid/error)
        self.desc_mem_base = 0x0001_0000  # Start at 64KB (address 0 reserved as invalid)
        self.desc_mem_size = 0x0001_0000  # 64KB
        self.src_mem_base = 0x8000_0000
        self.src_mem_size = 0x0200_0000   # 32MB
        self.dst_mem_base = 0x9000_0000
        self.dst_mem_size = 0x0200_0000   # 32MB

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

        # APB Master (for stream_top configuration, initialized separately)
        self.apb_master = None

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

    async def setup_clocks_and_reset(self, rd_xfer_beats=16, wr_xfer_beats=16):
        """
        Complete initialization following datapath pattern.

        Args:
            rd_xfer_beats: AXI read transfer size in beats (default 16)
            wr_xfer_beats: AXI write transfer size in beats (default 16)
        """
        # Start main clock (aclk or clk)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Start APB clock if present (stream_top has separate pclk domain)
        if self.pclk is not None:
            await self.start_clock('pclk', freq=10, units='ns')
            self.log.info("Started APB clock (pclk) @ 10ns period")

        # Initialize configuration signals ONLY for stream_core
        # stream_top configures via APB registers, not direct signals
        if self.pclk is None:
            # stream_core: has direct config signal ports
            self._init_config_signals(rd_xfer_beats, wr_xfer_beats)
        else:
            # stream_top: will configure via APB after reset
            # Just save parameters for later APB configuration
            self.rd_xfer_beats = rd_xfer_beats
            self.wr_xfer_beats = wr_xfer_beats
            self.log.info("stream_top: Deferring config to APB register writes")

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
        cocotb.start_soon(self._monitor_scheduler_state())
        cocotb.start_soon(self._monitor_descriptor_errors())
        cocotb.start_soon(self._monitor_wlast_channel_tracking())

        self.log.info(f"stream_core TB initialized: {self.num_channels} channels, "
                    f"{self.data_width}-bit data, {self.fifo_depth}-deep FIFO")
        self.log.info("Background monitors started for APB, datard, datawr, scheduler state, descriptor errors")

    async def assert_reset(self):
        """Assert reset signal(s)"""
        self.rst_n.value = 0
        # Also assert APB reset if present (stream_top)
        if self.presetn is not None:
            self.presetn.value = 0

    async def deassert_reset(self):
        """Deassert reset signal(s)"""
        self.rst_n.value = 1
        # Also deassert APB reset if present (stream_top)
        if self.presetn is not None:
            self.presetn.value = 1

    def _init_config_signals(self, rd_xfer_beats, wr_xfer_beats):
        """Initialize configuration signals before reset"""
        # Save burst sizes for test use
        self.rd_xfer_beats = rd_xfer_beats
        self.wr_xfer_beats = wr_xfer_beats

        # Configure transfer sizes (can be different for read and write)
        # Config register stores ARLEN values (0==1 beat per AXI spec), so subtract 1 from beat count
        self.dut.cfg_axi_rd_xfer_beats.value = rd_xfer_beats - 1
        self.dut.cfg_axi_wr_xfer_beats.value = wr_xfer_beats - 1

        # Enable all channels (vectored signal)
        channel_enable_mask = (1 << self.num_channels) - 1  # All channels enabled
        self.dut.cfg_channel_enable.value = channel_enable_mask

        # Scheduler configuration
        self.dut.cfg_sched_timeout_enable.value = 1
        self.dut.cfg_sched_timeout_cycles.value = 0xFFFF
        self.dut.cfg_sched_err_enable.value = 1
        self.dut.cfg_sched_compl_enable.value = 1
        self.dut.cfg_sched_perf_enable.value = 1

        # Descriptor engine configuration
        self.dut.cfg_desceng_enable.value = 1
        self.dut.cfg_desceng_prefetch.value = 1
        self.dut.cfg_desceng_fifo_thresh.value = 12  # 4-bit signal, max = 15
        # NOTE: Base addresses MUST match memory layout!
        # Descriptor memory starts at 0x0001_0000
        self.dut.cfg_desceng_addr0_base.value = self.desc_mem_base
        self.dut.cfg_desceng_addr0_limit.value = self.desc_mem_base + self.desc_mem_size - 1
        self.dut.cfg_desceng_addr1_base.value = 0
        self.dut.cfg_desceng_addr1_limit.value = 0xFFFFFFFF

        self.log.info(f"Configured AXI transfer sizes: RD={rd_xfer_beats} beats, WR={wr_xfer_beats} beats")

    async def _init_bfm_components(self):
        """Initialize AXI slave BFMs after reset"""

        # Create memory models
        self.desc_memory_model = MemoryModel(
            num_lines=16384,   # 512KB (16384 * 32 bytes)
            bytes_per_line=32, # 256-bit descriptors
            log=self.log
        )

        self.src_memory_model = MemoryModel(
            num_lines=524288,  # 32MB (524288 * data_bytes when data_bytes=64)
            bytes_per_line=self.data_bytes,
            log=self.log
        )

        self.dst_memory_model = MemoryModel(
            num_lines=524288,  # 32MB (524288 * data_bytes when data_bytes=64)
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
            ifc_name="descr",  # Debug name for logs
            data_width=256,
            id_width=self.axi_id_width,
            addr_width=self.addr_width,
            user_width=self.user_width,  # Channel ID encoding width
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
            ifc_name="rdeng",  # Debug name for logs
            data_width=self.data_width,
            id_width=self.axi_id_width,
            addr_width=self.addr_width,
            user_width=self.user_width,  # Channel ID encoding width
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
            ifc_name="wreng",  # Debug name for logs
            data_width=self.data_width,
            id_width=self.axi_id_width,
            addr_width=self.addr_width,
            user_width=self.user_width,  # Channel ID encoding width
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
                    time_str = self.get_time_ns_str()
                    self.log.info(f"{time_str} [APB→DESC] CH{ch}: Descriptor @ 0x{addr:08x}")

    async def _monitor_datard_interface(self):
        """Monitor Scheduler → Read Engine interface (datard)"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            # Access internal signals
            if not hasattr(self.dut, 'sched_rd_valid'):
                continue

            sched_rd_valid = int(self.dut.sched_rd_valid.value)

            # Check each channel for valid requests (no ready signal on read interface)
            for ch in range(self.num_channels):
                if ((sched_rd_valid >> ch) & 1):
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
                    time_str = self.get_time_ns_str()
                    self.log.info(f"{time_str} [DATARD_REQ] CH{ch}: addr=0x{addr:08x}, beats={beats}")

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
                    time_str = self.get_time_ns_str()
                    self.log.info(f"{time_str} [DATAWR_REQ] CH{ch}: addr=0x{addr:08x}, beats={beats}")

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
                    time_str = self.get_time_ns_str()
                    self.log.info(f"{time_str} [DATARD_DONE] CH{ch}: beats_done={beats_done}")

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
                    time_str = self.get_time_ns_str()
                    self.log.info(f"{time_str} [DATAWR_DONE] CH{ch}: beats_done={beats_done}")

    async def _monitor_scheduler_state(self):
        """Monitor scheduler FSM state for debugging (ONE-HOT ENCODED)"""
        last_state = {}

        # State decode mapping (one-hot encoding)
        # Updated to match stream_pkg.sv after concurrent read/write fix
        state_names = {
            0b0000001: "IDLE",
            0b0000010: "FETCH_DESC",
            0b0000100: "XFER_DATA",    # Concurrent read+write (was READ_DATA/WRITE_DATA)
            0b0001000: "COMPLETE",
            0b0010000: "NEXT_DESC",
            0b0100000: "ERROR",
            0b1000000: "RESERVED"
        }

        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            if not hasattr(self.dut, 'scheduler_state'):
                continue

            # scheduler_state is vectored - one 7-bit one-hot state per channel
            state_vec = int(self.dut.scheduler_state.value)

            for ch in range(self.num_channels):
                # Extract 7-bit one-hot state for this channel
                state = (state_vec >> (ch * 7)) & 0x7F

                # Only log on state changes
                if ch not in last_state or last_state[ch] != state:
                    last_state[ch] = state
                    time_str = self.get_time_ns_str()
                    state_name = state_names.get(state, f"UNKNOWN({state:07b})")
                    self.log.info(f"{time_str} [SCHED_STATE] CH{ch}: {state_name} (0b{state:07b})")

    async def _monitor_wlast_channel_tracking(self):
        """
        Monitor wlast rising edges and log which channel the W burst belongs to.

        This helps debug W beat matching in the transaction extraction script.
        Logs the internal r_w_channel_id from axi_write_engine when wlast asserts.
        """
        last_wlast = 0
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()  # Wait for signals to settle

            # Check if m_axi_wr signals exist
            try:
                wlast = int(self.dut.m_axi_wr_wlast.value)
                wvalid = int(self.dut.m_axi_wr_wvalid.value)
                wready = int(self.dut.m_axi_wr_wready.value)
            except AttributeError:
                # Signals don't exist, skip
                continue

            # Detect wlast rising edge with valid handshake
            if wlast and wvalid and wready and not last_wlast:
                # Rising edge on wlast
                try:
                    # Try multiple possible signal paths for channel ID
                    # PIPELINE=1: gen_w_pipeline.r_current_drain_id
                    # PIPELINE=0: gen_w_state_pipeline0.r_w_channel_id
                    try:
                        channel_id = int(self.dut.u_axi_write_engine.gen_w_pipeline.r_current_drain_id.value)
                    except AttributeError:
                        try:
                            channel_id = int(self.dut.u_axi_write_engine.gen_w_state_pipeline0.r_w_channel_id.value)
                        except AttributeError:
                            # Last resort: try the combinational wire
                            channel_id = int(self.dut.u_axi_write_engine.r_w_channel_id.value)

                    time_str = self.get_time_ns_str()
                    self.log.info(f"{time_str} [WLAST] Channel {channel_id} completed W burst")
                except (AttributeError, ValueError) as e:
                    # If we can't access internal signal, just log that wlast occurred
                    time_str = self.get_time_ns_str()
                    self.log.info(f"{time_str} [WLAST] W burst completed (channel ID not accessible: {e})")

            last_wlast = wlast if (wvalid and wready) else last_wlast

    async def _monitor_descriptor_errors(self):
        """Monitor descriptor engine error signals"""
        while True:
            await RisingEdge(self.clk)
            await ReadOnly()

            # Check descriptor AXI error signals
            if hasattr(self.dut, 'cfg_sts_desc_axi_conflict_error'):
                conflict_err = int(self.dut.cfg_sts_desc_axi_conflict_error.value)
                if conflict_err != 0:
                    time_str = self.get_time_ns_str()
                    self.log.error(f"{time_str} [DESC_ERROR] AXI conflict error: 0x{conflict_err:X}")

            if hasattr(self.dut, 'cfg_sts_desc_axi_error_count'):
                err_count = int(self.dut.cfg_sts_desc_axi_error_count.value)
                if err_count != 0:
                    time_str = self.get_time_ns_str()
                    self.log.error(f"{time_str} [DESC_ERROR] AXI error count: {err_count}")

    # =========================================================================
    # Descriptor Management
    # =========================================================================

    def write_descriptor(self, addr, src_addr, dst_addr, length,
                        next_ptr=0, priority=0, last=False, channel_id=0, interrupt=False):
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
            interrupt: Generate interrupt on completion
        """
        # Build descriptor packet using builder
        packet = self.desc_builder.build_descriptor_packet(
            src_addr=src_addr,
            dst_addr=dst_addr,
            length=length,
            next_ptr=next_ptr,
            valid=True,
            last=last,
            gen_irq=interrupt,
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

    def verify_descriptor_chain(self, descriptors):
        """
        Verify data transfers for a chain of descriptors with descriptor-aware error reporting.

        Similar to analysis script grouping, but done in TB with live descriptor info.

        Args:
            descriptors: List of descriptor dicts, each containing:
                - src_addr: Source address
                - dst_addr: Destination address
                - length: Transfer length in beats
                - (optional) desc_num: Descriptor number for logging

        Returns:
            dict: Verification results with per-descriptor breakdown
                {
                    'total_descriptors': int,
                    'passed_descriptors': int,
                    'failed_descriptors': int,
                    'total_beats': int,
                    'total_mismatches': int,
                    'descriptor_results': [
                        {
                            'desc_num': int,
                            'beats': int,
                            'mismatches': int,
                            'passed': bool,
                            'error_details': [(beat, src, dst), ...]
                        }
                    ]
                }
        """
        results = {
            'total_descriptors': len(descriptors),
            'passed_descriptors': 0,
            'failed_descriptors': 0,
            'total_beats': 0,
            'total_mismatches': 0,
            'descriptor_results': []
        }

        self.log.info("="*80)
        self.log.info("DESCRIPTOR CHAIN VERIFICATION")
        self.log.info("="*80)

        for desc_idx, desc in enumerate(descriptors):
            desc_num = desc.get('desc_num', desc_idx + 1)
            src_addr = desc['src_addr']
            dst_addr = desc['dst_addr']
            length = desc['length']

            self.log.info(f"\nDescriptor {desc_num}:")
            self.log.info(f"  src=0x{src_addr:08x}, dst=0x{dst_addr:08x}, length={length} beats")

            # Verify this descriptor's data
            errors = []
            for beat in range(length):
                beat_src_addr = src_addr + (beat * self.data_bytes)
                beat_dst_addr = dst_addr + (beat * self.data_bytes)

                src_offset = beat_src_addr - self.src_mem_base
                dst_offset = beat_dst_addr - self.dst_mem_base

                src_data_bytes = self.src_memory_model.read(src_offset, self.data_bytes)
                dst_data_bytes = self.dst_memory_model.read(dst_offset, self.data_bytes)

                src_data = int.from_bytes(bytes(src_data_bytes), byteorder='little')
                dst_data = int.from_bytes(bytes(dst_data_bytes), byteorder='little')

                if src_data != dst_data:
                    errors.append((beat, src_data, dst_data))

            # Record results for this descriptor
            desc_result = {
                'desc_num': desc_num,
                'beats': length,
                'mismatches': len(errors),
                'passed': (len(errors) == 0),
                'error_details': errors
            }
            results['descriptor_results'].append(desc_result)
            results['total_beats'] += length
            results['total_mismatches'] += len(errors)

            # Log descriptor result
            if len(errors) == 0:
                self.log.info(f"  ✓ PASS: All {length} beats match")
                results['passed_descriptors'] += 1
            else:
                self.log.error(f"  ✗ FAIL: {len(errors)} mismatches out of {length} beats")
                results['failed_descriptors'] += 1

                # Show first 5 errors
                for beat, src, dst in errors[:5]:
                    self.log.error(f"    Beat {beat}: src=0x{src:0{self.data_bytes*2}x}, "
                                 f"dst=0x{dst:0{self.data_bytes*2}x}")
                if len(errors) > 5:
                    self.log.error(f"    ... and {len(errors)-5} more mismatches")

        # Print summary
        self.log.info("\n" + "="*80)
        self.log.info("VERIFICATION SUMMARY")
        self.log.info("="*80)
        self.log.info(f"Total descriptors: {results['total_descriptors']}")
        self.log.info(f"  Passed: {results['passed_descriptors']}")
        self.log.info(f"  Failed: {results['failed_descriptors']}")
        self.log.info(f"Total beats verified: {results['total_beats']}")
        self.log.info(f"Total mismatches: {results['total_mismatches']}")

        if results['failed_descriptors'] == 0:
            self.log.info("\n✓ ALL DESCRIPTORS PASSED - Data integrity verified!")
        else:
            self.log.error(f"\n✗ {results['failed_descriptors']} DESCRIPTOR(S) FAILED")

        self.log.info("="*80 + "\n")

        return results

    # =========================================================================
    # Channel Control
    # =========================================================================

    async def kick_off_channel(self, channel, descriptor_addr):
        """
        Kick off a DMA transfer on specified channel.

        For stream_core: Uses per-channel control signals (apb_addr, apb_valid, apb_ready)
        For stream_top: Uses APB4 protocol writes to CHx_CTRL_LOW/HIGH registers

        Args:
            channel: Channel number (0 to num_channels-1)
            descriptor_addr: Address of first descriptor in chain
        """
        if channel >= self.num_channels:
            self.log.error(f"Invalid channel {channel}, max is {self.num_channels-1}")
            return

        # DEBUG: Log what we're about to do
        self.log.info(f"kick_off_channel: channel={channel}, descriptor_addr=0x{descriptor_addr:016X}")
        self.log.info(f"  APB master initialized: {self.apb_master is not None}")

        # Detect mode: APB (stream_top) or direct (stream_core)
        if self.apb_master is not None:
            # APB mode (stream_top) - write descriptor address to CHx_CTRL registers
            # 64-bit descriptor address split into two 32-bit registers
            ctrl_low_addr = StreamRegisterMap.get_ch_ctrl_low_addr(channel)
            ctrl_high_addr = StreamRegisterMap.get_ch_ctrl_high_addr(channel)

            desc_low = descriptor_addr & 0xFFFFFFFF
            desc_high = (descriptor_addr >> 32) & 0xFFFFFFFF

            self.log.info(f"  Writing to APB addr 0x{ctrl_low_addr:03X} = 0x{desc_low:08X} (descriptor LOW)")
            self.log.info(f"  Writing to APB addr 0x{ctrl_high_addr:03X} = 0x{desc_high:08X} (descriptor HIGH)")

            # Write lower 32 bits
            await self.write_apb_register(ctrl_low_addr, desc_low)

            # Write upper 32 bits (triggers kick-off)
            await self.write_apb_register(ctrl_high_addr, desc_high)

            self.log.info(f"Kicked off channel {channel} via APB with descriptor @ 0x{descriptor_addr:016X}")

        else:
            # Direct mode (stream_core) - drive per-channel control signals
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
        Wait for channel to return to idle state and all AXI transactions to complete.

        For stream_core: Monitors scheduler_idle, axi_rd_all_complete, axi_wr_all_complete signals
        For stream_top: Reads CHANNEL_IDLE APB register

        Args:
            channel: Channel number
            timeout_us: Timeout in microseconds

        Returns:
            bool: True if channel idle and all txns complete, False on timeout
        """
        timeout_ns = timeout_us * 1000
        start_time = cocotb.utils.get_sim_time('ns')

        self.log.info(f"Waiting for channel {channel} to become idle (timeout={timeout_us}us){self.get_time_ns_str()}")

        # Detect mode: APB (stream_top) or direct (stream_core)
        if self.apb_master is not None:
            # APB mode (stream_top) - read CHANNEL_IDLE register
            idle_seen = False
            cycle_count = 0

            while True:
                await RisingEdge(self.clk)

                current_time = cocotb.utils.get_sim_time('ns')
                elapsed_ns = current_time - start_time
                cycle_count += 1

                # Read CHANNEL_IDLE register (bit per channel)
                channel_idle = await self.read_apb_register(StreamRegisterMap.CHANNEL_IDLE)
                channel_idle_ch = (channel_idle >> channel) & 0x1

                # Log first time idle is seen
                if channel_idle_ch and not idle_seen:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.info(f"  Channel {channel} idle after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    idle_seen = True

                # Channel is idle when bit is set
                if channel_idle_ch:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.info(f"✓ Channel {channel} FULLY COMPLETE after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    self.transfer_end_time[channel] = current_time
                    return True

                # Timeout check
                if elapsed_ns > timeout_ns:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.error(f"✗ Channel {channel} timeout after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    self.log.error(f"  channel_idle[{channel}]={channel_idle_ch}")
                    # Read individual idle registers for debugging
                    desc_eng_idle = await self.read_apb_register(StreamRegisterMap.DESC_ENGINE_IDLE)
                    sched_idle = await self.read_apb_register(StreamRegisterMap.SCHEDULER_IDLE)
                    self.log.error(f"  DESC_ENGINE_IDLE=0x{desc_eng_idle:02X} (ch{channel}={(desc_eng_idle >> channel) & 1})")
                    self.log.error(f"  SCHEDULER_IDLE=0x{sched_idle:02X} (ch{channel}={(sched_idle >> channel) & 1})")

                    # Also probe internal RTL signals directly for comparison
                    try:
                        await ReadOnly()
                        # Try to access stream_core's internal signals (inside generate block)
                        # stream_top_ch8.g_stream_core.u_stream_core (when USE_AXI_MONITORS=0)
                        rtl_sched_idle = int(self.dut.g_stream_core.u_stream_core.scheduler_idle.value)
                        rtl_desc_idle = int(self.dut.g_stream_core.u_stream_core.descriptor_engine_idle.value)
                        self.log.error(f"  RTL scheduler_idle=0x{rtl_sched_idle:02X} (ch{channel}={(rtl_sched_idle >> channel) & 1})")
                        self.log.error(f"  RTL descriptor_engine_idle=0x{rtl_desc_idle:02X} (ch{channel}={(rtl_desc_idle >> channel) & 1})")
                        # Also probe signals directly in stream_top_ch8
                        top_sched_idle = int(self.dut.scheduler_idle.value)
                        top_desc_idle = int(self.dut.descriptor_engine_idle.value)
                        self.log.error(f"  TOP scheduler_idle=0x{top_sched_idle:02X}")
                        self.log.error(f"  TOP descriptor_engine_idle=0x{top_desc_idle:02X}")

                        # Probe hwif_in struct values inside stream_regs to see if struct connection works
                        try:
                            # Access the hwif_in port of u_stream_regs
                            hwif_in_val = self.dut.hwif_in.value
                            self.log.error(f"  hwif_in (raw): {hwif_in_val}")
                            # Probe intermediate signals that feed the struct
                            try:
                                hwif_sched_idle = int(self.dut.hwif_scheduler_idle.value)
                                hwif_desc_idle = int(self.dut.hwif_desc_engine_idle.value)
                                hwif_ch_idle = int(self.dut.hwif_channel_idle.value)
                                self.log.error(f"  hwif_scheduler_idle=0x{hwif_sched_idle:02X}")
                                self.log.error(f"  hwif_desc_engine_idle=0x{hwif_desc_idle:02X}")
                                self.log.error(f"  hwif_channel_idle=0x{hwif_ch_idle:02X}")
                            except Exception as e2:
                                self.log.error(f"  Cannot access hwif_ intermediate signals: {e2}")
                            # Probe debug outputs that show hwif_in struct field values
                            try:
                                debug_sched = int(self.dut.debug_hwif_scheduler_idle.value)
                                debug_desc = int(self.dut.debug_hwif_desc_engine_idle.value)
                                debug_ch = int(self.dut.debug_hwif_channel_idle.value)
                                self.log.error(f"  debug_hwif_scheduler_idle=0x{debug_sched:02X}")
                                self.log.error(f"  debug_hwif_desc_engine_idle=0x{debug_desc:02X}")
                                self.log.error(f"  debug_hwif_channel_idle=0x{debug_ch:02X}")
                            except Exception as e2b:
                                self.log.error(f"  Cannot access debug_hwif_ signals: {e2b}")
                            # Probe regblk interface debug signals
                            try:
                                debug_req = int(self.dut.debug_regblk_req.value)
                                debug_req_is_wr = int(self.dut.debug_regblk_req_is_wr.value)
                                debug_addr = int(self.dut.debug_regblk_addr.value)
                                debug_rd_data = int(self.dut.debug_regblk_rd_data.value)
                                debug_rd_ack = int(self.dut.debug_regblk_rd_ack.value)
                                self.log.error(f"  debug_regblk_req={debug_req}")
                                self.log.error(f"  debug_regblk_req_is_wr={debug_req_is_wr}")
                                self.log.error(f"  debug_regblk_addr=0x{debug_addr:03X}")
                                self.log.error(f"  debug_regblk_rd_data=0x{debug_rd_data:08X}")
                                self.log.error(f"  debug_regblk_rd_ack={debug_rd_ack}")
                            except Exception as e2c:
                                self.log.error(f"  Cannot access debug_regblk_ signals: {e2c}")
                            # Try individual fields if Verilator exposes them
                            try:
                                hwif_sched = self.dut.u_stream_regs.hwif_in.value
                                self.log.error(f"  u_stream_regs.hwif_in (raw): {hwif_sched}")
                            except Exception as e3:
                                self.log.error(f"  Cannot access u_stream_regs.hwif_in: {e3}")
                        except Exception as e4:
                            self.log.error(f"  Cannot access hwif_in: {e4}")
                    except Exception as e:
                        self.log.error(f"  Could not probe internal RTL signals: {e}")
                    return False

                # Poll every 10us to reduce APB traffic (1000 cycles @ 10ns = 10us)
                for _ in range(999):
                    await RisingEdge(self.clk)

        else:
            # Direct mode (stream_core) - read internal signals
            sched_idle_seen = False
            rd_complete_seen = False
            wr_complete_seen = False

            debug_log_interval = 1000  # Log every 1000 cycles when all not complete
            cycle_count = 0

            while True:
                await RisingEdge(self.clk)
                await ReadOnly()

                current_time = cocotb.utils.get_sim_time('ns')
                elapsed_ns = current_time - start_time
                cycle_count += 1

                # Check all completion conditions
                scheduler_idle = int(self.dut.scheduler_idle.value)
                rd_complete = int(self.dut.axi_rd_all_complete.value)
                wr_complete = int(self.dut.axi_wr_all_complete.value)

                sched_idle_ch = (scheduler_idle >> channel) & 0x1
                rd_complete_ch = (rd_complete >> channel) & 0x1
                wr_complete_ch = (wr_complete >> channel) & 0x1

                # Log first time each condition is met
                if sched_idle_ch and not sched_idle_seen:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.info(f"  Channel {channel} scheduler idle after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    sched_idle_seen = True

                if rd_complete_ch and not rd_complete_seen:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.info(f"  Channel {channel} AXI read complete after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    rd_complete_seen = True

                if wr_complete_ch and not wr_complete_seen:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.info(f"  Channel {channel} AXI write complete after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    wr_complete_seen = True

                # Periodic debug logging when scheduler idle but engines not complete
                if sched_idle_ch and (not rd_complete_ch or not wr_complete_ch) and (cycle_count % debug_log_interval == 0):
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.warning(f"Channel {channel} waiting for AXI complete after {elapsed_us:.1f}us: "
                                   f"sched_idle={sched_idle_ch}, rd_complete={rd_complete_ch}, wr_complete={wr_complete_ch}")

                # All three conditions must be true
                if sched_idle_ch and rd_complete_ch and wr_complete_ch:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.info(f"✓ Channel {channel} FULLY COMPLETE after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    self.transfer_end_time[channel] = current_time
                    return True

                # Timeout check
                if elapsed_ns > timeout_ns:
                    elapsed_us = elapsed_ns / 1000.0
                    self.log.error(f"✗ Channel {channel} timeout after {elapsed_us:.1f}us{self.get_time_ns_str()}")
                    self.log.error(f"  scheduler_idle[{channel}]={sched_idle_ch}, "
                                 f"rd_complete[{channel}]={rd_complete_ch}, "
                                 f"wr_complete[{channel}]={wr_complete_ch}")
                    return False

    # =========================================================================
    # APB Configuration Interface (stream_top only)
    # =========================================================================

    async def init_apb_master(self):
        """
        Initialize APB master for stream_top configuration interface.

        Only call this for stream_top testing. stream_core uses direct signals.
        """
        # Import here to avoid circular dependencies
        from CocoTBFramework.components.apb.apb_components import APBMaster
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        from CocoTBFramework.tbclasses.amba.amba_random_configs import APB_MASTER_RANDOMIZER_CONFIGS

        # Check if DUT has APB interface
        if not hasattr(self.dut, 's_apb_paddr'):
            self.log.warning("DUT does not have APB interface - APB master not initialized")
            self.apb_master = None
            return

        # Create APB Master
        # IMPORTANT: When CDC_ENABLE=0, the RTL connects apb_slave to aclk internally,
        # NOT the external pclk port. So the APBMaster must use the same clock.
        # For non-CDC testing, use self.clk (which is aclk).
        # For CDC testing, use self.dut.pclk (the separate APB clock domain).
        # Since we're primarily testing with CDC_ENABLE=0, use aclk (self.clk).
        self.apb_master = APBMaster(
            entity=self.dut,
            title='STREAM APB Master',
            prefix='s_apb',
            clock=self.clk,     # Use aclk - must match RTL's apb_slave clock when CDC_ENABLE=0
            bus_width=32,       # 32-bit data
            addr_width=12,      # 12-bit addressing (4KB space)
            randomizer=FlexRandomizer(APB_MASTER_RANDOMIZER_CONFIGS['fixed']),
            log=self.log
        )

        # Initialize the APB master
        await self.apb_master.reset_bus()

        self.log.info("APB Master initialized for stream_top configuration")

    async def write_apb_register(self, addr, data):
        """
        Write to APB configuration register using standard APB protocol.

        Args:
            addr: Register address (12-bit)
            data: 32-bit data to write

        Returns:
            APBPacket: Response packet
        """
        if self.apb_master is None:
            raise RuntimeError("APB master not initialized. Call init_apb_master() first.")

        # Create APB write packet with proper field configuration (matches HPET pattern)
        from CocoTBFramework.components.apb.apb_packet import APBPacket

        packet = APBPacket(
            pwrite=1,
            paddr=addr,
            pwdata=data,
            pstrb=0xF,      # All 4 bytes enabled for 32-bit
            pprot=0,
            data_width=32,  # Fixed 32-bit data
            addr_width=12,  # Fixed 12-bit addressing
            strb_width=4    # Fixed 4-byte strobe
        )

        # Send transaction and wait for completion
        # IMPORTANT: Use busy_send() to wait for transaction to complete!
        # send() is non-blocking and just queues the transaction.
        await self.apb_master.busy_send(packet)

        # Wait one more clock for APBMaster to finish bus cleanup
        # This avoids race conditions with background monitors using ReadOnly()
        await RisingEdge(self.clk)

        reg_name = StreamRegisterMap.get_register_name(addr)
        self.log.info(f"APB WRITE: {reg_name} (0x{addr:03X}) = 0x{data:08X}")

    async def read_apb_register(self, addr, debug_probe=False):
        """
        Read from APB configuration register using standard APB protocol.

        Args:
            addr: Register address (12-bit)
            debug_probe: If True, probe debug signals during read

        Returns:
            int: 32-bit data read
        """
        if self.apb_master is None:
            raise RuntimeError("APB master not initialized. Call init_apb_master() first.")

        # Create APB read packet with proper field configuration (matches HPET pattern)
        from CocoTBFramework.components.apb.apb_packet import APBPacket

        packet = APBPacket(
            pwrite=0,
            paddr=addr,
            pwdata=0,       # Don't care for reads
            pstrb=0xF,      # All 4 bytes enabled for 32-bit
            pprot=0,
            data_width=32,  # Fixed 32-bit data
            addr_width=12,  # Fixed 12-bit addressing
            strb_width=4    # Fixed 4-byte strobe
        )

        # Send transaction and wait for completion
        # IMPORTANT: Use busy_send() to wait for transaction to complete!
        # send() is non-blocking and just queues the transaction.
        await self.apb_master.busy_send(packet)

        # Wait one more clock for APBMaster to finish bus cleanup
        # This avoids race conditions with background monitors using ReadOnly()
        await RisingEdge(self.clk)

        # Extract data from packet after transaction completes
        data = packet.fields.get('prdata', 0)
        reg_name = StreamRegisterMap.get_register_name(addr)
        self.log.info(f"APB READ:  {reg_name} (0x{addr:03X}) = 0x{data:08X}")

        # Optional debug probing
        if debug_probe:
            try:
                await ReadOnly()
                # Probe regblk signals (to stream_regs)
                debug_req = int(self.dut.debug_regblk_req.value)
                debug_addr = int(self.dut.debug_regblk_addr.value)
                debug_rd_data = int(self.dut.debug_regblk_rd_data.value)
                debug_rd_ack = int(self.dut.debug_regblk_rd_ack.value)
                self.log.info(f"  [DEBUG] regblk_req={debug_req}, addr=0x{debug_addr:03X}, "
                             f"rd_data=0x{debug_rd_data:08X}, rd_ack={debug_rd_ack}")
                # Probe peakrdl cmd/rsp signals
                peakrdl_cmd_valid = int(self.dut.debug_peakrdl_cmd_valid.value)
                peakrdl_cmd_paddr = int(self.dut.debug_peakrdl_cmd_paddr.value)
                peakrdl_rsp_valid = int(self.dut.debug_peakrdl_rsp_valid.value)
                peakrdl_rsp_prdata = int(self.dut.debug_peakrdl_rsp_prdata.value)
                self.log.info(f"  [DEBUG] peakrdl cmd_valid={peakrdl_cmd_valid}, cmd_paddr=0x{peakrdl_cmd_paddr:03X}, "
                             f"rsp_valid={peakrdl_rsp_valid}, rsp_prdata=0x{peakrdl_rsp_prdata:08X}")
                # Probe registered debug capture (holds values from last read)
                last_addr = int(self.dut.debug_last_cpuif_addr.value)
                last_rd_data = int(self.dut.debug_last_cpuif_rd_data.value)
                last_rd_ack = int(self.dut.debug_last_cpuif_rd_ack.value)
                self.log.info(f"  [DEBUG CAPTURE] last_addr=0x{last_addr:03X}, "
                             f"last_rd_data=0x{last_rd_data:08X}, last_rd_ack={last_rd_ack}")
                # Probe APB cmd/rsp path (from apb_slave_cdc output) - current values
                apb_cmd_valid = int(self.dut.debug_apb_cmd_valid.value)
                apb_cmd_ready = int(self.dut.debug_apb_cmd_ready.value)
                apb_cmd_pwrite = int(self.dut.debug_apb_cmd_pwrite.value)
                apb_cmd_paddr = int(self.dut.debug_apb_cmd_paddr.value)
                apb_rsp_valid = int(self.dut.debug_apb_rsp_valid.value)
                apb_rsp_ready = int(self.dut.debug_apb_rsp_ready.value)
                apb_rsp_prdata = int(self.dut.debug_apb_rsp_prdata.value)
                self.log.info(f"  [APB CMD NOW] valid={apb_cmd_valid}, ready={apb_cmd_ready}, "
                             f"pwrite={apb_cmd_pwrite}, paddr=0x{apb_cmd_paddr:03X}")
                self.log.info(f"  [APB RSP NOW] valid={apb_rsp_valid}, ready={apb_rsp_ready}, "
                             f"prdata=0x{apb_rsp_prdata:08X}")
                # Registered captures (hold values after transaction)
                rd_cmd_seen = int(self.dut.debug_apb_rd_cmd_seen.value)
                rd_cmd_addr = int(self.dut.debug_apb_rd_cmd_addr.value)
                rsp_captured = int(self.dut.debug_apb_rsp_prdata_captured.value)
                self.log.info(f"  [APB CAPTURED] rd_cmd_seen={rd_cmd_seen}, rd_cmd_addr=0x{rd_cmd_addr:03X}, "
                             f"rsp_prdata=0x{rsp_captured:08X}")
                # Sticky counters - total reads at each pipeline stage
                apb_rd_count = int(self.dut.debug_apb_rd_count.value)
                peakrdl_rd_count = int(self.dut.debug_peakrdl_rd_count.value)
                regblk_rd_count = int(self.dut.debug_regblk_rd_count.value)
                self.log.info(f"  [STICKY COUNTERS] apb_rd={apb_rd_count}, peakrdl_rd={peakrdl_rd_count}, "
                             f"regblk_rd={regblk_rd_count}")
            except Exception as e:
                self.log.warning(f"  [DEBUG] Cannot probe debug signals: {e}")

        return data

    async def enable_global(self):
        """Enable STREAM engine globally via GLOBAL_CTRL register."""
        await self.write_apb_register(StreamRegisterMap.GLOBAL_CTRL, 0x1)
        self.log.info("STREAM engine globally enabled")

    async def disable_global(self):
        """Disable STREAM engine globally via GLOBAL_CTRL register."""
        await self.write_apb_register(StreamRegisterMap.GLOBAL_CTRL, 0x0)
        self.log.info("STREAM engine globally disabled")

    async def read_global_status(self):
        """
        Read global status register.

        Returns:
            int: Global status value
        """
        return await self.read_apb_register(StreamRegisterMap.GLOBAL_STATUS)

    async def read_version(self):
        """
        Read version register.

        Returns:
            int: Version register value
        """
        return await self.read_apb_register(StreamRegisterMap.VERSION)

    async def enable_channel_mask(self, channel_mask):
        """
        Enable channels via CHANNEL_ENABLE register.

        Args:
            channel_mask: 8-bit mask (bit N = channel N enable)
        """
        await self.write_apb_register(StreamRegisterMap.CHANNEL_ENABLE, channel_mask)
        self.log.info(f"Enabled channels: 0b{channel_mask:08b}")

    async def reset_channels(self, channel_mask):
        """
        Reset channels via CHANNEL_RESET register.

        Args:
            channel_mask: 8-bit mask (bit N = reset channel N)
        """
        await self.write_apb_register(StreamRegisterMap.CHANNEL_RESET, channel_mask)
        self.log.info(f"Reset channels: 0b{channel_mask:08b}")

    async def configure_descriptor_address_range(self, base_addr=None, limit_addr=None):
        """
        Configure descriptor engine address range for descriptor 0.

        Sets the legal address range that the descriptor engine will accept
        for descriptor addresses. Addresses outside this range will be rejected.

        NOTE: Registers are 32-bit only - can only configure lower 32 bits of address.
              Upper 32 bits are assumed to be 0 (addresses must be in lower 4GB).

        Args:
            base_addr: Base address of descriptor memory (default: self.desc_mem_base)
            limit_addr: Limit address of descriptor memory (default: base + size - 1)
        """
        # Use default descriptor memory range if not specified
        if base_addr is None:
            base_addr = self.desc_mem_base
        if limit_addr is None:
            limit_addr = self.desc_mem_base + self.desc_mem_size - 1

        # Extract lower 32 bits (registers are 32-bit only)
        base_low = base_addr & 0xFFFFFFFF
        limit_low = limit_addr & 0xFFFFFFFF

        # Warn if upper bits are non-zero
        if (base_addr >> 32) != 0:
            self.log.warning(f"Base address has non-zero upper 32 bits: 0x{base_addr:016X}")
            self.log.warning("  Descriptor engine only supports 32-bit addresses (lower 4GB)")
        if (limit_addr >> 32) != 0:
            self.log.warning(f"Limit address has non-zero upper 32 bits: 0x{limit_addr:016X}")
            self.log.warning("  Descriptor engine only supports 32-bit addresses (lower 4GB)")

        # Write base and limit address registers (32-bit only)
        await self.write_apb_register(StreamRegisterMap.DESCENG_ADDR0_BASE, base_low)
        await self.write_apb_register(StreamRegisterMap.DESCENG_ADDR0_LIMIT, limit_low)

        self.log.info(f"Configured descriptor address range (lower 32 bits):")
        self.log.info(f"  BASE:  0x{base_low:08X}")
        self.log.info(f"  LIMIT: 0x{limit_low:08X}")

    async def configure_transfer_beats(self, rd_xfer_beats=None, wr_xfer_beats=None):
        """
        Configure AXI read/write transfer burst sizes.

        This register MUST be configured via APB for stream_top (unlike stream_core
        which uses direct signal ports). Without this configuration, the AXI engines
        will not know what burst size to use, causing descriptor transfers to stall.

        Args:
            rd_xfer_beats: AXI read transfer beats (ARLEN value, 0-255 = 1-256 beats)
                          Default: use value from setup_clocks_and_reset()
            wr_xfer_beats: AXI write transfer beats (AWLEN value, 0-255 = 1-256 beats)
                          Default: use value from setup_clocks_and_reset()
        """
        # Use saved values from setup_clocks_and_reset if not specified
        if rd_xfer_beats is None:
            rd_xfer_beats = getattr(self, 'rd_xfer_beats', 16)
        if wr_xfer_beats is None:
            wr_xfer_beats = getattr(self, 'wr_xfer_beats', 16)

        # Build register value: WR_XFER_BEATS[15:8], RD_XFER_BEATS[7:0]
        reg_value = ((wr_xfer_beats & 0xFF) << 8) | (rd_xfer_beats & 0xFF)

        # Write AXI_XFER_CONFIG register
        await self.write_apb_register(StreamRegisterMap.AXI_XFER_CONFIG, reg_value)

        self.log.info(f"Configured AXI transfer beats:")
        self.log.info(f"  RD_XFER_BEATS: {rd_xfer_beats} beats")
        self.log.info(f"  WR_XFER_BEATS: {wr_xfer_beats} beats")
        self.log.info(f"  Register value: 0x{reg_value:08X}")

    async def read_channel_idle_status(self):
        """
        Read channel idle status register.

        Returns:
            int: 8-bit channel idle status (bit N = channel N idle)
        """
        return await self.read_apb_register(StreamRegisterMap.CHANNEL_IDLE)

    async def read_channel_state(self, channel):
        """
        Read per-channel state register.

        Args:
            channel: Channel number (0-7)

        Returns:
            int: Channel state value
        """
        addr = StreamRegisterMap.get_ch_state_addr(channel)
        return await self.read_apb_register(addr)

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
            # Replicate byte value across all bytes (not arithmetic multiply!)
            data = int.from_bytes(bytes([byte_val] * self.data_bytes), byteorder='little')
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
