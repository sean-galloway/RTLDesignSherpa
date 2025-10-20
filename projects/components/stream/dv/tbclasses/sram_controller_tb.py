"""
SRAM Controller Testbench

Reusable testbench class for validating STREAM sram_controller.sv module.

Key Features:
- Multi-channel SRAM segmentation testing
- Pre-allocation mechanism verification
- Dual data path testing (write from AXI RD, read to AXI WR)
- Flow control and backpressure handling
- Pointer management and wrap-around verification

Design Pattern:
- Testbench: Infrastructure and stimulus (this file)
- Test Runner: Test intelligence and parameters

Author: RTL Design Sherpa
Created: 2025-10-19
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random
from collections import deque
from enum import Enum

# Framework imports
import os
import sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class TestScenario(Enum):
    """Test scenario definitions"""
    BASIC_WRITE = "basic_write"              # Basic write to single channel
    BASIC_READ = "basic_read"                # Basic read from single channel
    MULTI_CHANNEL = "multi_channel"          # Multiple channels concurrent
    PRE_ALLOCATION = "pre_allocation"        # Pre-allocation mechanism
    WRAP_AROUND = "wrap_around"              # Pointer wrap-around
    BACKPRESSURE = "backpressure"            # Flow control testing


class SRAMControllerTB(TBBase):
    """
    Testbench class for STREAM SRAM Controller

    Provides:
    - Write path simulation (AXI read data → SRAM)
    - Read path simulation (SRAM → AXI write data)
    - Pre-allocation management
    - Multi-channel verification
    - SRAM model for verification
    """

    def __init__(self, dut, **kwargs):
        """Initialize testbench"""
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # Get parameters
        self.num_channels = int(dut.NUM_CHANNELS.value)
        self.sram_depth = int(dut.SRAM_DEPTH.value)
        self.data_width = int(dut.DATA_WIDTH.value)
        self.id_width = int(dut.ID_WIDTH.value)
        self.segment_size = int(dut.SEGMENT_SIZE.value)

        # SRAM model (verification only)
        self.sram_model = {}  # addr -> data dictionary

        # Channel tracking
        self.channel_wr_count = [0] * self.num_channels  # Writes per channel
        self.channel_rd_count = [0] * self.num_channels  # Reads per channel

        # Pre-allocation tracking
        self.reserved_space = [0] * self.num_channels

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - start clocks and perform reset sequence

        MANDATORY METHOD - Required by TBBase pattern
        """
        # Start clock (10ns period = 100MHz)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all input signals BEFORE reset
        self.dut.axi_rd_data_valid.value = 0
        self.dut.axi_rd_data_id.value = 0
        self.dut.axi_rd_data.value = 0

        # Pre-allocation signals (packed arrays - set as single value)
        self.dut.rd_space_req.value = 0
        self.dut.rd_xfer_count.value = 0  # Initialize entire packed array to 0

        # Read request signals
        self.dut.axi_wr_sram_req.value = 0

        # SRAM read data (from physical SRAM)
        self.dut.sram_rd_data.value = 0
        self.dut.sram_rd_data_valid.value = 0

        # Perform reset
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)  # Hold reset
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)   # Stabilization

        # Start background SRAM model (responds to sram_rd_en/sram_wr_en)
        cocotb.start_soon(self.sram_physical_model())

    async def assert_reset(self):
        """
        Assert reset signal

        MANDATORY METHOD - Required by TBBase pattern
        """
        self.rst_n.value = 0

    async def deassert_reset(self):
        """
        Deassert reset signal

        MANDATORY METHOD - Required by TBBase pattern
        """
        self.rst_n.value = 1

    async def sram_physical_model(self):
        """
        Model physical SRAM behavior (1-cycle read latency)

        Runs continuously in background
        """
        pending_read = False
        pending_addr = 0

        while True:
            await RisingEdge(self.clk)

            # Handle write operations
            if int(self.dut.sram_wr_en.value) == 1:
                wr_addr = int(self.dut.sram_wr_addr.value)
                wr_data = int(self.dut.sram_wr_data.value)
                self.sram_model[wr_addr] = wr_data
                self.log.debug(f"SRAM write: addr=0x{wr_addr:X}, data=0x{wr_data:X}")

            # Handle read requests (1-cycle latency)
            if int(self.dut.sram_rd_en.value) == 1:
                pending_read = True
                pending_addr = int(self.dut.sram_rd_addr.value)

            # Provide read data from PREVIOUS cycle (1-cycle latency)
            if pending_read:
                if pending_addr in self.sram_model:
                    self.dut.sram_rd_data.value = self.sram_model[pending_addr]
                    self.dut.sram_rd_data_valid.value = 1
                    self.log.debug(f"SRAM read: addr=0x{pending_addr:X}, data=0x{self.sram_model[pending_addr]:X}")
                else:
                    # Uninitialized location - return zeros
                    self.dut.sram_rd_data.value = 0
                    self.dut.sram_rd_data_valid.value = 1
                    self.log.debug(f"SRAM read: addr=0x{pending_addr:X}, data=0x0 (uninitialized)")
                pending_read = False
            else:
                self.dut.sram_rd_data_valid.value = 0

    async def request_space_allocation(self, channel: int, xfer_count: int):
        """
        Request space pre-allocation for a channel

        Args:
            channel: Channel number
            xfer_count: Number of beats to reserve

        Returns:
            bool: True if space granted
        """
        # Set request signals
        req_mask = 1 << channel
        self.dut.rd_space_req.value = req_mask

        # Set xfer_count for the specific channel (packed array)
        # rd_xfer_count is [NUM_CHANNELS-1:0][7:0], so we need to construct the value
        xfer_count_value = xfer_count << (channel * 8)
        self.dut.rd_xfer_count.value = xfer_count_value

        await RisingEdge(self.clk)

        # Check if granted
        grant_mask = int(self.dut.rd_space_grant.value)
        granted = (grant_mask >> channel) & 0x1

        # Clear request
        self.dut.rd_space_req.value = 0
        self.dut.rd_xfer_count.value = 0

        if granted:
            self.reserved_space[channel] += xfer_count
            self.log.info(f"✓ Space allocated: channel={channel}, beats={xfer_count}")
            return True
        else:
            self.log.warning(f"✗ Space allocation denied: channel={channel}, beats={xfer_count}")
            return False

    async def write_axi_data(self, channel: int, data: int):
        """
        Write AXI read data to SRAM controller

        Args:
            channel: Channel number (encoded in ID)
            data: Data payload
        """
        # Drive AXI read data interface
        self.dut.axi_rd_data_valid.value = 1
        self.dut.axi_rd_data_id.value = channel  # ID = channel
        self.dut.axi_rd_data.value = data

        await RisingEdge(self.clk)

        # Wait for ready
        while int(self.dut.axi_rd_data_ready.value) != 1:
            await RisingEdge(self.clk)

        # Clear signals
        self.dut.axi_rd_data_valid.value = 0

        self.channel_wr_count[channel] += 1
        if self.reserved_space[channel] > 0:
            self.reserved_space[channel] -= 1

        self.log.debug(f"Write: channel={channel}, data=0x{data:X}")

    async def read_sram_data(self, channel: int):
        """
        Read data from SRAM controller (via AXI write interface)

        Args:
            channel: Channel number

        Returns:
            int: Read data (after 1-cycle latency)
        """
        # Drive read request
        req_mask = 1 << channel
        self.dut.axi_wr_sram_req.value = req_mask

        await RisingEdge(self.clk)

        # Clear request immediately after 1 cycle (prevent double reads)
        self.dut.axi_wr_sram_req.value = 0

        # Wait for ack (1-cycle SRAM latency)
        await RisingEdge(self.clk)

        # Check ack and capture data
        ack_mask = int(self.dut.axi_wr_sram_ack.value)
        if (ack_mask >> channel) & 0x1:
            # Extract data for this channel from packed array
            # axi_wr_sram_data is [NUM_CHANNELS-1:0][DATA_WIDTH-1:0]
            full_data = int(self.dut.axi_wr_sram_data.value)
            # Extract channel's data: bits [(channel+1)*DATA_WIDTH-1 : channel*DATA_WIDTH]
            data_mask = (1 << self.data_width) - 1
            rd_data = (full_data >> (channel * self.data_width)) & data_mask

            self.log.debug(f"Read: channel={channel}, data=0x{rd_data:X}")
            self.channel_rd_count[channel] += 1

            return rd_data
        else:
            self.log.error(f"✗ Read failed: channel={channel}, no ack")
            return None

    async def run_basic_write_test(self, channel: int = 0, num_beats: int = 16):
        """
        Test basic write path operation

        Args:
            channel: Channel to test
            num_beats: Number of beats to write

        Returns:
            bool: True if test passed
        """
        self.log.info(f"=== Basic Write Test: channel={channel}, beats={num_beats} ===")

        # Pre-allocate space
        success = await self.request_space_allocation(channel, num_beats)
        if not success:
            self.log.error("✗ Pre-allocation failed")
            return False

        # Write test data
        test_data = []
        for i in range(num_beats):
            data = (i << 32) | (channel << 16) | i
            test_data.append(data)
            await self.write_axi_data(channel, data)

        # Wait for background SRAM model to process all writes
        await self.wait_clocks(self.clk_name, 5)

        # Verify writes in SRAM model
        base_addr = channel * self.segment_size
        for i, expected_data in enumerate(test_data):
            addr = base_addr + i
            if addr in self.sram_model:
                actual_data = self.sram_model[addr]
                if actual_data != expected_data:
                    self.log.error(f"✗ Data mismatch: addr=0x{addr:X}, expected=0x{expected_data:X}, got=0x{actual_data:X}")
                    return False
            else:
                self.log.error(f"✗ Missing write: addr=0x{addr:X}")
                return False

        self.log.info(f"✓ Basic write test passed: {num_beats} beats written")
        return True

    async def run_basic_read_test(self, channel: int = 0, num_beats: int = 16):
        """
        Test basic read path operation

        Args:
            channel: Channel to test
            num_beats: Number of beats to read

        Returns:
            bool: True if test passed
        """
        self.log.info(f"=== Basic Read Test: channel={channel}, beats={num_beats} ===")

        # First write data (so we have something to read)
        await self.run_basic_write_test(channel, num_beats)

        # Wait a few cycles for data to settle
        await self.wait_clocks(self.clk_name, 5)

        # Read data back
        test_data = []
        for i in range(num_beats):
            expected_data = (i << 32) | (channel << 16) | i
            test_data.append(expected_data)

        errors = 0
        for i, expected_data in enumerate(test_data):
            rd_data = await self.read_sram_data(channel)
            if rd_data is None:
                errors += 1
            elif rd_data != expected_data:
                self.log.error(f"✗ Read mismatch: beat={i}, expected=0x{expected_data:X}, got=0x{rd_data:X}")
                errors += 1

        if errors == 0:
            self.log.info(f"✓ Basic read test passed: {num_beats} beats read correctly")
            return True
        else:
            self.log.error(f"✗ Basic read test failed: {errors}/{num_beats} mismatches")
            return False

    async def run_multi_channel_test(self, num_channels_to_test: int = 4, beats_per_channel: int = 8):
        """
        Test multiple channels writing/reading concurrently

        Args:
            num_channels_to_test: Number of channels to use
            beats_per_channel: Beats per channel

        Returns:
            bool: True if test passed
        """
        self.log.info(f"=== Multi-Channel Test: channels={num_channels_to_test}, beats={beats_per_channel} ===")

        # Pre-allocate space for all channels
        for ch in range(num_channels_to_test):
            success = await self.request_space_allocation(ch, beats_per_channel)
            if not success:
                self.log.error(f"✗ Pre-allocation failed for channel {ch}")
                return False

        # Write data to all channels (interleaved)
        test_data = {}  # channel -> [data]
        for ch in range(num_channels_to_test):
            test_data[ch] = []

        for beat in range(beats_per_channel):
            for ch in range(num_channels_to_test):
                data = (beat << 32) | (ch << 16) | beat
                test_data[ch].append(data)
                await self.write_axi_data(ch, data)

        # Wait for writes to complete
        await self.wait_clocks(self.clk_name, 10)

        # Read back from all channels
        errors = 0
        for ch in range(num_channels_to_test):
            for beat, expected_data in enumerate(test_data[ch]):
                rd_data = await self.read_sram_data(ch)
                if rd_data is None:
                    errors += 1
                elif rd_data != expected_data:
                    self.log.error(f"✗ Channel {ch} beat {beat}: expected=0x{expected_data:X}, got=0x{rd_data:X}")
                    errors += 1

        if errors == 0:
            self.log.info(f"✓ Multi-channel test passed: {num_channels_to_test} channels × {beats_per_channel} beats")
            return True
        else:
            self.log.error(f"✗ Multi-channel test failed: {errors} mismatches")
            return False

    def get_test_report(self):
        """
        Generate test report

        Returns:
            dict: Test statistics
        """
        total_writes = sum(self.channel_wr_count)
        total_reads = sum(self.channel_rd_count)

        return {
            'num_channels': self.num_channels,
            'sram_depth': self.sram_depth,
            'segment_size': self.segment_size,
            'total_writes': total_writes,
            'total_reads': total_reads,
            'writes_per_channel': self.channel_wr_count,
            'reads_per_channel': self.channel_rd_count,
            'sram_locations_used': len(self.sram_model),
        }
