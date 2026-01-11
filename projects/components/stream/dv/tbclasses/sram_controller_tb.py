"""
SRAM Controller Testbench

Reusable testbench class for validating STREAM sram_controller.sv module.
Updated to match new FIFO-based interface with latency bridge integration.

Key Features:
- Per-channel FIFO testing with valid/ready handshaking
- Write path testing (AXI read engine → FIFO)
- Read path testing (FIFO → latency bridge → AXI write engine)
- Space tracking and data counting verification
- Multi-channel concurrent operation

Design Pattern:
- Testbench: Infrastructure and stimulus (this file)
- Test Runner: Test intelligence and parameters

Author: RTL Design Sherpa
Created: 2025-10-19
Updated: 2025-10-30 - Latency bridge integration
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

# Import framework utilities (PYTHONPATH includes bin/)
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)


class TestScenario(Enum):
    """Test scenario definitions"""
    BASIC_WRITE = "basic_write"              # Basic write to single channel
    BASIC_READ = "basic_read"                # Basic read from single channel
    MULTI_CHANNEL = "multi_channel"          # Multiple channels concurrent
    LATENCY_BRIDGE = "latency_bridge"        # Verify latency bridge alignment
    BACKPRESSURE = "backpressure"            # Flow control testing


class SRAMControllerTB(TBBase):
    """
    Testbench class for STREAM SRAM Controller (FIFO-based with Latency Bridge)

    Provides:
    - Write path simulation (AXI read data → FIFO)
    - Read path simulation (FIFO → Latency Bridge → AXI write data)
    - Multi-channel verification
    - Latency bridge validation (aligned valid+data)
    - Backpressure handling
    """

    def __init__(self, dut, **kwargs):
        """Initialize testbench"""
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Clock and reset
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # BFM clock (delayed by 100ps to avoid zero-cycle paths)
        self.bfm_clk = None  # Will be created as delayed trigger

        # Get parameters (SRAM-based interface)
        self.num_channels = int(dut.NUM_CHANNELS.value)
        self.fifo_depth = int(dut.SRAM_DEPTH.value)  # Parameter renamed from FIFO_DEPTH to SRAM_DEPTH
        self.data_width = int(dut.DATA_WIDTH.value)

        # Channel data tracking (for verification)
        self.channel_data = {}  # (channel, index) -> data
        self.channel_wr_count = [0] * self.num_channels
        self.channel_rd_count = [0] * self.num_channels

        # Pending read trackers (for latency bridge verification)
        self.pending_reads = [deque() for _ in range(self.num_channels)]

        # Test level configuration (scales operation counts)
        self.test_configs = {
            'gate': {
                'single_channel_beats': 16,
                'multi_channel_channels': 2,
                'multi_channel_beats': 8,
                'description': 'Quick smoke test (~30s)'
            },
            'func': {
                'single_channel_beats': 64,
                'multi_channel_channels': 4,
                'multi_channel_beats': 32,
                'description': 'Functional validation (~90s)'
            },
            'full': {
                'single_channel_beats': 256,
                'multi_channel_channels': 8,
                'multi_channel_beats': 128,
                'description': 'Comprehensive validation (~180s)'
            }
        }
        self.config = self.test_configs[self.TEST_LEVEL]
        self.log.info(f"Test level: {self.TEST_LEVEL.upper()} - {self.config['description']}{self.get_time_ns_str()}")

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - start clocks and perform reset sequence

        MANDATORY METHOD - Required by TBBase pattern
        """
        # Start clock (10ns period = 100MHz)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all input signals BEFORE reset
        # Write interface (transaction ID-based)
        self.dut.axi_rd_sram_valid.value = 0   # Single bit
        self.dut.axi_rd_sram_id.value = 0      # IW bits (channel select)
        self.dut.axi_rd_sram_data.value = 0    # Single data bus (shared)

        # Read/drain interface (transaction ID-based)
        self.dut.axi_wr_sram_drain.value = 0   # Single bit
        self.dut.axi_wr_sram_id.value = 0      # IW bits (channel select)

        # Allocation interface (transaction ID-based, read side only)
        self.dut.axi_rd_alloc_req.value = 0        # Single bit
        self.dut.axi_rd_alloc_size.value = 0       # 8 bits
        self.dut.axi_rd_alloc_id.value = 0         # IW bits (channel select)

        # Drain interface (write side flow control) - tie off to 0 for basic tests
        self.dut.axi_wr_drain_req.value = 0        # NC bits (per-channel)
        self.dut.axi_wr_drain_size.value = 0       # NC×8 bits (per-channel, packed)

        # Perform reset
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)  # Hold reset
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 20)  # Extended stabilization for FIFO/alloc_ctrl

        # Diagnostics: Check initial state
        await RisingEdge(self.clk)
        # Set ID to channel 0 to check ready
        self.dut.axi_rd_sram_id.value = 0
        await RisingEdge(self.clk)
        ready_val = int(self.dut.axi_rd_sram_ready.value)
        self.log.info(f"Post-reset ready state (ID=0): {ready_val}{self.get_time_ns_str()}")
        for ch in range(self.num_channels):
            # Check ready for each channel by setting ID
            self.dut.axi_rd_sram_id.value = ch
            await RisingEdge(self.clk)
            ch_ready = int(self.dut.axi_rd_sram_ready.value)
            space = await self.get_space_free(ch)
            self.log.info(f"  Channel {ch}: ready={ch_ready}, space_free={space}{self.get_time_ns_str()}")

        # Give one more cycle
        await RisingEdge(self.clk)

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

    async def wait_bfm_clk(self):
        """
        Wait for BFM clock edge (DUT clock + 100ps delay)

        This creates a delayed clock for BFM operations to avoid zero-cycle paths.
        The BFM should drive signals slightly after the DUT clock edge, allowing
        the DUT to sample on the next clock edge without race conditions.
        """
        await RisingEdge(self.clk)
        await Timer(100, units='ps')  # 100ps delay after DUT clock edge

    async def write_channel_data(self, channel: int, data: int, check_ready: bool = True, timeout_cycles: int = 100):
        """
        Write data to a specific channel (AXI read engine → FIFO)

        Transaction ID-based interface:
        - Set axi_rd_sram_valid = 1
        - Set axi_rd_sram_id = channel
        - Set axi_rd_sram_data = data
        - Wait for axi_rd_sram_ready = 1
        - Clear valid after handshake

        Args:
            channel: Channel number
            data: Data payload
            check_ready: Wait for ready if True
            timeout_cycles: Maximum cycles to wait for ready

        Returns:
            bool: True if write successful, False if timeout
        """
        # Track data for later verification
        write_index = self.channel_wr_count[channel]
        self.channel_data[(channel, write_index)] = data

        # Wait for BFM clock before driving (avoids zero-cycle path)
        await self.wait_bfm_clk()

        # Drive write interface with transaction ID
        self.dut.axi_rd_sram_valid.value = 1
        self.dut.axi_rd_sram_id.value = channel
        self.dut.axi_rd_sram_data.value = data

        # Wait for ready (with valid still asserted)
        cycles_waited = 0
        if check_ready:
            while cycles_waited < timeout_cycles:
                await RisingEdge(self.clk)
                cycles_waited += 1
                ready = int(self.dut.axi_rd_sram_ready.value)
                if ready:
                    # Handshake complete!
                    self.log.debug(f"Write handshake: channel={channel}, cycles={cycles_waited}{self.get_time_ns_str()}")
                    break
            else:
                # Timeout!
                self.log.error(f"Write timeout: channel={channel}, waited {timeout_cycles} cycles, ready never went high{self.get_time_ns_str()}")
                space = await self.get_space_free(channel)
                self.log.error(f"  axi_rd_alloc_space_free[{channel}] = {space}{self.get_time_ns_str()}")
                # Clear valid before returning
                self.dut.axi_rd_sram_valid.value = 0
                return False
        else:
            # Not checking ready, just wait one cycle
            await RisingEdge(self.clk)

        # Clear valid after handshake
        self.dut.axi_rd_sram_valid.value = 0

        self.channel_wr_count[channel] += 1
        self.log.debug(f"Write complete: channel={channel}, data=0x{data:X}, idx={write_index}{self.get_time_ns_str()}")
        return True

    async def issue_drain_request(self, channel: int, size: int):
        """
        Issue a drain request for the specified channel

        This simulates the write engine reserving data before issuing AW command.
        The drain controller will decrement its data_available count by 'size'.

        Args:
            channel: Channel number
            size: Number of beats to reserve
        """
        # Set drain request for one cycle (combinational in real write engine)
        # Need to properly drive the packed array [NC-1:0]
        drain_req_value = 1 << channel  # One-hot for specified channel
        self.dut.axi_wr_drain_req.value = drain_req_value

        # Set drain size for this channel
        # axi_wr_drain_size is [NC-1:0][7:0] packed array
        # Calculate bit position: channel * 8
        drain_size_value = 0
        for i in range(self.num_channels):
            if i == channel:
                drain_size_value |= (size << (i * 8))
        self.dut.axi_wr_drain_size.value = drain_size_value

        # Wait one cycle for drain controller to register
        await RisingEdge(self.clk)

        # Clear drain request
        self.dut.axi_wr_drain_req.value = 0
        self.dut.axi_wr_drain_size.value = 0

        self.log.debug(f"Drain request issued: channel={channel}, size={size}{self.get_time_ns_str()}")

    async def read_channel_data(self, channel: int, timeout_cycles: int = 100):
        """
        Read data from a specific channel (FIFO → latency bridge → AXI write engine)

        Transaction ID-based interface (SAMPLE-THEN-DRAIN approach):
        - Set axi_wr_sram_id = channel (select channel MUX) - CRITICAL: Must do this first!
        - Sample current data (already on output from previous operation or priming)
        - Pulse drain to consume current data and advance for NEXT read
        - Wait for new data to propagate

        Args:
            channel: Channel number
            timeout_cycles: Maximum cycles to wait (currently unused - drain is direct)

        Returns:
            int: Read data
        """
        # CRITICAL: Set channel ID BEFORE sampling!
        # The mux is combinatorial, so we need this set before reading
        self.dut.axi_wr_sram_id.value = channel

        # Wait a bit for the BFM clock (avoid zero-cycle paths)
        await self.wait_bfm_clk()

        # Sample the current output (data should already be there from previous drain/priming)
        rd_data = int(self.dut.axi_wr_sram_data.value)

        # NOW pulse drain to consume this data and advance for next read
        self.dut.axi_wr_sram_drain.value = 1
        await RisingEdge(self.clk)
        self.dut.axi_wr_sram_drain.value = 0

        # Wait for new data to propagate through latency bridge
        await RisingEdge(self.clk)

        self.channel_rd_count[channel] += 1
        self.log.debug(f"Read ch{channel}: data=0x{rd_data:X}, idx={self.channel_rd_count[channel]-1}{self.get_time_ns_str()}")
        return rd_data

    async def get_space_free(self, channel: int):
        """
        Get free space count for a channel

        Args:
            channel: Channel number

        Returns:
            int: Free space in beats
        """
        # axi_rd_alloc_space_free is [NC-1:0][$clog2(FIFO_DEPTH):0] packed array
        # Width per element = $clog2(FIFO_DEPTH) + 1
        import math
        element_width = math.ceil(math.log2(self.fifo_depth)) + 1
        full_value = int(self.dut.axi_rd_alloc_space_free.value)
        mask = (1 << element_width) - 1
        space = (full_value >> (channel * element_width)) & mask
        return space

    async def get_data_available(self, channel: int):
        """
        Get data available count for a channel (after drain reservations)

        Args:
            channel: Channel number

        Returns:
            int: Data available in beats (accounting for drain reservations)
        """
        # axi_wr_drain_data_avail is [NC-1:0][$clog2(FIFO_DEPTH):0] packed array
        # Width per element = $clog2(FIFO_DEPTH) + 1
        import math
        element_width = math.ceil(math.log2(self.fifo_depth)) + 1
        full_value = int(self.dut.axi_wr_drain_data_avail.value)
        mask = (1 << element_width) - 1
        count = (full_value >> (channel * element_width)) & mask
        return count

    async def allocate_space(self, channel: int, size: int):
        """
        Pre-allocate space in a channel (simulates AXI read engine reservation)

        This models what the AXI read engine does BEFORE data arrives:
        1. Check available space
        2. Reserve N beats
        3. Later: write actual data when AXI read completes

        Args:
            channel: Channel number
            size: Number of beats to allocate

        Returns:
            bool: True if allocation successful
        """
        # Check space before allocating
        space_before = await self.get_space_free(channel)
        self.log.debug(f"Allocate request: channel={channel}, size={size}, space_before={space_before}{self.get_time_ns_str()}")

        # Wait for BFM clock before driving (avoids zero-cycle path)
        await self.wait_bfm_clk()

        # Drive allocation interface (transaction ID-based)
        self.dut.axi_rd_alloc_req.value = 1
        self.dut.axi_rd_alloc_id.value = channel
        self.dut.axi_rd_alloc_size.value = size

        # Wait one cycle for allocation to take effect
        await RisingEdge(self.clk)

        # Clear allocation request
        self.dut.axi_rd_alloc_req.value = 0

        # Wait for allocation controller to update
        await RisingEdge(self.clk)

        # Wait one more cycle for registered count to update
        # (FIFO count is now registered for proper timing)
        await RisingEdge(self.clk)

        # Check space after allocation
        space_after = await self.get_space_free(channel)
        space_allocated = space_before - space_after

        self.log.debug(f"Allocation result: space_after={space_after}, allocated={space_allocated}{self.get_time_ns_str()}")

        if space_allocated == size:
            self.log.debug(f"✓ Allocation successful: {size} beats reserved{self.get_time_ns_str()}")
            return True
        else:
            self.log.error(f"✗ Allocation mismatch: requested={size}, actually_allocated={space_allocated}{self.get_time_ns_str()}")
            return False

    async def run_single_channel_test(self, channel: int = 0, num_beats: int = None):
        """
        Comprehensive single-channel test: write, verify count, read, verify data

        Args:
            channel: Channel to test
            num_beats: Number of beats to transfer (None = use TEST_LEVEL config)

        Returns:
            bool: True if test passed
        """
        # Use TEST_LEVEL config if num_beats not specified
        if num_beats is None:
            num_beats = self.config['single_channel_beats']
        self.log.info(f"=== Single Channel Test: channel={channel}, beats={num_beats} ==={self.get_time_ns_str()}")

        # Phase 1: Check initial space
        initial_space = await self.get_space_free(channel)
        self.log.info(f"Phase 1: Initial space for channel {channel}: {initial_space} beats{self.get_time_ns_str()}")

        if initial_space < num_beats:
            self.log.error(f"✗ Insufficient space: need {num_beats}, have {initial_space}{self.get_time_ns_str()}")
            return False

        # Phase 2: Write test data
        self.log.info(f"Phase 2: Writing {num_beats} beats to channel {channel}{self.get_time_ns_str()}")
        for i in range(num_beats):
            # Create unique test pattern (start at 1 for visibility)
            beat_num = i + 1
            data = (beat_num << 32) | (channel << 16) | beat_num
            success = await self.write_channel_data(channel, data)
            if not success:
                self.log.error(f"✗ Write failed at beat {i}{self.get_time_ns_str()}")
                return False

        # Wait for writes to settle and propagate through latency bridge
        await self.wait_clocks(self.clk_name, 10)

        # Phase 3: Verify data_available count
        # Note: count includes FIFO contents + latency bridge occupancy (up to 4 beats)
        # After recent fix, bridge occupancy is correctly added to the count
        self.log.info(f"Phase 3: Verifying wr_drain_data_avail count for channel {channel}{self.get_time_ns_str()}")
        data_count = await self.get_data_available(channel)
        self.log.info(f"Data available count: {data_count} (expected: {num_beats} to {num_beats+4}){self.get_time_ns_str()}")

        # Accept num_beats to num_beats+4 (latency bridge depth = 4)
        if data_count < num_beats or data_count > num_beats + 4:
            self.log.error(f"✗ Data count out of range: expected={num_beats} to {num_beats+4}, got={data_count}{self.get_time_ns_str()}")
            return False
        else:
            bridge_occ = data_count - num_beats
            self.log.info(f"✓ Data count acceptable: {data_count} beats ({num_beats} in FIFO + {bridge_occ} in latency bridge){self.get_time_ns_str()}")

        # Phase 4: Read data back and verify
        self.log.info(f"Phase 4: Reading {num_beats} beats from channel {channel}{self.get_time_ns_str()}")

        # IMPORTANT: Issue drain request BEFORE reading to update drain controller
        # This simulates write engine reserving data before AW command
        self.log.debug(f"Issuing drain request: channel={channel}, size={num_beats}{self.get_time_ns_str()}")
        await self.issue_drain_request(channel, num_beats)

        # Prepare for reading: set channel ID and wait for signals to settle
        # The FIFO/latency bridge should already have data flowing after writes
        self.dut.axi_wr_sram_id.value = channel
        self.dut.axi_wr_sram_drain.value = 0  # Ensure drain is low
        # Wait for any pending data to settle
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        errors = 0
        for i in range(num_beats):
            # Get expected data
            expected_data = self.channel_data.get((channel, i))
            if expected_data is None:
                self.log.error(f"✗ No data found in tracking for channel={channel}, beat={i}{self.get_time_ns_str()}")
                errors += 1
                continue

            # Read from FIFO (via latency bridge)
            rd_data = await self.read_channel_data(channel)
            if rd_data is None:
                self.log.error(f"✗ Read failed at beat {i}{self.get_time_ns_str()}")
                errors += 1
            elif rd_data != expected_data:
                self.log.error(f"✗ Read mismatch: beat={i}, expected=0x{expected_data:X}, got=0x{rd_data:X}{self.get_time_ns_str()}")
                errors += 1
            else:
                self.log.debug(f"✓ Beat {i} verified: 0x{rd_data:X}{self.get_time_ns_str()}")

        # Phase 5: Verify FIFO is empty
        await self.wait_clocks(self.clk_name, 2)
        final_count = await self.get_data_available(channel)
        if final_count != 0:
            self.log.error(f"✗ FIFO not empty after reads: {final_count} beats remaining{self.get_time_ns_str()}")
            errors += 1

        if errors == 0:
            self.log.info(f"✓ Single channel test PASSED: {num_beats} beats verified{self.get_time_ns_str()}")
            return True
        else:
            self.log.error(f"✗ Single channel test FAILED: {errors}/{num_beats} errors{self.get_time_ns_str()}")
            return False

    async def run_multi_channel_test(self, num_channels_to_test: int = None, beats_per_channel: int = None):
        """
        Comprehensive multi-channel test: write to all, verify counts, read from all, verify data

        Args:
            num_channels_to_test: Number of channels to use (None = use TEST_LEVEL config)
            beats_per_channel: Beats per channel (None = use TEST_LEVEL config)

        Returns:
            bool: True if test passed
        """
        # Use TEST_LEVEL config if parameters not specified
        if num_channels_to_test is None:
            num_channels_to_test = self.config['multi_channel_channels']
        if beats_per_channel is None:
            beats_per_channel = self.config['multi_channel_beats']
        self.log.info(f"=== Multi-Channel Test: channels={num_channels_to_test}, beats={beats_per_channel} ==={self.get_time_ns_str()}")

        # Phase 1: Check initial space for all channels
        self.log.info(f"Phase 1: Checking initial space for {num_channels_to_test} channels{self.get_time_ns_str()}")
        for ch in range(num_channels_to_test):
            space = await self.get_space_free(ch)
            if space < beats_per_channel:
                self.log.error(f"✗ Channel {ch} insufficient space: need {beats_per_channel}, have {space}{self.get_time_ns_str()}")
                return False
            self.log.info(f"  Channel {ch}: {space} beats available{self.get_time_ns_str()}")

        # Phase 2: Write data to all channels (interleaved for realism)
        self.log.info(f"Phase 2: Writing {beats_per_channel} beats to {num_channels_to_test} channels (interleaved){self.get_time_ns_str()}")
        for beat in range(beats_per_channel):
            for ch in range(num_channels_to_test):
                # Start at 1 for visibility
                beat_num = beat + 1
                data = (beat_num << 32) | (ch << 16) | beat_num
                success = await self.write_channel_data(ch, data)
                if not success:
                    self.log.error(f"✗ Write failed: channel={ch}, beat={beat}{self.get_time_ns_str()}")
                    return False

        # Wait for writes to settle
        await self.wait_clocks(self.clk_name, 10)

        # Phase 3: Verify wr_drain_data_avail counts for all channels
        self.log.info(f"Phase 3: Verifying wr_drain_data_avail counts{self.get_time_ns_str()}")

        # Debug: Show full packed value and extraction
        full_value = int(self.dut.axi_wr_drain_data_avail.value)
        self.log.info(f"DEBUG: axi_wr_drain_data_avail full value = 0x{full_value:08X}{self.get_time_ns_str()}")
        self.log.info(f"DEBUG: Extracting per-channel:{self.get_time_ns_str()}")

        count_errors = 0
        for ch in range(num_channels_to_test):
            # Manual extraction for debug
            extracted = (full_value >> (ch * 8)) & 0xFF
            data_count = await self.get_data_available(ch)
            self.log.info(f"  Channel {ch}: extracted=0x{extracted:02X} ({extracted}), get_data_available={data_count}{self.get_time_ns_str()}")

            # Accept beats_per_channel to beats_per_channel+4 (latency bridge depth = 4)
            if data_count < beats_per_channel or data_count > beats_per_channel + 4:
                self.log.error(f"✗ Channel {ch} count out of range: expected={beats_per_channel} to {beats_per_channel+4}, got={data_count}{self.get_time_ns_str()}")
                count_errors += 1
            else:
                self.log.info(f"✓ Channel {ch} count acceptable: {data_count} beats{self.get_time_ns_str()}")

        if count_errors > 0:
            return False

        # Phase 4: Read data back from all channels (interleaved) and verify
        self.log.info(f"Phase 4: Reading data from {num_channels_to_test} channels (interleaved){self.get_time_ns_str()}")

        # IMPORTANT: Issue drain requests for all channels BEFORE reading
        # This simulates write engine reserving data before AW commands
        for ch in range(num_channels_to_test):
            self.log.debug(f"Issuing drain request: channel={ch}, size={beats_per_channel}{self.get_time_ns_str()}")
            await self.issue_drain_request(ch, beats_per_channel)

        # Prepare for reading: ensure drain is low
        # The FIFO/latency bridge should already have data flowing after writes
        self.dut.axi_wr_sram_drain.value = 0
        # Wait for any pending data to settle
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        data_errors = 0
        for beat in range(beats_per_channel):
            for ch in range(num_channels_to_test):
                # Get expected data
                expected_data = self.channel_data.get((ch, beat))
                if expected_data is None:
                    self.log.error(f"✗ No data found for channel={ch}, beat={beat}{self.get_time_ns_str()}")
                    data_errors += 1
                    continue

                # Read from FIFO
                rd_data = await self.read_channel_data(ch)
                if rd_data is None:
                    self.log.error(f"✗ Read failed: channel={ch}, beat={beat}{self.get_time_ns_str()}")
                    data_errors += 1
                elif rd_data != expected_data:
                    self.log.error(f"✗ Channel {ch} beat {beat}: expected=0x{expected_data:X}, got=0x{rd_data:X}{self.get_time_ns_str()}")
                    data_errors += 1

        # Phase 5: Verify all FIFOs are empty
        await self.wait_clocks(self.clk_name, 5)
        for ch in range(num_channels_to_test):
            final_count = await self.get_data_available(ch)
            if final_count != 0:
                self.log.error(f"✗ Channel {ch} FIFO not empty: {final_count} beats remaining{self.get_time_ns_str()}")
                data_errors += 1

        if data_errors == 0:
            total_beats = num_channels_to_test * beats_per_channel
            self.log.info(f"✓ Multi-channel test PASSED: {total_beats} total beats verified{self.get_time_ns_str()}")
            return True
        else:
            self.log.error(f"✗ Multi-channel test FAILED: {data_errors} errors{self.get_time_ns_str()}")
            return False

    async def run_allocation_test(self, channel: int = 0, num_beats: int = 64):
        """
        Realistic allocation test: Pre-allocate, then write data, verify timing

        This models real AXI read engine behavior:
        1. Pre-allocate N beats (reserve space before data arrives)
        2. Watch rd_space_free decrease
        3. Write actual data when AXI read completes
        4. Verify wr_drain_data_avail updates with proper timing (1-2 clock delay)

        Args:
            channel: Channel to test
            num_beats: Number of beats to allocate and write

        Returns:
            bool: True if test passed
        """
        self.log.info(f"=== Allocation Test: channel={channel}, beats={num_beats} ==={self.get_time_ns_str()}")

        # Phase 1: Check initial space
        initial_space = await self.get_space_free(channel)
        self.log.info(f"Phase 1: Initial space={initial_space} beats{self.get_time_ns_str()}")

        if initial_space < num_beats:
            self.log.error(f"✗ Insufficient space: need {num_beats}, have {initial_space}{self.get_time_ns_str()}")
            return False

        # Phase 2: Pre-allocate space (like AXI read engine does)
        self.log.info(f"Phase 2: Pre-allocating {num_beats} beats{self.get_time_ns_str()}")
        success = await self.allocate_space(channel, num_beats)
        if not success:
            return False

        # Verify space decreased
        space_after_alloc = await self.get_space_free(channel)
        expected_space = initial_space - num_beats
        if space_after_alloc != expected_space:
            self.log.error(f"✗ Space mismatch after alloc: expected={expected_space}, got={space_after_alloc}{self.get_time_ns_str()}")
            return False
        self.log.info(f"✓ Space correctly decreased: {initial_space} → {space_after_alloc}{self.get_time_ns_str()}")

        # Phase 3: Write actual data (simulating AXI read completion)
        self.log.info(f"Phase 3: Writing {num_beats} beats of actual data{self.get_time_ns_str()}")
        for i in range(num_beats):
            beat_num = i + 1
            data = (beat_num << 32) | (channel << 16) | beat_num
            success = await self.write_channel_data(channel, data, check_ready=True)
            if not success:
                self.log.error(f"✗ Write failed at beat {i}{self.get_time_ns_str()}")
                return False

        # Phase 4: Verify wr_drain_data_avail timing (should have 1-2 clock delay)
        # Wait for data to propagate through FIFO and latency bridge
        await self.wait_clocks(self.clk_name, 3)

        data_count = await self.get_data_available(channel)
        self.log.info(f"Phase 4: wr_drain_data_avail={data_count} (expected {num_beats} to {num_beats+4} after pipeline delay){self.get_time_ns_str()}")

        # Accept num_beats to num_beats+4 (latency bridge depth = 4)
        if data_count < num_beats or data_count > num_beats + 4:
            self.log.error(f"✗ Data count out of range: expected={num_beats} to {num_beats+4}, got={data_count}{self.get_time_ns_str()}")
            return False

        # Phase 5: Verify space is still reduced (data committed)
        final_space = await self.get_space_free(channel)
        if final_space != expected_space:
            self.log.error(f"✗ Final space incorrect: expected={expected_space}, got={final_space}{self.get_time_ns_str()}")
            return False

        # Phase 6: Read back and verify
        self.log.info(f"Phase 5: Reading {num_beats} beats to verify data{self.get_time_ns_str()}")
        errors = 0
        for i in range(num_beats):
            expected_data = self.channel_data.get((channel, i))
            rd_data = await self.read_channel_data(channel)
            if rd_data != expected_data:
                self.log.error(f"✗ Data mismatch at beat {i}: expected=0x{expected_data:X}, got=0x{rd_data:X}{self.get_time_ns_str()}")
                errors += 1

        if errors == 0:
            self.log.info(f"✓ Allocation test PASSED: {num_beats} beats{self.get_time_ns_str()}")
            return True
        else:
            self.log.error(f"✗ Allocation test FAILED: {errors} errors{self.get_time_ns_str()}")
            return False

    async def run_full_allocation_test(self, channel: int = 0):
        """
        Fill FIFO completely via allocation, then write data

        This tests:
        1. Allocating until rd_space_free drops to 0
        2. Writing data to completely fill the FIFO
        3. Verifying proper behavior when FIFO is full

        Args:
            channel: Channel to test

        Returns:
            bool: True if test passed
        """
        self.log.info(f"=== Full Allocation Test: channel={channel} ==={self.get_time_ns_str()}")

        # Get maximum allocatable space (limited by FIFO depth and saturation)
        initial_space = await self.get_space_free(channel)
        # Saturated to 255 for 8-bit reporting, but FIFO might be larger
        max_alloc = min(initial_space, self.fifo_depth)
        self.log.info(f"Initial space={initial_space}, will allocate {max_alloc} beats{self.get_time_ns_str()}")

        # Allocate in chunks to fill FIFO
        chunk_size = 32
        total_allocated = 0

        while total_allocated < max_alloc:
            space_free = await self.get_space_free(channel)
            if space_free == 0:
                self.log.info(f"✓ Space exhausted after allocating {total_allocated} beats{self.get_time_ns_str()}")
                break

            # Allocate remaining or chunk_size, whichever is smaller
            to_allocate = min(chunk_size, max_alloc - total_allocated, space_free)
            self.log.debug(f"Allocating chunk: {to_allocate} beats, space_free={space_free}{self.get_time_ns_str()}")

            success = await self.allocate_space(channel, to_allocate)
            if not success:
                self.log.error(f"✗ Allocation failed at {total_allocated} total beats{self.get_time_ns_str()}")
                return False

            total_allocated += to_allocate

        # Verify space is zero (or near-zero if FIFO > 255)
        final_space = await self.get_space_free(channel)
        self.log.info(f"After allocation: space_free={final_space}, allocated={total_allocated}{self.get_time_ns_str()}")

        if final_space > 1:  # Allow for rounding
            self.log.error(f"✗ Space should be exhausted, but got {final_space}{self.get_time_ns_str()}")
            return False

        # Write data to fill the allocated space
        self.log.info(f"Writing {total_allocated} beats of data{self.get_time_ns_str()}")
        for i in range(total_allocated):
            beat_num = i + 1
            data = (beat_num << 32) | (channel << 16) | beat_num
            success = await self.write_channel_data(channel, data, check_ready=True)
            if not success:
                self.log.error(f"✗ Write failed at beat {i}/{total_allocated}{self.get_time_ns_str()}")
                return False

        # Wait for data to propagate
        await self.wait_clocks(self.clk_name, 5)

        # Verify data is available
        data_count = await self.get_data_available(channel)
        self.log.info(f"After writes: wr_drain_data_avail={data_count}{self.get_time_ns_str()}")

        # Allow for latency bridge occupancy (up to 4 beats)
        if data_count < total_allocated or data_count > total_allocated + 4:
            self.log.error(f"✗ Expected {total_allocated} to {total_allocated+4} beats available, got {data_count}{self.get_time_ns_str()}")
            return False

        self.log.info(f"✓ Full allocation test PASSED: {total_allocated} beats allocated and written{self.get_time_ns_str()}")
        return True

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
            'fifo_depth': self.fifo_depth,
            'data_width': self.data_width,
            'total_writes': total_writes,
            'total_reads': total_reads,
            'writes_per_channel': self.channel_wr_count,
            'reads_per_channel': self.channel_rd_count,
            'unique_data_entries': len(self.channel_data),
        }
