"""
Testbench class for datapath_rd_test module.

Purpose: Test wrapper for read data path streaming performance validation.
        Tests AXI Read Engine → SRAM Controller → SRAM integration.

Author: sean galloway
Created: 2025-10-26
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles
from cocotb.clock import Clock
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

# Add project-specific testbench utilities
from projects.components.stream.dv.tbclasses.descriptor_packet_builder import DescriptorPacketBuilder


class DatapathRdTestTB(TBBase):
    """Testbench for read data path streaming test wrapper."""

    def __init__(self, dut):
        """Initialize testbench.

        Args:
            dut: DUT instance from cocotb
        """
        super().__init__(dut)

        # Store DUT reference
        self.dut = dut

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))
        self.NOSTRESS_MODE = self.convert_to_int(os.environ.get('NOSTRESS_MODE', '0'))
        self.TIMING_PROFILE = os.environ.get('TIMING_PROFILE', 'fixed')  # AXI BFM timing configuration

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}{self.get_time_ns_str()}")
            self.TEST_LEVEL = 'basic'

        # Clock and reset
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # Read parameters from DUT
        self.data_width = int(dut.DATA_WIDTH.value)
        self.num_channels = int(dut.NUM_CHANNELS.value)
        self.sram_depth = int(dut.SRAM_DEPTH.value)
        self.addr_width = 64  # Fixed for test
        self.id_width = 8     # Fixed for test

        # Log configuration
        self.log.info(f"Datapath Read Test TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}, DEBUG={self.DEBUG}{self.get_time_ns_str()}")
        self.log.info(f"NOSTRESS_MODE={'ENABLED' if self.NOSTRESS_MODE else 'DISABLED'}{self.get_time_ns_str()}")
        self.log.info(f"DATA_WIDTH={self.data_width}, NUM_CHANNELS={self.num_channels}, SRAM_DEPTH={self.sram_depth}{self.get_time_ns_str()}")

        # Memory model for AXI slave (represents system memory with 64-byte cache lines)
        # Note: Memory model line size is independent of datapath width
        self.memory_model = MemoryModel(num_lines=262144, bytes_per_line=64)

        # AXI slave (simulates memory on read side)
        self.axi_slave = None  # Created in setup

        # Descriptor packet builder
        self.desc_builder = DescriptorPacketBuilder()

        # Cycle counter for performance measurement
        self.cycle_count = 0

        # Nostress mode bubble detection
        self.bubble_detector_active = False
        self.r_channel_bubbles = []  # List of (cycle, reason) tuples

        # Auto-drain control
        self.auto_drain_active = False
        self.auto_drain_stats = {'total_drained': 0, 'per_channel': [0] * 8}

        # FIFO health monitor control
        self.fifo_health_monitor_active = False
        self.fifo_health_violations = []

    async def setup_clocks_and_reset(self, xfer_beats=16):
        """Complete initialization - clocks and reset.

        Args:
            xfer_beats: Transfer size in beats (default 16, range 1-255)
        """
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize configuration
        # Config register stores ARLEN values (0==1 beat per AXI spec), so subtract 1 from beat count
        self.dut.cfg_axi_rd_xfer_beats.value = xfer_beats - 1
        self.xfer_beats = xfer_beats  # Store for test use
        self.log.info(f"Configured AXI read transfer size: {xfer_beats} beats (ARLEN={xfer_beats-1}){self.get_time_ns_str()}")

        # Initialize descriptor interface signals (all channels)
        for ch_id in range(self.num_channels):
            desc_valid_signal = getattr(self.dut, f'descriptor_{ch_id}_valid')
            desc_packet_signal = getattr(self.dut, f'descriptor_{ch_id}_packet')
            desc_error_signal = getattr(self.dut, f'descriptor_{ch_id}_error')

            desc_valid_signal.value = 0
            desc_packet_signal.value = 0
            desc_error_signal.value = 0

        # Initialize SRAM drain interface (transaction-ID based)
        self.dut.axi_wr_sram_drain.value = 0
        self.dut.axi_wr_sram_id.value = 0

        # Create AXI slave with nostress-aware response delay
        # NOSTRESS mode: zero delays (no BFM-induced bubbles)
        # NORMAL mode: 1-cycle delay for realistic timing
        response_delay = 0 if self.NOSTRESS_MODE else 1
        self.log.info(f"AXI slave response_delay = {response_delay} cycles (NOSTRESS={'ON' if self.NOSTRESS_MODE else 'OFF'}){self.get_time_ns_str()}")

        self.axi_slave = AXI4SlaveRead(
            clock=self.clk,
            reset=self.rst_n,
            data_width=self.data_width,
            addr_width=self.addr_width,
            id_width=self.id_width,
            dut=self.dut,
            prefix='m_axi',
            memory_model=self.memory_model,
            response_delay=response_delay,
            super_debug=True,
            log=self.log
        )

        # Initialize SRAM drain interface signals (ID-multiplexed)
        # This interface uses:
        #   - axi_wr_sram_valid[ch]: Per-channel valid (packed bit vector)
        #   - axi_wr_sram_drain: Shared drain/ready signal (manual control)
        #   - axi_wr_sram_id: Channel selector (manual control)
        #   - axi_wr_sram_data: Multiplexed data output
        #
        # Manual handshaking sequence (per user requirement):
        #   1. Set axi_wr_sram_id to select channel
        #   2. Set axi_wr_sram_drain = 1
        #   3. Wait for falling edge of clk
        #   4. Sample axi_wr_sram_data
        #   5. Clear axi_wr_sram_drain = 0
        self.dut.axi_wr_sram_id.value = 0
        self.dut.axi_wr_sram_drain.value = 0

        # Configure AXI channel timing using canonical randomizer configs
        # Select profile based on test mode (NOSTRESS overrides TIMING_PROFILE)
        timing_profile = 'backtoback' if self.NOSTRESS_MODE else self.TIMING_PROFILE
        self.set_axi_timing_profile(timing_profile)

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        # Start cycle counter background task
        cocotb.start_soon(self._cycle_counter())

        # Start bubble detector in nostress mode
        if self.NOSTRESS_MODE:
            self.bubble_detector_active = True
            cocotb.start_soon(self._bubble_detector())
            self.log.info(f"NOSTRESS bubble detector: ENABLED - will fail on any rready=0 when rvalid=1{self.get_time_ns_str()}")

        # Start auto-drain task in NOSTRESS mode to prevent SRAM overflow
        if self.NOSTRESS_MODE:
            self.auto_drain_active = True
            cocotb.start_soon(self._auto_drain_sram())
            self.log.info(f"NOSTRESS auto-drain: ENABLED - will drain SRAM automatically to prevent stalls{self.get_time_ns_str()}")

        # Start FIFO health monitor to detect pointer bugs
        self.fifo_health_monitor_active = True
        cocotb.start_soon(self._fifo_health_monitor())
        self.log.info(f"FIFO health monitor: ENABLED - will check fifo_count and space_free invariants{self.get_time_ns_str()}")

    async def assert_reset(self):
        """Assert reset signal."""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal."""
        self.rst_n.value = 1

    def set_axi_timing_profile(self, profile_name):
        """
        Configure AXI channel randomizers using canonical timing profiles.

        Applies timing configuration to both AR and R channels of the AXI slave.

        Args:
            profile_name: Timing profile from AXI_RANDOMIZER_CONFIGS
                        ('backtoback', 'fixed', 'fast', 'constrained', etc.)

        Channel Configuration:
            - AR channel (GAXISlave): Controls arready signal timing
            Uses 'slave' config for ready_delay
            - R channel (GAXIMaster): Controls rvalid signal timing
            Uses 'master' config for valid_delay

        Standard Profiles:
            - 'backtoback': Zero delays (NOSTRESS mode - continuous operation)
            - 'fixed': Constant 1-cycle delays
            - 'fast': Mostly zero, occasional short delays
            - 'constrained': Moderate random delays
            - 'burst_pause': Occasional long pauses
            - 'slow_producer': Consistently slow responses
        """
        if profile_name not in AXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown AXI timing profile '{profile_name}', using 'fixed'{self.get_time_ns_str()}")
            profile_name = 'fixed'

        config = AXI_RANDOMIZER_CONFIGS[profile_name]

        # AR channel: GAXISlave drives arready
        # Uses 'slave' config to control ready_delay
        ar_randomizer = FlexRandomizer(config['slave'])
        self.axi_slave.ar_channel.randomizer = ar_randomizer

        # R channel: GAXIMaster drives rvalid
        # Uses 'master' config to control valid_delay
        r_randomizer = FlexRandomizer(config['master'])
        self.axi_slave.r_channel.randomizer = r_randomizer

        # Log configuration details
        mode_str = "NOSTRESS (zero delays)" if profile_name == 'backtoback' else "NORMAL (with delays)"
        self.log.info(f"AXI timing profile: '{profile_name}' - {mode_str}{self.get_time_ns_str()}")
        self.log.info(f"  AR channel (slave/ready): {config['slave']}{self.get_time_ns_str()}")
        self.log.info(f"  R channel (master/valid): {config['master']}{self.get_time_ns_str()}")

    async def _cycle_counter(self):
        """Background task to increment cycle counter on every clock edge."""
        while True:
            await RisingEdge(self.clk)
            self.cycle_count += 1

    async def _bubble_detector(self):
        """Background task to detect AXI R channel bubbles in nostress mode.

        In nostress mode, we expect:
        - AR commands issued as fast as possible (best effort)
        - R channel streaming continuously: rvalid=1 and rready=1

        Any cycle where rvalid=1 and rready=0 is a bubble, indicating either:
        - Configuration limitation (e.g., SRAM full, no space for data)
        - RTL bug (unexpected backpressure)

        This detector logs all bubbles and reports them at test end.
        Enhanced to track burst boundaries for better root cause analysis.

        CRITICAL: Uses dbg_arb_request to distinguish TRUE BUBBLES from SYSTEM IDLE:
        - TRUE BUBBLE: arvalid=0 while arb_request!=0 (channels waiting, arbiter stalled)
        - SYSTEM IDLE: arvalid=0 while arb_request==0 (no channels need service)

        When all channels complete their read phase and move to write phase,
        arb_request goes to 0. This is not a bubble, it's legitimate idle time.
        We filter these cycles AND the first cycle after arb_request resumes
        (to allow arbiter to grant).
        """
        # Skip first few cycles after reset to allow initialization
        await self.wait_clocks(self.clk_name, 20)

        r_transfer_ever_active = False  # Track if we've ever seen a transfer
        r_idle_count = 0  # Count consecutive idle cycles
        bubble_count = 0
        beat_count = 0  # Count beats within current burst
        burst_count = 0  # Count total bursts
        inter_burst_bubbles = 0  # Count bubbles between bursts
        intra_burst_bubbles = 0  # Count bubbles within bursts
        in_burst = False  # Track if we're currently in a burst
        last_burst_end_cycle = 0  # Track when last burst ended

        # Arbiter request tracking for system idle filtering
        arb_request_was_zero = False  # Track if arb_request was 0 last cycle
        cycles_after_resume = 0  # Count cycles after arb_request resumes (filter 0 and 1)

        while self.bubble_detector_active:
            await RisingEdge(self.clk)

            # Read AXI R channel signals including rlast for burst tracking
            try:
                r_valid = int(self.dut.m_axi_rvalid.value)
                r_ready = int(self.dut.m_axi_rready.value)
                r_last = int(self.dut.m_axi_rlast.value) if hasattr(self.dut, 'm_axi_rlast') else 0
                # Read arbiter request vector (0 = all channels idle, no requests pending)
                arb_request = int(self.dut.dbg_arb_request.value) if hasattr(self.dut, 'dbg_arb_request') else 0xFF
            except Exception as e:
                # Signals may not be valid during early initialization
                continue

            # Track burst boundaries
            if r_valid == 1 and r_ready == 1:
                if not r_transfer_ever_active:
                    r_transfer_ever_active = True
                    in_burst = True
                    beat_count = 1
                    burst_count = 1
                    self.log.info(f"R channel first beat @ cycle {self.cycle_count} (burst #{burst_count}){self.get_time_ns_str()}")
                elif not in_burst:
                    # New burst starting
                    in_burst = True
                    beat_count = 1
                    burst_count += 1
                    gap_since_last = self.cycle_count - last_burst_end_cycle
                    self.log.info(f"R channel burst #{burst_count} start @ cycle {self.cycle_count}, {self.get_time_ns_str()}"
                                f"beat #1 (gap since last burst: {gap_since_last} cycles)")
                else:
                    # Continuing burst
                    beat_count += 1

                # Check for burst end (rlast)
                if r_last == 1:
                    self.log.info(f"R channel burst #{burst_count} end @ cycle {self.cycle_count}, {self.get_time_ns_str()}"
                                f"total beats: {beat_count}")
                    in_burst = False
                    last_burst_end_cycle = self.cycle_count
                    self._last_burst_end_cycle = self.cycle_count  # Save for stop_bubble_detector()
                    beat_count = 0

                r_idle_count = 0  # Reset idle counter

            # Track arb_request transitions for filtering
            # Filter cycles when arb_request==0 AND two cycles after it resumes
            # (one for the transition, one for arbiter to settle)
            current_arb_request_zero = (arb_request == 0)

            # Detect rising edge (0 → non-zero transition)
            if arb_request_was_zero and not current_arb_request_zero:
                # arb_request just went non-zero, start counting settle cycles
                cycles_after_resume = 2  # Filter THIS cycle (0) and NEXT cycle (1)
            elif cycles_after_resume > 0:
                # Decrement settle counter
                cycles_after_resume -= 1

            # Track arb_request state for next iteration
            arb_request_was_zero = current_arb_request_zero

            # NOSTRESS bubble detection: after first transfer starts,
            # BOTH rvalid and rready must stay high continuously
            # EXCEPT when arb_request==0 (system idle) or 1 cycle after resume
            if r_transfer_ever_active:
                # Check for any cycle where both are not high
                if not (r_valid == 1 and r_ready == 1):
                    # Filter out system idle periods and arbiter settling
                    # Filter if: (1) arb_request==0 OR (2) cycles_after_resume > 0
                    is_filtered = current_arb_request_zero or (cycles_after_resume > 0)
                    filter_reason = ""
                    if current_arb_request_zero:
                        filter_reason = "FILTERED: arb_request=0 (system idle, all channels in WRITE phase)"
                    elif cycles_after_resume > 0:
                        filter_reason = f"FILTERED: {3-cycles_after_resume} cycle(s) after arb_request resumed (arbiter settling)"

                    # Only count as bubble if NOT filtered
                    if not is_filtered:
                        # Determine bubble type
                        if r_valid == 1 and r_ready == 0:
                            bubble_type = "master backpressure (rvalid=1, rready=0)"
                        elif r_ready == 1 and r_valid == 0:
                            bubble_type = "slave gap (rready=1, rvalid=0)"
                        else:
                            bubble_type = "both idle (rvalid=0, rready=0)"

                        # Classify as inter-burst or intra-burst
                        if in_burst:
                            location = f"INTRA-BURST (burst #{burst_count}, beat #{beat_count})"
                            intra_burst_bubbles += 1
                        else:
                            gap_since_last = self.cycle_count - last_burst_end_cycle if last_burst_end_cycle > 0 else 0
                            location = f"INTER-BURST (gap={gap_since_last} cycles after burst #{burst_count})"
                            inter_burst_bubbles += 1

                        bubble_count += 1
                        bubble_info = (self.cycle_count, bubble_type, location)
                        self.r_channel_bubbles.append(bubble_info)

                        # Log first few bubbles with enhanced info, then summarize
                        if bubble_count <= 5:
                            self.log.warning(f"NOSTRESS BUBBLE #{bubble_count} @ cycle {self.cycle_count}: "
                                           f"{bubble_type} | {location}{self.get_time_ns_str()}")
                        elif bubble_count == 6:
                            self.log.warning(f"NOSTRESS: {bubble_count} bubbles detected, "
                                        f"suppressing further warnings (will report total at end){self.get_time_ns_str()}")
                    else:
                        # Log filtered idle for debugging (first few only)
                        if bubble_count <= 5:
                            self.log.debug(f"@ cycle {self.cycle_count}: {filter_reason}{self.get_time_ns_str()}")

                    # Count consecutive idle cycles to detect end of burst
                    if r_valid == 0:
                        r_idle_count += 1
                        # After 50 idle cycles, assume all transfers complete
                        if r_idle_count >= 50:
                            self.log.info(f"R channel idle for 50 cycles @ {self.cycle_count} - all transfers complete{self.get_time_ns_str()}")
                            self.log.info(f"Bubble summary: {intra_burst_bubbles} intra-burst, {self.get_time_ns_str()}"
                                        f"{inter_burst_bubbles} inter-burst, {bubble_count} total")
                            r_transfer_ever_active = False  # Reset for next round of transfers
                            r_idle_count = 0
                            in_burst = False

    def stop_bubble_detector(self):
        """Stop bubble detector and return results.

        Filters out bubbles that occurred after the last valid rlast transaction,
        as these are cleanup/idle cycles, not actual RTL bubbles.
        """
        self.bubble_detector_active = False

        # Filter out bubbles after last burst ended (cleanup cycles)
        # Get the last_burst_end_cycle from the detector task
        if hasattr(self, '_last_burst_end_cycle') and self._last_burst_end_cycle > 0:
            valid_bubbles = [b for b in self.r_channel_bubbles if b[0] <= self._last_burst_end_cycle]
            filtered_count = len(self.r_channel_bubbles) - len(valid_bubbles)
            if filtered_count > 0:
                self.log.info(f"Bubble detector: Filtered out {filtered_count} cleanup-phase bubbles "
                             f"(occurred after last rlast @ cycle {self._last_burst_end_cycle})")
            return len(valid_bubbles), valid_bubbles
        else:
            return len(self.r_channel_bubbles), self.r_channel_bubbles

    async def _auto_drain_sram(self):
        """Background task to automatically drain SRAM to prevent overflow.

        Drains at 1 beat/cycle to match AXI R load rate.

        CRITICAL: Only drains when axi_wr_drain_data_avail shows data present
        to prevent FIFO underflow.
        """
        # Skip first few cycles after reset
        await self.wait_clocks(self.clk_name, 15)

        drain_count = 0
        last_channel_drained = -1

        self.log.info(f"Auto-drain: Starting SRAM drain (1 beat/cycle, only when data available){self.get_time_ns_str()}")

        while self.auto_drain_active:
            # Read data availability for all channels (current state)
            try:
                data_avail_bv = self.dut.axi_wr_drain_data_avail.value
            except Exception as e:
                # Signals not ready, wait and retry
                await RisingEdge(self.clk)
                continue

            # Convert to list of data available per channel
            # axi_wr_drain_data_avail is [NUM_CHANNELS-1:0][7:0]
            channels_with_data = []
            for ch_id in range(self.num_channels):
                # Extract 8-bit count for this channel
                shift = ch_id * 8
                mask = 0xFF << shift
                data_avail = (int(data_avail_bv) & mask) >> shift

                if data_avail > 0:
                    channels_with_data.append((ch_id, data_avail))

            # DRAIN ALL CHANNELS WITH DATA (not just one!)
            # Each channel can drain 1 beat/cycle, so drain all simultaneously
            if channels_with_data:
                # Build mask of all channels with data
                drain_mask = 0
                for ch_id, count in channels_with_data:
                    drain_mask |= (1 << ch_id)

                # Set drain_decoded directly (multi-channel drain)
                # Note: axi_wr_sram_drain is actually drain_decoded in the DUT
                # We need to assert drain for each channel separately
                # Since we only have one drain signal, we need to drain one at a time
                # but cycle through them as fast as possible

                # Select next channel to drain (round-robin)
                selected = None
                for ch_id, count in channels_with_data:
                    if ch_id > last_channel_drained:
                        selected = (ch_id, count)
                        break

                if selected is None:
                    selected = channels_with_data[0]

                ch_id, count = selected

                # Set drain signals for THIS channel this cycle
                self.dut.axi_wr_sram_drain.value = 1
                self.dut.axi_wr_sram_id.value = ch_id

                # Update stats
                drain_count += 1
                self.auto_drain_stats['total_drained'] += 1
                self.auto_drain_stats['per_channel'][ch_id] += 1
                last_channel_drained = ch_id

                # Log periodically with WARNING if falling behind
                if drain_count % 100 == 0:
                    channels_active = len(channels_with_data)
                    self.log.info(f"Auto-drain: Drained {drain_count} beats total, {self.get_time_ns_str()}"
                                f"active channels: {channels_active}, "
                                f"per-channel: {self.auto_drain_stats['per_channel'][:self.num_channels]}")
                    if channels_active > 1:
                        self.log.warning(f"Auto-drain: {channels_active} channels active but can only drain 1/cycle - SRAM will back up!{self.get_time_ns_str()}")
            else:
                # NO data available - deassert drain
                self.dut.axi_wr_sram_drain.value = 0
                self.dut.axi_wr_sram_id.value = 0

            # Wait for clock edge (drain takes effect)
            await RisingEdge(self.clk)

        # Stop draining
        self.dut.axi_wr_sram_drain.value = 0
        self.dut.axi_wr_sram_id.value = 0
        self.log.info(f"Auto-drain: Stopped - drained {drain_count} beats total{self.get_time_ns_str()}")

    def stop_auto_drain(self):
        """Stop auto-drain task and return statistics."""
        self.auto_drain_active = False
        return self.auto_drain_stats

    async def _fifo_health_monitor(self):
        """Background task to monitor FIFO count and space_free invariants.

        Detects pointer bugs by checking that:
        1. fifo_count + alloc_space_free ≈ DEPTH (accounting for in-flight)
        2. All 3 values (fifo_count, alloc_space_free, rd_space_free) should NEVER all be 0
        3. If fifo_count=0, space_free should be near DEPTH

        This helps identify pointer management bugs in sram_controller_unit.
        """
        # Skip first few cycles after reset
        await self.wait_clocks(self.clk_name, 20)

        violation_count = 0
        last_log_cycle = 0

        self.log.info(f"FIFO health monitor: Starting checks on all channels{self.get_time_ns_str()}")

        while self.fifo_health_monitor_active:
            await RisingEdge(self.clk)

            # Check each channel's FIFO health
            for ch_id in range(self.num_channels):
                try:
                    # Access sram_controller_unit internals for this channel
                    # Hierarchy: u_sram_controller.gen_channel[ch_id].u_channel_unit
                    channel_unit = self.dut.u_sram_controller.gen_channel[ch_id].u_channel_unit

                    fifo_count = int(channel_unit.fifo_count.value)
                    alloc_space_free = int(channel_unit.alloc_space_free.value)
                    rd_space_free = int(channel_unit.rd_space_free.value)

                    # CRITICAL BUG DETECTION: All 3 values = 0 should NEVER happen
                    if fifo_count == 0 and alloc_space_free == 0 and rd_space_free == 0:
                        violation_count += 1
                        violation_info = (self.cycle_count, ch_id, fifo_count, alloc_space_free, rd_space_free)
                        self.fifo_health_violations.append(violation_info)

                        # Log first few violations and periodically after
                        if violation_count <= 5 or (self.cycle_count - last_log_cycle) > 100:
                            self.log.error(f"FIFO HEALTH VIOLATION #{violation_count} @ cycle {self.cycle_count}{self.get_time_ns_str()}")
                            self.log.error(f"  Channel {ch_id}: fifo_count={fifo_count}, {self.get_time_ns_str()}"
                                         f"alloc_space_free={alloc_space_free}, rd_space_free={rd_space_free}")
                            self.log.error(f"  ALL ZEROS - This indicates a pointer management bug!{self.get_time_ns_str()}")
                            last_log_cycle = self.cycle_count

                    # Secondary check: fifo_count + alloc_space_free should be reasonable
                    # SRAM depth is per-channel: self.sram_depth // self.num_channels
                    per_channel_depth = self.sram_depth // self.num_channels

                    # Allow some margin for in-flight transactions (±10)
                    total = fifo_count + alloc_space_free
                    if abs(total - per_channel_depth) > 10:
                        # This might indicate pointer wraparound or accounting bug
                        violation_info = (self.cycle_count, ch_id, fifo_count, alloc_space_free, rd_space_free)
                        if violation_info not in self.fifo_health_violations:
                            self.fifo_health_violations.append(violation_info)
                            if (self.cycle_count - last_log_cycle) > 100:
                                self.log.warning(f"FIFO accounting mismatch @ cycle {self.cycle_count}{self.get_time_ns_str()}")
                                self.log.warning(f"  Channel {ch_id}: fifo_count={fifo_count}, {self.get_time_ns_str()}"
                                               f"alloc_space_free={alloc_space_free}, "
                                               f"total={total}, expected≈{per_channel_depth}")
                                last_log_cycle = self.cycle_count

                except Exception as e:
                    # Signals might not be accessible, skip this check
                    continue

        self.log.info(f"FIFO health monitor: Stopped - detected {violation_count} violations{self.get_time_ns_str()}")

    def stop_fifo_health_monitor(self):
        """Stop FIFO health monitor and return violations."""
        self.fifo_health_monitor_active = False
        return len(self.fifo_health_violations), self.fifo_health_violations

    async def _channel_transaction_counter(self, channel_id):
        """Monitor and count SRAM writes and drains for a specific channel.

        Args:
            channel_id: Channel to monitor
        """
        writes = 0
        drains = 0

        self.log.info(f"Channel {channel_id} transaction counter: STARTED{self.get_time_ns_str()}")

        try:
            while True:
                await RisingEdge(self.clk)

                # Count SRAM writes (axi_rd_sram_valid && axi_rd_sram_id == channel_id)
                if int(self.dut.axi_rd_sram_valid.value) == 1:
                    axi_id = int(self.dut.axi_rd_sram_id.value)
                    if axi_id == channel_id:
                        # Check if ready (successful handshake)
                        if int(self.dut.axi_rd_sram_ready.value) == 1:
                            writes += 1
                            if writes <= 5 or writes >= 45:  # Log first/last few
                                self.log.info(f"CH{channel_id} WRITE #{writes} @ {cocotb.utils.get_sim_time(units='ns'):.0f} ns{self.get_time_ns_str()}")

                # Count SRAM drains (axi_wr_sram_drain && axi_wr_sram_id == channel_id)
                if int(self.dut.axi_wr_sram_drain.value) == 1:
                    drain_id = int(self.dut.axi_wr_sram_id.value)
                    if drain_id == channel_id:
                        drains += 1
                        if drains <= 5 or drains >= 45:  # Log first/last few
                            self.log.info(f"CH{channel_id} DRAIN #{drains} @ {cocotb.utils.get_sim_time(units='ns'):.0f} ns{self.get_time_ns_str()}")

        except Exception as e:
            self.log.info(f"Channel {channel_id} transaction counter: STOPPED{self.get_time_ns_str()}")
            self.log.error(f"!!! CHANNEL {channel_id} TRANSACTION SUMMARY{self.get_time_ns_str()} !!!")
            self.log.error(f"  Total WRITES: {writes}{self.get_time_ns_str()}")
            self.log.error(f"  Total DRAINS: {drains}{self.get_time_ns_str()}")
            self.log.error(f"  DIFFERENCE:   {writes - drains} (writes - drains){self.get_time_ns_str()}")
            if writes != drains:
                self.log.error(f"  >>> BUG: Write/drain mismatch! Expected equal counts.{self.get_time_ns_str()}")
            return writes, drains

    def start_channel_transaction_counter(self, channel_id):
        """Start monitoring transactions for a channel."""
        self.channel_counter_task = cocotb.start_soon(self._channel_transaction_counter(channel_id))

    def stop_channel_transaction_counter(self):
        """Stop channel transaction counter."""
        if hasattr(self, 'channel_counter_task'):
            self.channel_counter_task.kill()

    async def _sram_ready_keeper(self):
        """Background task (DEPRECATED - no longer needed with transaction-ID based drain)."""
        # With transaction-ID based drain interface, ready is not needed
        # TB explicitly drives drain + ID to pull data
        self.log.debug(f"SRAM ready keeper: No longer needed with transaction-ID drain interface{self.get_time_ns_str()}")
        pass

    def _increment_data_pattern(self, bytes_per_beat, addr):
        # Pattern: LOWER 4 BYTES for waveform visibility!
        #   - Byte 0 (LSB): Burst position (0x01-0x08) - EASY TO SEE in waves!
        #   - Bytes 1-3: Address bits [23:0] (3 bytes) - UNIQUE, INCREMENTING!
        #   - Bytes 4-31: 0x00
        # Example: Beat 0 @ 0x0000 = 0x00000001, Beat 1 @ 0x0020 = 0x00002002
        #          Beat 8 @ 0x0100 = 0x00010001 (burst wraps, address increments)
        # Waveform shows data[31:0] = address << 8 | burst_pos (VISIBLE!)
        data = bytearray()
        beat = addr // bytes_per_beat
        burst_pos = (beat % 8) + 1

        for byte_idx in range(bytes_per_beat):
            if byte_idx == 0:  # Byte 0 (LSB) - Burst position (VISIBLE!)
                byte_val = burst_pos  # 0x01-0x08
            elif byte_idx == 1:  # Byte 1 - Address low byte
                byte_val = addr & 0xFF          # Address bits [7:0]
            elif byte_idx == 2:  # Byte 2 - Address mid byte
                byte_val = (addr >> 8) & 0xFF   # Address bits [15:8]
            elif byte_idx == 3:  # Byte 3 - Address high byte
                byte_val = (addr >> 16) & 0xFF  # Address bits [23:16]
            else:
                byte_val = 0x00
            data.append(byte_val)

        return data

    async def populate_memory(self, start_addr, num_beats, pattern='increment'):
        """Populate memory model with test data.

        Args:
            start_addr: Starting address (must be aligned)
            num_beats: Number of beats to populate
            pattern: 'increment', 'random', or 'fixed'
        """
        bytes_per_beat = self.data_width // 8

        for beat in range(num_beats):
            addr = start_addr + (beat * bytes_per_beat)

            if pattern == 'increment':
                data = self._increment_data_pattern(bytes_per_beat, addr)
            elif pattern == 'fixed':
                # Fixed pattern for easy verification
                data = bytearray([0xAA] * bytes_per_beat)
            else:
                # Random pattern
                import random
                data = bytearray([random.randint(0, 255) for _ in range(bytes_per_beat)])

            # Write to memory model
            self.memory_model.write(addr, data)

    async def issue_descriptor_packet(self, channel_id, src_addr, length, last=True):
        """Issue a single descriptor packet to a channel.

        Args:
            channel_id: Channel ID (0-7)
            src_addr: Source address (must be aligned)
            length: Transfer length in BEATS
            last: Last descriptor flag (default True)

        Returns:
            bool: True if descriptor accepted, False on timeout
        """
        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel_id {channel_id}, max is {self.num_channels-1}{self.get_time_ns_str()}")
            return False

        # Build descriptor packet
        packet = self.desc_builder.build_descriptor_packet(
            src_addr=src_addr,
            dst_addr=0,  # Unused in read-only test
            length=length,
            next_ptr=0,  # No chaining in this test
            valid=True,
            last=last,
            channel_id=channel_id
        )

        # Get descriptor interface signals for this channel
        desc_valid_signal = getattr(self.dut, f'descriptor_{channel_id}_valid')
        desc_ready_signal = getattr(self.dut, f'descriptor_{channel_id}_ready')
        desc_packet_signal = getattr(self.dut, f'descriptor_{channel_id}_packet')
        desc_error_signal = getattr(self.dut, f'descriptor_{channel_id}_error')

        # Drive descriptor packet
        desc_valid_signal.value = 1
        desc_packet_signal.value = packet
        desc_error_signal.value = 0

        # Wait for ready handshake
        timeout_cycles = 1000
        for cycle in range(timeout_cycles):
            await RisingEdge(self.clk)
            if int(desc_ready_signal.value) == 1:
                # Handshake complete
                desc_valid_signal.value = 0
                self.log.info(f"Channel {channel_id}: Descriptor accepted - {self.get_time_ns_str()}"
                            f"src_addr=0x{src_addr:016X}, length={length} beats")
                return True

        # Timeout
        desc_valid_signal.value = 0
        self.log.error(f"Channel {channel_id}: Descriptor timeout after {timeout_cycles} cycles{self.get_time_ns_str()}")
        self.log.error(f"  This likely indicates SRAM is full or scheduler not accepting{self.get_time_ns_str()}")
        return False

    async def issue_multiple_requests(self, channel_id, start_addr, num_requests, beats_per_request, burst_len):
        """Issue multiple descriptor packets sequentially.

        Each descriptor represents a separate transfer. The scheduler inside the DUT
        will parse each descriptor and drive the read engine continuously.

        NOTE: burst_len parameter is ignored - the scheduler and read engine decide
        burst sizes autonomously based on cfg_axi_rd_xfer_beats configuration.

        Args:
            channel_id: Channel ID (0-7)
            start_addr: Starting address for first descriptor
            num_requests: Number of descriptors to issue
            beats_per_request: Beats per descriptor
            burst_len: Ignored (kept for API compatibility)

        Returns:
            bool: True if all descriptors issued successfully
        """
        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel_id {channel_id}, max is {self.num_channels-1}{self.get_time_ns_str()}")
            return False

        bytes_per_beat = self.data_width // 8

        self.log.info(f"Channel {channel_id}: Issuing {num_requests} descriptors {self.get_time_ns_str()}"
                    f"({beats_per_request} beats each) "
                    f"[NOSTRESS={'ON' if self.NOSTRESS_MODE else 'OFF'}]")

        for req_idx in range(num_requests):
            # Calculate address for this descriptor
            req_addr = start_addr + (req_idx * beats_per_request * bytes_per_beat)

            # Issue descriptor packet
            success = await self.issue_descriptor_packet(
                channel_id=channel_id,
                src_addr=req_addr,
                length=beats_per_request,
                last=True  # Each descriptor is independent
            )

            if not success:
                self.log.error(f"Channel {channel_id}: Failed to issue descriptor {req_idx + 1}/{num_requests}{self.get_time_ns_str()}")
                return False

            # Log progress periodically
            if (req_idx + 1) % 10 == 0 or (req_idx + 1) == num_requests:
                self.log.info(f"Channel {channel_id}: Issued {req_idx + 1}/{num_requests} descriptors{self.get_time_ns_str()}")

            # In NOSTRESS mode, issue back-to-back (no gaps)
            # In NORMAL mode, brief wait between descriptors
            if not self.NOSTRESS_MODE:
                await self.wait_clocks(self.clk_name, 1)

        self.log.info(f"Channel {channel_id}: All {num_requests} descriptors issued successfully{self.get_time_ns_str()}")
        return True

    async def kick_off_all_channels(self, descriptors_per_channel, beats_per_descriptor, start_addr_base=0x100000):
        """Kick off all channels simultaneously for true NOSTRESS zero-bubble operation.

        Pre-loads all channels with descriptors so all schedulers are ready from the start.

        Args:
            descriptors_per_channel: Number of descriptors to pre-load per channel
            beats_per_descriptor: Beats per descriptor
            start_addr_base: Base address (each channel gets offset region)

        Returns:
            bool: True if all channels kicked off successfully
        """
        bytes_per_beat = self.data_width // 8
        bytes_per_descriptor = beats_per_descriptor * bytes_per_beat

        # Pre-populate memory for all channels
        self.log.info(f"Pre-populating memory for {self.num_channels} channels...{self.get_time_ns_str()}")
        for ch_id in range(self.num_channels):
            ch_base_addr = start_addr_base + (ch_id * descriptors_per_channel * bytes_per_descriptor)
            total_bytes = descriptors_per_channel * bytes_per_descriptor
            total_beats = total_bytes // bytes_per_beat
            await self.populate_memory(ch_base_addr, total_beats, pattern='increment')

        # Kick off all channels simultaneously (issue first descriptor to each)
        self.log.info(f"Kicking off all {self.num_channels} channels simultaneously...{self.get_time_ns_str()}")
        success_list = []
        for ch_id in range(self.num_channels):
            ch_base_addr = start_addr_base + (ch_id * descriptors_per_channel * bytes_per_descriptor)

            # Issue first descriptor to this channel
            success = await self.issue_descriptor_packet(
                channel_id=ch_id,
                src_addr=ch_base_addr,
                length=beats_per_descriptor,
                last=False  # More descriptors will follow
            )
            success_list.append(success)

            if not success:
                self.log.error(f"Channel {ch_id}: Failed to kick off{self.get_time_ns_str()}")
                return False

        # Issue remaining descriptors to all channels in round-robin fashion
        # This keeps all schedulers fed continuously
        for desc_idx in range(1, descriptors_per_channel):
            for ch_id in range(self.num_channels):
                ch_base_addr = start_addr_base + (ch_id * descriptors_per_channel * bytes_per_descriptor)
                desc_addr = ch_base_addr + (desc_idx * bytes_per_descriptor)

                is_last = (desc_idx == descriptors_per_channel - 1)
                success = await self.issue_descriptor_packet(
                    channel_id=ch_id,
                    src_addr=desc_addr,
                    length=beats_per_descriptor,
                    last=is_last
                )

                if not success:
                    self.log.error(f"Channel {ch_id}: Failed to issue descriptor {desc_idx + 1}{self.get_time_ns_str()}")
                    return False

            # Log progress periodically
            if (desc_idx + 1) % 5 == 0 or (desc_idx + 1) == descriptors_per_channel:
                self.log.info(f"Issued descriptor {desc_idx + 1}/{descriptors_per_channel} to all channels{self.get_time_ns_str()}")

        self.log.info(f"✓ All {self.num_channels} channels kicked off with {descriptors_per_channel} descriptors each{self.get_time_ns_str()}")
        return True

    async def wait_for_completion(self, channel_id=0, expected_beats=0, timeout_cycles=10000):
        """Wait for channel transfer to complete by monitoring SRAM fill.

        Args:
            channel_id: Channel ID to wait for (default 0)
            expected_beats: Expected beats to be written to SRAM
            timeout_cycles: Maximum cycles to wait

        Returns:
            (success, beats_done, error, error_resp)
        """
        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel_id {channel_id}{self.get_time_ns_str()}")
            return (False, 0, 1, 0)

        # Wait for expected data to appear in SRAM
        if expected_beats > 0:
            success = await self.wait_for_sram_data(channel_id, expected_beats, timeout_cycles)
            if success:
                return (True, expected_beats, 0, 0)
            else:
                return (False, 0, 1, 0)

        # If no expected_beats specified, just wait briefly
        await self.wait_clocks(self.clk_name, 100)
        return (True, 0, 0, 0)

    async def validate_completion_signal_sticky(self, channel_id=0, duration_cycles=1000):
        """
        Validate that axi_rd_all_complete signal stays HIGH once asserted.

        CRITICAL: This catches the completion signal pulsing bug that caused
        all core tests to hang. The signal must be STICKY - once it goes HIGH
        (indicating all transactions complete), it must STAY HIGH until a new
        transfer starts.

        Args:
            channel_id: Channel ID to monitor
            duration_cycles: How many cycles to monitor

        Returns:
            bool: True if signal behaves correctly, False if it pulses
        """
        completion_changes = []
        prev_complete = 0

        for cycle in range(duration_cycles):
            await RisingEdge(self.clk)

            # Read completion signal
            try:
                complete_reg = int(self.dut.axi_rd_all_complete.value)
                complete_ch = (complete_reg >> channel_id) & 0x1
            except:
                self.log.warning(f"Could not read axi_rd_all_complete{self.get_time_ns_str()}")
                continue

            # Detect changes
            if complete_ch != prev_complete:
                completion_changes.append({
                    'cycle': cycle,
                    'value': complete_ch,
                    'transition': f"{prev_complete} -> {complete_ch}"
                })
                self.log.info(f"Channel {channel_id} axi_rd_all_complete: {prev_complete} -> {complete_ch} @ cycle {cycle}{self.get_time_ns_str()}")

            prev_complete = complete_ch

        # Validate: Once HIGH, must stay HIGH (sticky behavior)
        went_high = False
        for change in completion_changes:
            if change['value'] == 1:
                went_high = True
            elif went_high and change['value'] == 0:
                # BUG! Signal went LOW after going HIGH
                self.log.error(f"❌ COMPLETION SIGNAL BUG DETECTED: Channel {channel_id} axi_rd_all_complete went LOW after going HIGH!{self.get_time_ns_str()}")
                self.log.error(f"   Changes: {completion_changes}{self.get_time_ns_str()}")
                return False

        if went_high:
            self.log.info(f"✅ Channel {channel_id} axi_rd_all_complete is STICKY (stayed HIGH after going HIGH){self.get_time_ns_str()}")
        else:
            self.log.debug(f"Channel {channel_id} axi_rd_all_complete never went HIGH (no transactions?){self.get_time_ns_str()}")

        return True

    async def check_sram_fill(self, channel_id, expected_count=None, timeout_cycles=5000):
        """Check SRAM fill level for channel.

        Args:
            channel_id: Channel ID to check
            expected_count: Expected count (None = any count, no wait)
            timeout_cycles: Maximum cycles to wait for expected_count

        Returns:
            Current count
        """
        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel_id {channel_id}{self.get_time_ns_str()}")
            return 0

        seg_count_width = 13  # $clog2(512) + 1 for default 4096/8 = 512 segment size
        count_mask = (1 << seg_count_width) - 1

        # If no expected count, just read once
        if expected_count is None:
            await RisingEdge(self.clk)
            has_data_value = int(self.dut.axi_wr_has_data.value)
            count = (has_data_value >> (channel_id * seg_count_width)) & count_mask
            return count

        # Poll until expected count reached or timeout
        for cycle in range(timeout_cycles):
            await RisingEdge(self.clk)
            has_data_value = int(self.dut.axi_wr_has_data.value)
            count = (has_data_value >> (channel_id * seg_count_width)) & count_mask

            if count == expected_count:
                self.log.info(f"Channel {channel_id}: SRAM fill reached {count}/{expected_count} after {cycle} cycles{self.get_time_ns_str()}")
                return count

            # Log progress periodically
            if cycle % 100 == 0 and cycle > 0:
                self.log.debug(f"Channel {channel_id}: SRAM fill {count}/{expected_count} (cycle {cycle}/{timeout_cycles}){self.get_time_ns_str()}")

        # Timeout - assert failure
        assert count == expected_count, \
            f"Channel {channel_id} SRAM count timeout: got {count}, expected {expected_count} after {timeout_cycles} cycles"

        return count

    async def wait_for_sram_data(self, channel_id, expected_count, timeout_cycles=1000):
        """Wait for expected number of beats to be available in SRAM.

        Args:
            channel_id: Channel ID to check
            expected_count: Expected number of beats in SRAM
            timeout_cycles: Max cycles to wait

        Returns:
            bool: True if expected count reached, False on timeout
        """
        import math

        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel_id {channel_id}{self.get_time_ns_str()}")
            return False

        # Calculate correct bit extraction for flattened unpacked array
        # axi_wr_drain_data_avail is [NC-1:0][SEG_COUNT_WIDTH-1:0]
        seg_size = self.sram_depth // self.num_channels
        seg_count_width = math.ceil(math.log2(seg_size)) + 1 if seg_size > 1 else 1
        shift = channel_id * seg_count_width
        mask = (1 << seg_count_width) - 1

        for cycle in range(timeout_cycles):
            await RisingEdge(self.clk)

            # Read data_available for this channel
            try:
                data_avail_bv = self.dut.axi_wr_drain_data_avail.value
                full_value = int(data_avail_bv)
                data_available = (full_value >> shift) & mask
            except Exception as e:
                self.log.error(f"Failed to read data_available: {e}{self.get_time_ns_str()}")
                return False

            if data_available >= expected_count:
                self.log.info(f"Channel {channel_id}: SRAM has {data_available} beats (expected {expected_count}) after {cycle} cycles{self.get_time_ns_str()}")
                return True

            # Log progress periodically
            if cycle % 100 == 0 and cycle > 0:
                self.log.debug(f"Channel {channel_id}: SRAM has {data_available}/{expected_count} beats (cycle {cycle}/{timeout_cycles}){self.get_time_ns_str()}")

        # Timeout
        self.log.error(f"Channel {channel_id}: Timeout waiting for {expected_count} beats (has {data_available}) after {timeout_cycles} cycles{self.get_time_ns_str()}")
        return False

    async def read_sram_data(self, channel_id, timeout_cycles=100):
        """Read one beat of data from SRAM using GAXI slave interface.

        Args:
            channel_id: Channel ID to read from
            timeout_cycles: Max cycles to wait for data

        Returns:
            int: Data read from SRAM (or None on timeout/error)

        Note: Uses GAXI slave component for proper valid/ready handshaking
        """
        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel_id {channel_id}{self.get_time_ns_str()}")
            return None

        # Check if data is available for this channel
        # axi_wr_drain_data_avail is [NC-1:0][$clog2(FIFO_DEPTH):0]
        import math
        # Wait for data to become available (with timeout)
        # FIX: With REGISTERED=1 FIFOs/bridge, data_available has pipeline delay
        # Must WAIT for it to update, not check once and give up!
        data_available = 0

        # FIX: axi_wr_drain_data_avail is [NC-1:0][SEG_COUNT_WIDTH-1:0] unpacked array
        # CocoTB flattens it to packed, so use correct bit width for extraction
        # SEG_SIZE = SRAM_DEPTH / NUM_CHANNELS, SEG_COUNT_WIDTH = $clog2(SEG_SIZE) + 1
        seg_size = self.sram_depth // self.num_channels
        seg_count_width = math.ceil(math.log2(seg_size)) + 1 if seg_size > 1 else 1
        shift = channel_id * seg_count_width
        mask = (1 << seg_count_width) - 1

        for wait_cycle in range(timeout_cycles):
            try:
                data_avail_bv = self.dut.axi_wr_drain_data_avail.value
                full_value = int(data_avail_bv)
                data_available = (full_value >> shift) & mask

                if data_available > 0:
                    self.log.debug(f"Channel {channel_id}: data_available = {data_available} after {wait_cycle} cycles{self.get_time_ns_str()}")
                    break  # Data is ready!

                # Wait one more cycle
                await RisingEdge(self.clk)

            except Exception as e:
                self.log.error(f"Failed to read data_available: {e}{self.get_time_ns_str()}")
                return None

        if data_available == 0:
            self.log.error(f"Channel {channel_id}: No data available after {timeout_cycles} cycles{self.get_time_ns_str()}")
            return None

        # Manual handshaking sequence for ID-multiplexed interface
        # Per user requirement: sample data on falling edge after drain is driven

        # Step 1: Set channel ID to select which channel to drain
        self.dut.axi_wr_sram_id.value = channel_id
        self.log.debug(f"Channel {channel_id}: Set axi_wr_sram_id = {channel_id}{self.get_time_ns_str()}")

        # Step 2: Drive drain signal high
        self.dut.axi_wr_sram_drain.value = 1
        self.log.debug(f"Channel {channel_id}: Asserted axi_wr_sram_drain{self.get_time_ns_str()}")

        # Step 3: Wait for falling edge of clock (gives RTL time to respond)
        await FallingEdge(self.clk)

        # Step 4: Sample the data on falling edge
        data = int(self.dut.axi_wr_sram_data.value)
        self.log.debug(f"Channel {channel_id}: Sampled data = 0x{data:X}{self.get_time_ns_str()}")

        # Step 5: Clear drain signal
        self.dut.axi_wr_sram_drain.value = 0
        self.log.debug(f"Channel {channel_id}: Cleared axi_wr_sram_drain{self.get_time_ns_str()}")

        return data

    async def drain_and_verify_sram(self, channel_id, expected_beats, start_addr):
        """Drain SRAM and verify data matches expected pattern.

        Args:
            channel_id: Channel ID to drain
            expected_beats: Number of beats to verify
            start_addr: Starting address used for pattern generation

        Returns:
            (bool, int): (success, error_count)
        """
        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel_id {channel_id}{self.get_time_ns_str()}")
            return (False, expected_beats)

        self.log.info(f"Channel {channel_id}: Draining and verifying {expected_beats} beats{self.get_time_ns_str()}")

        errors = 0
        bytes_per_beat = self.data_width // 8

        for beat_idx in range(expected_beats):
            # Read data from SRAM using transaction-ID based drain
            actual_data = await self.read_sram_data(channel_id, timeout_cycles=1000)
            if actual_data is None:
                self.log.error(f"Channel {channel_id}: Failed to read beat {beat_idx}{self.get_time_ns_str()}")
                errors += 1
                continue

            # Generate expected data (matches populate_memory increment pattern)
            # Simple incrementing bytes: 0x01, 0x02, 0x03, 0x04, ... 0x11, 0x12, 0x13...
            addr = start_addr + (beat_idx * bytes_per_beat)
            expected_data_bytes = self._increment_data_pattern(bytes_per_beat, addr)
            # Convert bytearray to integer (little-endian to match RTL)
            expected_data = int.from_bytes(expected_data_bytes, byteorder='little')
            # for byte_idx in range(bytes_per_beat):
            #     byte_val = (beat_idx * bytes_per_beat + byte_idx + 1) & 0xFF
            #     expected_data |= (byte_val << (byte_idx * 8))

            # Verify
            if actual_data != expected_data:
                # Enhanced error logging for debugging
                self.log.error(f"Channel {channel_id} beat {beat_idx}: MISMATCH{self.get_time_ns_str()}")
                self.log.error(f"  Expected: 0x{expected_data:064X}{self.get_time_ns_str()}")
                self.log.error(f"  Got:      0x{actual_data:064X}{self.get_time_ns_str()}")
                self.log.error(f"  Addr used for pattern: 0x{addr:X}{self.get_time_ns_str()}")
                # Show first few bytes for easy comparison
                exp_bytes = f"{(expected_data & 0xFFFFFFFF):08X}"
                got_bytes = f"{(actual_data & 0xFFFFFFFF):08X}"
                self.log.error(f"  Expected[31:0]: 0x{exp_bytes}, Got[31:0]: 0x{got_bytes}{self.get_time_ns_str()}")
                errors += 1
            else:
                self.log.debug(f"Channel {channel_id} beat {beat_idx}: ✓ Match (0x{actual_data:X}){self.get_time_ns_str()}")

        if errors == 0:
            self.log.info(f"Channel {channel_id}: ✓ All {expected_beats} beats verified{self.get_time_ns_str()}")
            return (True, 0)
        else:
            self.log.error(f"Channel {channel_id}: ✗ {errors}/{expected_beats} mismatches{self.get_time_ns_str()}")
            return (False, errors)

    async def verify_continuous_streaming(self, total_beats, timeout_cycles=20000):
        """Verify R channel valid stays high continuously during streaming.

        Args:
            total_beats: Total beats expected
            timeout_cycles: Maximum cycles to wait

        Returns:
            (max_consecutive_valid, invalid_gaps, beats_transferred)
        """
        consecutive_valid = 0
        max_consecutive = 0
        invalid_gaps = 0
        beats_transferred = 0
        cycles = 0

        while beats_transferred < total_beats and cycles < timeout_cycles:
            await RisingEdge(self.clk)
            cycles += 1

            r_valid = int(self.dut.m_axi_rvalid.value)
            r_ready = int(self.dut.m_axi_rready.value)

            if r_valid:
                consecutive_valid += 1
                if r_ready:
                    beats_transferred += 1
            else:
                # Valid dropped - record gap if we were streaming
                if consecutive_valid > 0:
                    max_consecutive = max(max_consecutive, consecutive_valid)
                    # Gap only counts if we haven't finished yet
                    if beats_transferred < total_beats:
                        invalid_gaps += 1
                    consecutive_valid = 0

        # Final consecutive count
        if consecutive_valid > 0:
            max_consecutive = max(max_consecutive, consecutive_valid)

        return (max_consecutive, invalid_gaps, beats_transferred)

    async def measure_bandwidth_utilization(self, total_beats, timeout_cycles=20000):
        """Measure actual bandwidth vs theoretical maximum.

        Args:
            total_beats: Total beats to transfer
            timeout_cycles: Maximum cycles to wait

        Returns:
            (actual_cycles, bandwidth_utilization_percent, beats_transferred)
        """
        # Wait for first R beat
        start_cycle = 0
        beats_transferred = 0
        cycles = 0

        while cycles < timeout_cycles:
            await RisingEdge(self.clk)
            cycles += 1

            r_valid = int(self.dut.m_axi_rvalid.value)
            r_ready = int(self.dut.m_axi_rready.value)

            if r_valid and r_ready:
                if start_cycle == 0:
                    start_cycle = cycles
                beats_transferred += 1

                if beats_transferred >= total_beats:
                    break

        actual_cycles = cycles - start_cycle + 1 if start_cycle > 0 else cycles
        theoretical_cycles = total_beats  # Perfect: 1 beat/cycle

        bandwidth_utilization = (theoretical_cycles / actual_cycles * 100) if actual_cycles > 0 else 0

        return (actual_cycles, bandwidth_utilization, beats_transferred)

    async def measure_burst_to_burst_latency(self, channel_id, src_addr, burst_len, num_bursts):
        """Measure cycles between consecutive bursts.

        Args:
            channel_id: Channel ID
            src_addr: Starting source address
            burst_len: Burst length
            num_bursts: Number of bursts to measure

        Returns:
            (gaps_list, avg_gap, max_gap)
        """
        burst_end_cycles = []
        burst_start_cycles = []

        for burst in range(num_bursts):
            addr = src_addr + (burst * burst_len * (self.data_width // 8))

            # Populate memory for this burst
            await self.populate_memory(addr, burst_len, pattern='increment')

            # Issue request
            await self.issue_read_request(channel_id, addr, burst_len, burst_len)

            # Track when first R data appears
            while True:
                await RisingEdge(self.clk)
                if int(self.dut.m_axi_rvalid.value):
                    burst_start_cycles.append(len(burst_start_cycles) + len(burst_end_cycles))
                    break

            # Track when burst completes
            while True:
                await RisingEdge(self.clk)
                if int(self.dut.datard_done_strobe.value):
                    burst_end_cycles.append(len(burst_start_cycles) + len(burst_end_cycles))
                    break

        # Calculate inter-burst gaps
        gaps = []
        for i in range(1, num_bursts):
            gap = burst_start_cycles[i] - burst_end_cycles[i-1]
            gaps.append(gap)

        avg_gap = sum(gaps) / len(gaps) if gaps else 0
        max_gap = max(gaps) if gaps else 0

        return (gaps, avg_gap, max_gap)

    async def run_streaming_test(self, channel_id, src_addr, total_beats, burst_len,
                                check_stalls=True):
        """Run streaming performance test.

        Args:
            channel_id: Channel ID
            src_addr: Source address
            total_beats: Total beats to transfer
            burst_len: Burst length
            check_stalls: Check for AXI stalls

        Returns:
            (success, total_cycles, stall_cycles)
        """
        # Populate source memory
        await self.populate_memory(src_addr, total_beats, pattern='increment')

        # Issue request
        await self.issue_read_request(channel_id, src_addr, total_beats, burst_len)

        # Monitor streaming performance
        start_cycle = 0
        stall_cycles = 0
        ar_active = False
        r_active = False

        cycles = 0
        while cycles < 10000:
            await RisingEdge(self.clk)
            cycles += 1

            # Track AXI activity
            ar_valid = int(self.dut.m_axi_arvalid.value)
            ar_ready = int(self.dut.m_axi_arready.value)
            r_valid = int(self.dut.m_axi_rvalid.value)
            r_ready = int(self.dut.m_axi_rready.value)

            if ar_valid:
                ar_active = True
                if start_cycle == 0:
                    start_cycle = cycles
                if ar_ready == 0:
                    stall_cycles += 1

            if r_valid:
                r_active = True
                if r_ready == 0:
                    stall_cycles += 1

            # Check for completion
            if self.dut.datard_done_strobe.value == 1:
                total_cycles = cycles - start_cycle
                success = (int(self.dut.datard_error.value) == 0)

                if check_stalls:
                    # Streaming should have minimal stalls
                    stall_ratio = stall_cycles / total_cycles if total_cycles > 0 else 0
                    print(f"Streaming test: {total_cycles} cycles, "
                        f"{stall_cycles} stalls ({stall_ratio*100:.1f}%)")

                return (success, total_cycles, stall_cycles)

        # Timeout
        return (False, cycles, stall_cycles)

    # =========================================================================
    # Auto-drain methods for varying_lengths test
    # =========================================================================

    async def auto_drain_sram_monitor(self):
        """Background task that automatically drains SRAM whenever any channel has valid data.

        Monitors axi_wr_sram_valid[NC-1:0] and drains immediately when any bit asserts.
        Saves (channel_id, data, time_ns) tuples for later verification.

        NOTE: Caller must initialize self.drained_data=[] and self.drain_active=True before calling.
        """
        # Data structures initialized by caller
        drain_count = 0
        self.log.info(f"Auto-drain monitor STARTED{self.get_time_ns_str()}")

        while self.drain_active:
            await RisingEdge(self.clk)

            try:
                # Check which channels have valid data
                valid_vec = int(self.dut.axi_wr_sram_valid.value)

                if valid_vec != 0:  # Only process if at least one channel has data
                    # Find first channel with valid data
                    for ch in range(self.num_channels):
                        if (valid_vec >> ch) & 0x1:
                            # Channel has valid data - drain it
                            # Set ID and assert drain HIGH for FULL CLOCK CYCLE
                            self.dut.axi_wr_sram_id.value = ch
                            self.dut.axi_wr_sram_drain.value = 1

                            # Wait for NEXT rising edge (drain held high for full clock)
                            await RisingEdge(self.clk)

                            # Sample data on THIS rising edge
                            data = int(self.dut.axi_wr_sram_data.value)
                            time_ns = cocotb.utils.get_sim_time('ns')

                            # Clear drain AFTER sampling
                            self.dut.axi_wr_sram_drain.value = 0

                            # Save for later verification
                            self.drained_data.append((ch, data, time_ns))
                            drain_count += 1
                            if drain_count <= 5 or drain_count % 50 == 0:
                                self.log.info(f"SRAM_OUT: ch={ch} data=0x{data:064X} @ {time_ns}ns (total={drain_count})")

                            break  # Check again from the top (will check valid on NEXT rising edge)

            except Exception as e:
                self.log.error(f"Auto-drain error: {e}{self.get_time_ns_str()}")

        self.log.info(f"Auto-drain monitor STOPPED (drained {drain_count} total beats){self.get_time_ns_str()}")

    def stop_auto_drain(self):
        """Stop the auto-drain background task."""
        self.drain_active = False

    def get_drained_data_for_channel(self, channel_id):
        """Get all drained data for a specific channel in order.

        Args:
            channel_id: Channel to get data for

        Returns:
            List of data values (in order received)
        """
        return [data for ch, data, time_ns in self.drained_data if ch == channel_id]
