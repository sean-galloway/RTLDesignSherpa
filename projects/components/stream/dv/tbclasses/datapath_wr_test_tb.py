"""
Testbench class for datapath_wr_test module.

Purpose: Test wrapper for write data path streaming performance validation.
        Tests TB fills SRAM → SRAM Controller → AXI Write Engine integration.

Author: sean galloway
Created: 2025-11-05
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
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveWrite
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS

# Add project-specific testbench utilities
from projects.components.stream.dv.tbclasses.descriptor_packet_builder import DescriptorPacketBuilder


class DatapathWrTestTB(TBBase):
    """Testbench for write data path streaming test wrapper."""

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
        self.log.info(f"Datapath Write Test TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}, DEBUG={self.DEBUG}{self.get_time_ns_str()}")
        self.log.info(f"NOSTRESS_MODE={'ENABLED' if self.NOSTRESS_MODE else 'DISABLED'}{self.get_time_ns_str()}")
        self.log.info(f"DATA_WIDTH={self.data_width}, NUM_CHANNELS={self.num_channels}, SRAM_DEPTH={self.sram_depth}{self.get_time_ns_str()}")

        # Memory model for AXI slave (represents system memory with 64-byte cache lines)
        self.memory_model = MemoryModel(num_lines=262144, bytes_per_line=64)

        # AXI slave (simulates memory on write side)
        self.axi_slave = None  # Created in setup

        # Descriptor packet builder
        self.desc_builder = DescriptorPacketBuilder()

        # Cycle counter for performance measurement
        self.cycle_count = 0

        # Write timestamp tracking (address -> timestamp_ns)
        self.write_timestamps = {}
        self.w_monitor_active = False
        self.aw_addresses = []  # Track AW addresses to correlate with W data

    async def setup_clocks_and_reset(self, xfer_beats=16):
        """Complete initialization - clocks and reset.

        Args:
            xfer_beats: Transfer size in beats (default 16, range 1-255)
        """
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize configuration
        self.dut.cfg_axi_wr_xfer_beats.value = xfer_beats
        self.xfer_beats = xfer_beats  # Store for test use
        self.log.info(f"Configured AXI write transfer size: {xfer_beats} beats{self.get_time_ns_str()}")

        # Initialize descriptor interface signals (all channels)
        for ch_id in range(self.num_channels):
            desc_valid_signal = getattr(self.dut, f'descriptor_{ch_id}_valid')
            desc_packet_signal = getattr(self.dut, f'descriptor_{ch_id}_packet')
            desc_error_signal = getattr(self.dut, f'descriptor_{ch_id}_error')

            desc_valid_signal.value = 0
            desc_packet_signal.value = 0
            desc_error_signal.value = 0

        # Initialize SRAM fill interface (transaction-ID based)
        # These signals are arrays but cocotb treats them as packed
        for ch_id in range(self.num_channels):
            # axi_rd_sram_valid is [NC-1:0] packed array
            pass  # Will set per transaction

        self.dut.axi_rd_sram_id.value = 0
        self.dut.axi_rd_sram_data.value = 0

        # Create AXI slave with nostress-aware response delay
        # NOSTRESS mode: zero delays (no BFM-induced bubbles)
        # NORMAL mode: 1-cycle delay for realistic timing
        response_delay = 0 if self.NOSTRESS_MODE else 1
        self.log.info(f"AXI slave response_delay = {response_delay} cycles (NOSTRESS={'ON' if self.NOSTRESS_MODE else 'OFF'}){self.get_time_ns_str()}")

        self.axi_slave = AXI4SlaveWrite(
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

    async def assert_reset(self):
        """Assert reset signal."""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal."""
        self.rst_n.value = 1

    def set_axi_timing_profile(self, profile_name):
        """
        Configure AXI channel randomizers using canonical timing profiles.

        Applies timing configuration to AW, W, and B channels of the AXI slave.

        Args:
            profile_name: Timing profile from AXI_RANDOMIZER_CONFIGS
                        ('backtoback', 'fixed', 'fast', 'constrained', etc.)

        Channel Configuration:
            - AW channel (GAXISlave): Controls awready signal timing
            Uses 'slave' config for ready_delay
            - W channel (GAXISlave): Controls wready signal timing
            Uses 'slave' config for ready_delay
            - B channel (GAXIMaster): Controls bvalid signal timing
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

        # AW channel: GAXISlave drives awready
        # Uses 'slave' config to control ready_delay
        aw_randomizer = FlexRandomizer(config['slave'])
        self.axi_slave.aw_channel.randomizer = aw_randomizer

        # W channel: GAXISlave drives wready
        # Uses 'slave' config to control ready_delay
        w_randomizer = FlexRandomizer(config['slave'])
        self.axi_slave.w_channel.randomizer = w_randomizer

        # B channel: GAXIMaster drives bvalid
        # Uses 'master' config to control valid_delay
        b_randomizer = FlexRandomizer(config['master'])
        self.axi_slave.b_channel.randomizer = b_randomizer

        # Log configuration details
        mode_str = "NOSTRESS (zero delays)" if profile_name == 'backtoback' else "NORMAL (with delays)"
        self.log.info(f"AXI timing profile: '{profile_name}' - {mode_str}{self.get_time_ns_str()}")
        self.log.info(f"  AW channel (slave/ready): {config['slave']}{self.get_time_ns_str()}")
        self.log.info(f"  W channel (slave/ready): {config['slave']}{self.get_time_ns_str()}")
        self.log.info(f"  B channel (master/valid): {config['master']}{self.get_time_ns_str()}")

    async def _cycle_counter(self):
        """Background task to increment cycle counter on every clock edge."""
        while True:
            await RisingEdge(self.clk)
            self.cycle_count += 1

    def _increment_data_pattern(self, bytes_per_beat, addr):
        """Generate increment data pattern matching read test."""
        data = bytearray()
        beat = addr // bytes_per_beat
        burst_pos = (beat % 8) + 1

        for byte_idx in range(bytes_per_beat):
            if byte_idx == 0:  # Byte 0 (LSB) - Burst position
                byte_val = burst_pos  # 0x01-0x08
            elif byte_idx == 1:  # Byte 1 - Address low byte
                byte_val = addr & 0xFF
            elif byte_idx == 2:  # Byte 2 - Address mid byte
                byte_val = (addr >> 8) & 0xFF
            elif byte_idx == 3:  # Byte 3 - Address high byte
                byte_val = (addr >> 16) & 0xFF
            else:
                byte_val = 0x00
            data.append(byte_val)

        return data

    async def fill_sram(self, channel_id, start_addr, num_beats, pattern='increment'):
        """Fill SRAM channel with test data.

        Args:
            channel_id: Channel to fill (0-7)
            start_addr: Virtual address for pattern generation
            num_beats: Number of beats to fill
            pattern: 'increment', 'random', or 'fixed'
        """
        import cocotb.utils
        bytes_per_beat = self.data_width // 8
        data_width_hex = (self.data_width + 3) // 4  # Number of hex digits for data width

        self.log.info(f"Channel {channel_id}: Filling SRAM with {num_beats} beats{self.get_time_ns_str()}")

        for beat in range(num_beats):
            addr = start_addr + (beat * bytes_per_beat)

            if pattern == 'increment':
                data_bytes = self._increment_data_pattern(bytes_per_beat, addr)
                data = int.from_bytes(data_bytes, byteorder='little')
            elif pattern == 'fixed':
                data = int('AA' * bytes_per_beat, 16)
            else:
                # Random pattern
                import random
                data = random.randint(0, (1 << self.data_width) - 1)

            # Write to SRAM via transaction-ID interface
            # Single valid signal + ID selects channel
            self.dut.axi_rd_sram_valid.value = 1
            self.dut.axi_rd_sram_id.value = channel_id
            self.dut.axi_rd_sram_data.value = data

            await RisingEdge(self.clk)

            # Get timestamp after clock edge
            timestamp_ns = cocotb.utils.get_sim_time(units='ns')

            # Check if ready (handshake successful)
            ready = int(self.dut.axi_rd_sram_ready.value)
            if ready == 1:
                # Log SRAM write with timestamp and data (following GLOBAL_REQUIREMENTS.md Section 3.4)
                self.log.info(f"@ {timestamp_ns:.1f}ns: SRAM write beat {beat+1}/{num_beats} ch={channel_id} @ 0x{addr:X}: data=0x{data:0{data_width_hex}X}")
            else:
                self.log.warning(f"@ {timestamp_ns:.1f}ns: Channel {channel_id}: SRAM not ready at beat {beat}")

        # Clear valid
        self.dut.axi_rd_sram_valid.value = 0
        self.log.info(f"Channel {channel_id}: SRAM filled with {num_beats} beats{self.get_time_ns_str()}")

    async def issue_descriptor_packet(self, channel_id, dst_addr, length, last=True):
        """Issue a single descriptor packet to a channel.

        Args:
            channel_id: Channel ID (0-7)
            dst_addr: Destination address (must be aligned)
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
            src_addr=0,  # Unused in write-only test
            dst_addr=dst_addr,
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
                            f"dst_addr=0x{dst_addr:016X}, length={length} beats")
                return True

        # Timeout
        desc_valid_signal.value = 0
        self.log.error(f"Channel {channel_id}: Descriptor timeout after {timeout_cycles} cycles{self.get_time_ns_str()}")
        return False

    async def wait_for_idle(self, timeout_cycles=10000):
        """Wait for all channels to become idle (all write operations complete).

        This waits for sched_idle to go high, which indicates:
        1. All AW transactions issued
        2. All W data sent
        3. All B responses received

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            bool: True if all channels idle, False on timeout
        """
        start_cycle = self.cycle_count
        expected_idle_mask = (1 << self.num_channels) - 1  # All 1's

        self.log.info(f"Waiting for all channels to become idle (sched_idle=0x{expected_idle_mask:X}){self.get_time_ns_str()}")

        while (self.cycle_count - start_cycle) < timeout_cycles:
            await RisingEdge(self.clk)

            # Check if all channels idle
            idle_val = int(self.dut.sched_idle.value)
            if idle_val == expected_idle_mask:
                elapsed = self.cycle_count - start_cycle
                self.log.info(f"✓ All channels idle (sched_idle=0x{idle_val:X}) after {elapsed} cycles{self.get_time_ns_str()}")
                return True

        # Timeout
        idle_val = int(self.dut.sched_idle.value)
        elapsed = self.cycle_count - start_cycle
        self.log.error(f"✗ Timeout waiting for idle: sched_idle=0x{idle_val:X} (expected 0x{expected_idle_mask:X}) "
                      f"after {elapsed} cycles{self.get_time_ns_str()}")
        return False

    async def axi_aw_monitor(self):
        """Background monitor for AXI AW channel transactions.

        Captures AW addresses and burst lengths for correlation with W channel.
        """
        bytes_per_beat = self.data_width // 8

        self.log.info(f"Starting background AXI AW channel monitor{self.get_time_ns_str()}")

        while self.w_monitor_active:
            await RisingEdge(self.clk)

            # Check for AW channel handshake
            awvalid = int(self.dut.m_axi_awvalid.value)
            awready = int(self.dut.m_axi_awready.value)

            if awvalid and awready:
                # AW channel transaction
                base_addr = int(self.dut.m_axi_awaddr.value)
                burst_len = int(self.dut.m_axi_awlen.value) + 1  # awlen+1 = number of beats

                self.aw_addresses.append((base_addr, burst_len))

                self.log.debug(f"AW @ 0x{base_addr:X}, len={burst_len} beats{self.get_time_ns_str()}")

        self.log.info(f"Stopped AXI AW channel monitor. Captured {len(self.aw_addresses)} addresses{self.get_time_ns_str()}")

    async def axi_w_monitor(self):
        """Background monitor for AXI W channel transactions.

        Monitors m_axi_wvalid & m_axi_wready handshakes and captures timestamps.
        Correlates with AW addresses tracked separately.
        """
        import cocotb.utils

        bytes_per_beat = self.data_width // 8
        aw_index = 0  # Index into aw_addresses list
        w_beat_in_burst = 0  # Beat counter within current burst
        current_burst_len = 0
        current_base_addr = 0

        self.log.info(f"Starting background AXI W channel monitor{self.get_time_ns_str()}")

        while self.w_monitor_active:
            await RisingEdge(self.clk)

            # Check for W channel handshake
            wvalid = int(self.dut.m_axi_wvalid.value)
            wready = int(self.dut.m_axi_wready.value)

            if wvalid and wready:
                # W channel beat transferred
                timestamp_ns = cocotb.utils.get_sim_time(units='ns')

                # Get write data value
                wdata = int(self.dut.m_axi_wdata.value)

                # Get corresponding address from AW tracking
                if w_beat_in_burst == 0 and aw_index < len(self.aw_addresses):
                    # Start of new burst - get address info
                    current_base_addr, current_burst_len = self.aw_addresses[aw_index]
                    aw_index += 1

                if current_burst_len > 0:
                    # Calculate address for this beat
                    addr = current_base_addr + (w_beat_in_burst * bytes_per_beat)
                    self.write_timestamps[addr] = timestamp_ns

                    # INFO-level logging with timestamp and data (following GLOBAL_REQUIREMENTS.md Section 3.4)
                    data_width_hex = (self.data_width + 3) // 4  # Number of hex digits for data width
                    self.log.info(f"@ {timestamp_ns:.1f}ns: W beat {w_beat_in_burst+1}/{current_burst_len} @ 0x{addr:X}: data=0x{wdata:0{data_width_hex}X}")

                    # Update beat counter
                    w_beat_in_burst += 1
                    if w_beat_in_burst >= current_burst_len:
                        # End of burst
                        w_beat_in_burst = 0
                        current_burst_len = 0

        self.log.info(f"Stopped AXI W channel monitor. Captured {len(self.write_timestamps)} timestamps{self.get_time_ns_str()}")

    async def wait_for_completion(self, channel_id, expected_aw_transactions, timeout_cycles=10000):
        """Wait for channel write transfer to complete.

        Args:
            channel_id: Channel ID to wait for
            expected_aw_transactions: Expected number of AW transactions
            timeout_cycles: Maximum cycles to wait

        Returns:
            (success, actual_transactions)
        """
        # Start background W channel monitors for timestamp capture
        self.w_monitor_active = True
        self.write_timestamps.clear()
        self.aw_addresses.clear()

        aw_monitor_task = cocotb.start_soon(self.axi_aw_monitor())
        w_monitor_task = cocotb.start_soon(self.axi_w_monitor())

        # Wait for AXI transactions to complete
        # Monitor dbg_aw_transactions and dbg_w_beats
        start_cycle = self.cycle_count

        while (self.cycle_count - start_cycle) < timeout_cycles:
            await RisingEdge(self.clk)

            aw_count = int(self.dut.dbg_aw_transactions.value)
            if aw_count >= expected_aw_transactions:
                self.log.info(f"Channel {channel_id}: Completed {aw_count} AW transactions{self.get_time_ns_str()}")

                # CRITICAL: Wait for all channels to be idle (B responses received)
                idle_success = await self.wait_for_idle(timeout_cycles=5000)

                # Stop background monitors
                self.w_monitor_active = False
                await self.wait_clocks(self.clk_name, 5)  # Allow monitors to stop

                self.log.info(f"Captured {len(self.write_timestamps)} write timestamps from W channel monitor{self.get_time_ns_str()}")

                return (idle_success, aw_count)

        # Timeout - stop monitors
        self.w_monitor_active = False
        await self.wait_clocks(self.clk_name, 5)

        aw_count = int(self.dut.dbg_aw_transactions.value)
        self.log.error(f"Channel {channel_id}: Timeout - got {aw_count}/{expected_aw_transactions} AW transactions{self.get_time_ns_str()}")
        return (False, aw_count)

    async def validate_completion_signal_sticky(self, channel_id=0, duration_cycles=1000):
        """
        Validate that axi_wr_all_complete signal stays HIGH once asserted.

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
                complete_reg = int(self.dut.axi_wr_all_complete.value)
                complete_ch = (complete_reg >> channel_id) & 0x1
            except:
                self.log.warning(f"Could not read axi_wr_all_complete{self.get_time_ns_str()}")
                continue

            # Detect changes
            if complete_ch != prev_complete:
                completion_changes.append({
                    'cycle': cycle,
                    'value': complete_ch,
                    'transition': f"{prev_complete} -> {complete_ch}"
                })
                self.log.info(f"Channel {channel_id} axi_wr_all_complete: {prev_complete} -> {complete_ch} @ cycle {cycle}{self.get_time_ns_str()}")

            prev_complete = complete_ch

        # Validate: Once HIGH, must stay HIGH (sticky behavior)
        went_high = False
        for change in completion_changes:
            if change['value'] == 1:
                went_high = True
            elif went_high and change['value'] == 0:
                # BUG! Signal went LOW after going HIGH
                self.log.error(f"❌ COMPLETION SIGNAL BUG DETECTED: Channel {channel_id} axi_wr_all_complete went LOW after going HIGH!{self.get_time_ns_str()}")
                self.log.error(f"   Changes: {completion_changes}{self.get_time_ns_str()}")
                return False

        if went_high:
            self.log.info(f"✅ Channel {channel_id} axi_wr_all_complete is STICKY (stayed HIGH after going HIGH){self.get_time_ns_str()}")
        else:
            self.log.debug(f"Channel {channel_id} axi_wr_all_complete never went HIGH (no transactions?){self.get_time_ns_str()}")

        return True

    async def verify_memory(self, start_addr, num_beats):
        """Verify data in memory model matches expected pattern.

        Args:
            start_addr: Starting address
            num_beats: Number of beats to verify

        Returns:
            (bool, int): (success, error_count)
        """
        bytes_per_beat = self.data_width // 8
        errors = 0

        self.log.info(f"Verifying memory: {num_beats} beats from 0x{start_addr:X}{self.get_time_ns_str()}")

        for beat in range(num_beats):
            addr = start_addr + (beat * bytes_per_beat)

            # Generate expected data
            expected_data_bytes = self._increment_data_pattern(bytes_per_beat, addr)
            expected_data = int.from_bytes(expected_data_bytes, byteorder='little')

            # Read from memory model
            actual_data_bytes = self.memory_model.read(addr, bytes_per_beat)
            actual_data = int.from_bytes(actual_data_bytes, byteorder='little')

            # Get write timestamp for this address (if available)
            write_time_ns = self.write_timestamps.get(addr, None)
            time_str = f" @ {write_time_ns:.1f}ns" if write_time_ns is not None else self.get_time_ns_str()

            # Verify
            if actual_data != expected_data:
                self.log.error(f"Beat {beat} @ 0x{addr:X}: MISMATCH{time_str}")
                self.log.error(f"  Expected: 0x{expected_data:064X}{time_str}")
                self.log.error(f"  Got:      0x{actual_data:064X}{time_str}")
                errors += 1
            else:
                self.log.debug(f"Beat {beat} @ 0x{addr:X}: ✓ Match{time_str}")

        if errors == 0:
            self.log.info(f"✓ Memory verification: All {num_beats} beats match{self.get_time_ns_str()}")
            return (True, 0)
        else:
            self.log.error(f"✗ Memory verification: {errors}/{num_beats} mismatches{self.get_time_ns_str()}")
            return (False, errors)
