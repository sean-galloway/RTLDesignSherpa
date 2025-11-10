"""
Performance Profiler Testbench

Testbench class for perf_profiler module validation.
Provides methods for profiling configuration, event generation,
and FIFO reading.

Location: projects/components/stream/dv/tbclasses/
Pattern: Project-area testbench (NOT in framework!)
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, Timer
import sys
import os

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
if repo_root not in sys.path:
    sys.path.insert(0, repo_root)
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from bin.CocoTBFramework.tbclasses.shared.tbbase import TBBase


class PerfProfilerTB(TBBase):
    """
    Testbench for Performance Profiler module

    Supports:
    - Timestamp mode and elapsed mode profiling
    - Multi-channel event generation
    - Two-register FIFO read interface
    - Event tracking and verification
    """

    def __init__(self, dut, **kwargs):
        """Initialize testbench"""
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        self.dut = dut
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # Profiler configuration
        self.num_channels = int(dut.NUM_CHANNELS.value) if hasattr(dut, 'NUM_CHANNELS') else 8

        # Event tracking
        self.expected_events = []
        self.actual_events = []

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset (MANDATORY METHOD)"""
        # Start clock (10ns period = 100MHz)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all inputs before reset
        self.dut.channel_idle.value = (1 << self.num_channels) - 1  # All idle
        self.dut.cfg_enable.value = 0
        self.dut.cfg_mode.value = 0
        self.dut.cfg_clear.value = 0
        self.dut.perf_fifo_rd.value = 0

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert reset signal (MANDATORY METHOD)"""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal (MANDATORY METHOD)"""
        self.rst_n.value = 1

    async def enable_profiler(self, mode=0):
        """
        Enable profiler

        Args:
            mode: 0=timestamp mode, 1=elapsed mode
        """
        self.dut.cfg_mode.value = mode
        self.dut.cfg_enable.value = 1
        await RisingEdge(self.clk)
        self.log.info(f"Profiler enabled in {'ELAPSED' if mode else 'TIMESTAMP'} mode")

    async def disable_profiler(self):
        """Disable profiler"""
        self.dut.cfg_enable.value = 0
        await RisingEdge(self.clk)
        self.log.info("Profiler disabled")

    async def clear_profiler(self):
        """Clear FIFO and counters"""
        self.dut.cfg_clear.value = 1
        await RisingEdge(self.clk)
        self.dut.cfg_clear.value = 0
        await RisingEdge(self.clk)
        self.log.info("Profiler cleared")
        self.expected_events.clear()
        self.actual_events.clear()

    async def set_channel_idle(self, channel, idle):
        """
        Set idle state for a channel

        Args:
            channel: Channel number (0-7)
            idle: True=idle, False=active
        """
        current = int(self.dut.channel_idle.value)
        if idle:
            new_val = current | (1 << channel)
        else:
            new_val = current & ~(1 << channel)
        self.dut.channel_idle.value = new_val
        await RisingEdge(self.clk)

    async def set_all_channels(self, idle_mask):
        """
        Set idle state for all channels

        Args:
            idle_mask: 8-bit mask (bit N = 1 means channel N is idle)
        """
        self.dut.channel_idle.value = idle_mask
        await RisingEdge(self.clk)

    async def channel_active_pulse(self, channel, duration_cycles):
        """
        Generate an active pulse on a channel (idle->active->idle)

        Args:
            channel: Channel number
            duration_cycles: How many cycles to stay active
        """
        # Go active (idle=0)
        await self.set_channel_idle(channel, False)
        self.log.info(f"Channel {channel}: idle -> active")

        # Stay active
        await self.wait_clocks(self.clk_name, duration_cycles)

        # Go idle (idle=1)
        await self.set_channel_idle(channel, True)
        self.log.info(f"Channel {channel}: active -> idle (duration={duration_cycles} cycles)")

    async def read_fifo_entry(self):
        """
        Read one FIFO entry via two-register interface

        Returns:
            tuple: (timestamp/elapsed, channel_id, event_type) or None if empty
        """
        if int(self.dut.perf_fifo_empty.value):
            return None

        # Read LOW register (pops FIFO, latches data)
        self.dut.perf_fifo_rd.value = 1
        await RisingEdge(self.clk)
        self.dut.perf_fifo_rd.value = 0

        # Sample both registers on next cycle
        await RisingEdge(self.clk)
        data_low = int(self.dut.perf_fifo_data_low.value)
        data_high = int(self.dut.perf_fifo_data_high.value)

        # Parse metadata
        channel_id = data_high & 0x7
        event_type = (data_high >> 3) & 1

        event = {
            'timestamp': data_low,
            'channel_id': channel_id,
            'event_type': event_type,
            'event_str': 'END' if event_type else 'START'
        }

        self.actual_events.append(event)
        self.log.info(f"Read FIFO: Ch{channel_id} {event['event_str']} @ {data_low}")

        return (data_low, channel_id, event_type)

    async def read_all_fifo_entries(self):
        """Read all entries from FIFO"""
        entries = []
        while not int(self.dut.perf_fifo_empty.value):
            entry = await self.read_fifo_entry()
            if entry:
                entries.append(entry)
        return entries

    def get_fifo_count(self):
        """Get number of entries in FIFO"""
        return int(self.dut.perf_fifo_count.value)

    def is_fifo_empty(self):
        """Check if FIFO is empty"""
        return bool(int(self.dut.perf_fifo_empty.value))

    def is_fifo_full(self):
        """Check if FIFO is full"""
        return bool(int(self.dut.perf_fifo_full.value))

    def get_timestamp_counter(self):
        """Get current timestamp counter value"""
        # Access internal signal for debugging
        try:
            return int(self.dut.r_timestamp_counter.value)
        except:
            # If can't access internal signal, estimate from time
            return 0

    async def wait_for_events(self, expected_count, timeout_cycles=1000):
        """
        Wait for FIFO to contain expected number of events

        Args:
            expected_count: Number of events to wait for
            timeout_cycles: Maximum cycles to wait

        Returns:
            bool: True if events arrived, False if timeout
        """
        for _ in range(timeout_cycles):
            count = self.get_fifo_count()
            if count >= expected_count:
                self.log.info(f"FIFO has {count} events (expected {expected_count})")
                return True
            await RisingEdge(self.clk)

        self.log.error(f"Timeout waiting for {expected_count} events (got {self.get_fifo_count()})")
        return False
