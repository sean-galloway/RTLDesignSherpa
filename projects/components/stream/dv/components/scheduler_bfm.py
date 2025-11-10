"""
Multi-Channel Scheduler BFM for STREAM datapath testing.

Purpose: Emulate scheduler behavior that continuously issues read/write requests
         while channels have active work, monitoring completions and auto-updating
         channel state (address, beats_remaining).

Author: Claude Code
Created: 2025-10-28
"""

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb.log import SimLog


class ChannelState:
    """State for a single channel."""

    def __init__(self, channel_id):
        self.channel_id = channel_id
        self.active = False
        self.start_addr = 0
        self.current_addr = 0
        self.total_beats = 0
        self.beats_remaining = 0
        self.burst_len = 16
        self.bytes_per_beat = 64  # Default for 512-bit data

    def start_transfer(self, addr, total_beats, burst_len, bytes_per_beat=64):
        """Start a new transfer on this channel."""
        self.active = True
        self.start_addr = addr
        self.current_addr = addr
        self.total_beats = total_beats
        self.beats_remaining = total_beats
        self.burst_len = burst_len
        self.bytes_per_beat = bytes_per_beat

    def update_progress(self, beats_done):
        """Update channel state after completion."""
        self.beats_remaining -= beats_done
        self.current_addr += (beats_done * self.bytes_per_beat)

        if self.beats_remaining <= 0:
            self.active = False

    def is_complete(self):
        """Check if channel transfer is complete."""
        return not self.active or self.beats_remaining <= 0


class StreamSchedulerBFM:
    """
    Multi-channel scheduler BFM.

    Manages an array of channel states and continuously drives datard_* interface
    to emulate scheduler behavior:
    - Assert datard_valid while channel has work
    - Monitor datard_done_strobe and auto-update channel state
    - Simple round-robin selection among active channels
    """

    def __init__(self, dut, clk, rst_n, num_channels=8, prefix='datard', log=None):
        """
        Initialize scheduler BFM.

        Args:
            dut: DUT instance
            clk: Clock signal
            rst_n: Reset signal (active-low)
            num_channels: Number of channels (default 8)
            prefix: Signal prefix (default 'datard' for read, 'datawr' for write)
            log: Logger instance
        """
        self.dut = dut
        self.clk = clk
        self.rst_n = rst_n
        self.num_channels = num_channels
        self.prefix = prefix
        self.log = log if log else SimLog(f"cocotb.{self.__class__.__name__}")

        # Channel state array
        self.channels = [ChannelState(i) for i in range(num_channels)]

        # Current channel being serviced (round-robin)
        self.current_channel_idx = 0

        # Get signal references
        self.valid = getattr(dut, f"{prefix}_valid")
        self.ready = getattr(dut, f"{prefix}_ready")
        self.addr = getattr(dut, f"{prefix}_addr")
        self.beats_remaining = getattr(dut, f"{prefix}_beats_remaining")
        self.burst_len = getattr(dut, f"{prefix}_burst_len")
        self.channel_id = getattr(dut, f"{prefix}_channel_id")
        self.done_strobe = getattr(dut, f"{prefix}_done_strobe")
        self.beats_done = getattr(dut, f"{prefix}_beats_done")

        # Initialize signals
        self.valid.value = 0
        self.addr.value = 0
        self.beats_remaining.value = 0
        self.burst_len.value = 0
        self.channel_id.value = 0

        # Start driver and monitor tasks
        self._driver_task = None
        self._monitor_task = None

    def start_channel(self, channel_id, addr, total_beats, burst_len=16, bytes_per_beat=64):
        """
        Start a transfer on the specified channel.

        Args:
            channel_id: Channel ID (0-7)
            addr: Starting address
            total_beats: Total beats to transfer
            burst_len: Burst length per AXI transaction
            bytes_per_beat: Bytes per beat (DATA_WIDTH / 8)
        """
        if channel_id >= self.num_channels:
            self.log.error(f"Invalid channel ID {channel_id}, max is {self.num_channels-1}")
            return

        ch = self.channels[channel_id]
        ch.start_transfer(addr, total_beats, burst_len, bytes_per_beat)
        self.log.info(f"Channel {channel_id}: Started transfer - addr=0x{addr:08X}, "
                     f"total_beats={total_beats}, burst_len={burst_len}")

    def is_channel_complete(self, channel_id):
        """Check if channel has completed its transfer."""
        return self.channels[channel_id].is_complete()

    def get_channel_progress(self, channel_id):
        """Get channel progress (completed_beats, total_beats)."""
        ch = self.channels[channel_id]
        completed = ch.total_beats - ch.beats_remaining
        return (completed, ch.total_beats)

    def _get_next_active_channel(self):
        """Round-robin selection of next active channel."""
        # Try to find next active channel starting from current index
        for offset in range(self.num_channels):
            idx = (self.current_channel_idx + offset) % self.num_channels
            if self.channels[idx].active and self.channels[idx].beats_remaining > 0:
                self.current_channel_idx = (idx + 1) % self.num_channels
                return self.channels[idx]
        return None

    async def driver_loop(self):
        """
        Driver loop: Continuously present active channels on datard_* interface.

        Emulates scheduler behavior:
        - Assert datard_valid while channel has work
        - Update to next channel on each clock when ready
        - Keep presenting same channel until ready accepts it
        """
        while True:
            await RisingEdge(self.clk)

            # Check for reset
            if int(self.rst_n.value) == 0:
                self.valid.value = 0
                continue

            # Get next active channel
            ch = self._get_next_active_channel()

            if ch is not None:
                # Drive interface with channel's current state
                self.valid.value = 1
                self.channel_id.value = ch.channel_id
                self.addr.value = ch.current_addr
                self.beats_remaining.value = ch.beats_remaining
                self.burst_len.value = ch.burst_len
            else:
                # No active channels
                self.valid.value = 0

    async def monitor_loop(self):
        """
        Monitor loop: Watch for done_strobe and update channel state.

        On each done_strobe:
        - Identify which channel completed (from channel_id signal)
        - Update channel's current_addr and beats_remaining
        - Mark channel inactive if complete
        """
        while True:
            await RisingEdge(self.clk)

            # Check for reset
            if int(self.rst_n.value) == 0:
                continue

            # Check for completion strobe
            if int(self.done_strobe.value) == 1:
                ch_id = int(self.channel_id.value)
                beats_done = int(self.beats_done.value)

                if ch_id < self.num_channels:
                    ch = self.channels[ch_id]
                    prev_remaining = ch.beats_remaining
                    ch.update_progress(beats_done)

                    self.log.info(f"Channel {ch_id}: Completed {beats_done} beats, "
                                 f"{prev_remaining} → {ch.beats_remaining} remaining")

                    if ch.is_complete():
                        self.log.info(f"Channel {ch_id}: Transfer complete!")

    def start(self):
        """Start driver and monitor tasks."""
        if self._driver_task is None:
            self._driver_task = cocotb.start_soon(self.driver_loop())
        if self._monitor_task is None:
            self._monitor_task = cocotb.start_soon(self.monitor_loop())

    def stop(self):
        """Stop driver and monitor tasks."""
        if self._driver_task is not None:
            self._driver_task.kill()
            self._driver_task = None
        if self._monitor_task is not None:
            self._monitor_task.kill()
            self._monitor_task = None
