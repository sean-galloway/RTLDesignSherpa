"""
Single-Channel Scheduler BFM for STREAM datapath testing.

Purpose: Drive one channel's scheduler interface signals (sched_rd_valid[i], etc.)
         Can be instantiated N times for multi-channel testing.

Author: RTL Design Sherpa
Created: 2025-10-29
"""

import cocotb
from cocotb.triggers import RisingEdge
from cocotb.log import SimLog


class SchedulerChannelBFM:
    """
    Single-channel scheduler BFM - drives ONE channel's signals.

    Instantiate N of these for N-channel testing.
    """

    def __init__(self, dut, channel_id, num_channels, clk, rst_n, data_width=512, prefix='sched_rd', log=None):
        """
        Initialize single-channel scheduler BFM.

        Args:
            dut: DUT instance
            channel_id: This channel's ID (0 to num_channels-1)
            num_channels: Total number of channels (for signal width)
            clk: Clock signal
            rst_n: Reset signal (active-low)
            data_width: Data width in bits (for address increment calculation)
            prefix: Signal prefix ('sched_rd' or 'sched_wr')
            log: Logger instance
        """
        self.dut = dut
        self.channel_id = channel_id
        self.num_channels = num_channels
        self.clk = clk
        self.rst_n = rst_n
        self.data_width = data_width
        self.bytes_per_beat = data_width // 8
        self.prefix = prefix
        self.log = log if log else SimLog(f"cocotb.{self.__class__.__name__}.ch{channel_id}")

        # Get packed array signal references
        self.valid_array = getattr(dut, f"{prefix}_valid")
        self.ready_array = getattr(dut, f"{prefix}_ready")
        self.addr_array = getattr(dut, f"{prefix}_addr")
        self.beats_array = getattr(dut, f"{prefix}_beats")
        self.burst_len_array = getattr(dut, f"{prefix}_burst_len")

        # Channel state
        self.active = False
        self.current_addr = 0
        self.beats_remaining = 0
        self.burst_len = 16
        self.total_beats = 0

    def _set_channel_valid(self, value):
        """Set this channel's valid bit in the packed array."""
        current = int(self.valid_array.value)
        if value:
            current |= (1 << self.channel_id)
        else:
            current &= ~(1 << self.channel_id)
        self.valid_array.value = current

    def _get_channel_ready(self):
        """Get this channel's ready bit from the packed array."""
        current = int(self.ready_array.value)
        return (current >> self.channel_id) & 0x1

    def _set_channel_addr(self, addr):
        """Set this channel's address in the packed array."""
        # For packed arrays like [NC-1:0][AW-1:0], we need to set bits
        # [channel_id * AW + AW - 1 : channel_id * AW]
        addr_width = 64  # Default, could be parameter
        shift = self.channel_id * addr_width
        mask = (1 << addr_width) - 1

        current = int(self.addr_array.value)
        current &= ~(mask << shift)  # Clear this channel's bits
        current |= ((addr & mask) << shift)  # Set new value
        self.addr_array.value = current

    def _set_channel_beats(self, beats):
        """Set this channel's beats_remaining in the packed array."""
        beats_width = 32
        shift = self.channel_id * beats_width
        mask = (1 << beats_width) - 1

        current = int(self.beats_array.value)
        current &= ~(mask << shift)
        current |= ((beats & mask) << shift)
        self.beats_array.value = current

    def _set_channel_burst_len(self, burst_len):
        """Set this channel's burst_len in the packed array."""
        burst_len_width = 8
        shift = self.channel_id * burst_len_width
        mask = (1 << burst_len_width) - 1

        current = int(self.burst_len_array.value)
        current &= ~(mask << shift)
        current |= ((burst_len & mask) << shift)
        self.burst_len_array.value = current

    async def issue_request(self, addr, beats, burst_len):
        """
        Issue a read request on this channel.

        Args:
            addr: Starting address
            beats: Total beats to read
            burst_len: Burst length per AXI transaction
        """
        self.active = True
        self.current_addr = addr
        self.beats_remaining = beats
        self.total_beats = beats
        self.burst_len = burst_len

        self.log.info(f"Channel {self.channel_id}: Issue request - "
                     f"addr=0x{addr:X}, beats={beats}, burst_len={burst_len}")

        # Drive signals
        self._set_channel_valid(1)
        self._set_channel_addr(addr)
        self._set_channel_beats(beats)
        self._set_channel_burst_len(burst_len)

    async def wait_for_ready(self, timeout_cycles=1000):
        """
        Wait for this channel's ready signal.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            bool: True if ready asserted, False on timeout
        """
        for _ in range(timeout_cycles):
            await RisingEdge(self.clk)
            if self._get_channel_ready():
                self.log.debug(f"Channel {self.channel_id}: Ready asserted")
                return True

        self.log.error(f"Channel {self.channel_id}: Timeout waiting for ready")
        return False

    async def single_transaction(self, addr, beats, burst_len):
        """
        Issue request and wait for ready handshake.

        Args:
            addr: Starting address
            beats: Total beats to read
            burst_len: Burst length per AXI transaction

        Returns:
            bool: True if handshake succeeded
        """
        await self.issue_request(addr, beats, burst_len)
        success = await self.wait_for_ready()

        if success:
            # Clear valid after handshake
            self._set_channel_valid(0)
            self.beats_remaining -= burst_len
            self.current_addr += (burst_len * self.bytes_per_beat)

            if self.beats_remaining <= 0:
                self.active = False
                self.log.info(f"Channel {self.channel_id}: Transfer complete")

        return success

    async def continuous_transfer(self, addr, total_beats, burst_len):
        """
        Issue continuous burst requests until total_beats transferred.

        Args:
            addr: Starting address
            total_beats: Total beats to transfer
            burst_len: Burst length per transaction

        Returns:
            bool: True if all beats transferred
        """
        self.active = True
        self.current_addr = addr
        self.beats_remaining = total_beats
        self.total_beats = total_beats

        while self.beats_remaining > 0:
            # Calculate beats for this burst
            this_burst = min(burst_len, self.beats_remaining)

            # Issue request for THIS burst (don't use single_transaction - it resets state)
            self._set_channel_valid(1)
            self._set_channel_addr(self.current_addr)
            self._set_channel_beats(this_burst)  # Tell DUT how many beats THIS request wants
            self._set_channel_burst_len(this_burst)

            self.log.info(f"Channel {self.channel_id}: Issue request - "
                         f"addr=0x{self.current_addr:X}, beats={this_burst}, burst_len={this_burst}")

            # Wait for ready handshake
            success = await self.wait_for_ready(timeout_cycles=10000)  # Increased timeout for no-pipeline mode
            if not success:
                return False

            # Clear valid after handshake
            self._set_channel_valid(0)

            # Update state for next burst
            self.beats_remaining -= this_burst
            self.current_addr += (this_burst * self.bytes_per_beat)

            # In no-pipeline mode, wait for this burst to start draining before issuing next
            # Give the RTL time to process the burst and be ready for the next command
            if self.beats_remaining > 0:
                # Wait for data to start flowing to SRAM (burst cycles + margin for AXI latency)
                wait_cycles = this_burst + 20
                for _ in range(wait_cycles):
                    await RisingEdge(self.clk)

        # After all bursts issued, wait for final burst's AXI data to reach SRAM
        # This prevents testbench from starting drain before pipeline completes
        final_drain_cycles = 100  # Conservative: AXI read latency + pipeline stages
        for _ in range(final_drain_cycles):
            await RisingEdge(self.clk)

        self.active = False
        return True

    def is_complete(self):
        """Check if channel transfer is complete."""
        return not self.active or self.beats_remaining <= 0

    def get_progress(self):
        """Get transfer progress (completed, total)."""
        completed = self.total_beats - self.beats_remaining
        return (completed, self.total_beats)

    def clear(self):
        """Clear this channel's signals."""
        self._set_channel_valid(0)
        self._set_channel_addr(0)
        self._set_channel_beats(0)
        self._set_channel_burst_len(0)
        self.active = False
        self.beats_remaining = 0
