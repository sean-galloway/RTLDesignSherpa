"""
Testbench for axi_data_dnsize module
Tests wide→narrow splitter with various configurations
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random


class AXIDataDnsizeTB:
    """
    Testbench class for axi_data_dnsize module

    Provides methods to drive wide input and monitor narrow output.
    Supports both broadcast and slice sideband modes.
    Supports optional burst tracking for LAST generation.
    """

    def __init__(self, dut):
        self.dut = dut
        self.clk = dut.aclk
        self.rst_n = dut.aresetn

        # Extract parameters from DUT
        try:
            self.wide_width = int(dut.WIDE_WIDTH.value)
            self.narrow_width = int(dut.NARROW_WIDTH.value)
            self.wide_sb_width = int(dut.WIDE_SB_WIDTH.value) if hasattr(dut, 'WIDE_SB_WIDTH') else 0
            self.narrow_sb_width = int(dut.NARROW_SB_WIDTH.value) if hasattr(dut, 'NARROW_SB_WIDTH') else 0
            self.sb_broadcast = bool(int(dut.SB_BROADCAST.value)) if hasattr(dut, 'SB_BROADCAST') else True
            self.track_bursts = bool(int(dut.TRACK_BURSTS.value)) if hasattr(dut, 'TRACK_BURSTS') else False
            self.width_ratio = self.wide_width // self.narrow_width
        except:
            # Fallback if parameters not accessible
            self.wide_width = 128
            self.narrow_width = 32
            self.wide_sb_width = 2
            self.narrow_sb_width = 2
            self.sb_broadcast = True
            self.track_bursts = False
            self.width_ratio = 4

        # Statistics
        self.wide_beats_sent = 0
        self.narrow_beats_received = 0

    async def setup_clocks_and_reset(self, period_ns=10):
        """Initialize clocks and perform reset"""
        # Start clock
        cocotb.start_soon(Clock(self.clk, period_ns, units='ns').start())

        # Initialize signals
        self.dut.wide_valid.value = 0
        self.dut.wide_data.value = 0
        self.dut.wide_sideband.value = 0
        self.dut.wide_last.value = 0
        self.dut.narrow_ready.value = 0

        if self.track_bursts:
            self.dut.burst_len.value = 0
            self.dut.burst_start.value = 0

        # Assert reset
        await self.assert_reset()
        await Timer(period_ns * 5, units='ns')

        # Deassert reset
        await self.deassert_reset()
        await Timer(period_ns * 2, units='ns')

    async def assert_reset(self):
        """Assert reset signal"""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.rst_n.value = 1

    async def wait_clocks(self, n=1):
        """Wait for n clock cycles"""
        for _ in range(n):
            await RisingEdge(self.clk)

    async def start_burst(self, burst_len):
        """
        Start a new burst (only if TRACK_BURSTS=1)

        Args:
            burst_len: Burst length (encoded as beats-1)
        """
        if self.track_bursts:
            self.dut.burst_len.value = burst_len
            self.dut.burst_start.value = 1
            await RisingEdge(self.clk)
            self.dut.burst_start.value = 0

    async def send_wide_beat(self, data, sideband=0, last=False):
        """
        Send a wide beat on the input

        Args:
            data: Data value
            sideband: Sideband value (WSTRB or RRESP)
            last: Assert wide_last
        """
        self.dut.wide_valid.value = 1
        self.dut.wide_data.value = data
        if self.wide_sb_width > 0:
            self.dut.wide_sideband.value = sideband
        self.dut.wide_last.value = 1 if last else 0

        # Wait for handshake
        await RisingEdge(self.clk)
        while self.dut.wide_ready.value == 0:
            await RisingEdge(self.clk)

        # Deassert after accepted
        self.dut.wide_valid.value = 0
        self.dut.wide_last.value = 0
        self.wide_beats_sent += 1

    async def receive_narrow_beat(self, timeout_cycles=100):
        """
        Receive a narrow beat from output

        Returns:
            (data, sideband, last) tuple
        """
        # Assert ready
        self.dut.narrow_ready.value = 1

        # Wait for valid
        cycles = 0
        await RisingEdge(self.clk)
        while self.dut.narrow_valid.value == 0:
            await RisingEdge(self.clk)
            cycles += 1
            if cycles > timeout_cycles:
                raise TimeoutError(f"Timeout waiting for narrow_valid after {timeout_cycles} cycles")

        # Capture data
        data = int(self.dut.narrow_data.value)
        sideband = int(self.dut.narrow_sideband.value) if self.narrow_sb_width > 0 else 0
        last = bool(self.dut.narrow_last.value)

        # Deassert ready immediately after handshake
        self.dut.narrow_ready.value = 0
        self.narrow_beats_received += 1

        return (data, sideband, last)

    async def test_basic_splitting(self, num_transactions=10):
        """
        Test basic splitting: send 1 wide beat,
        expect WIDTH_RATIO narrow beats with correct data slices
        """
        for txn in range(num_transactions):
            # Generate wide beat data
            wide_data = random.randint(0, (1 << self.wide_width) - 1)
            wide_sideband = random.randint(0, (1 << self.wide_sb_width) - 1) if self.wide_sb_width > 0 else 0

            # Send wide beat
            await self.send_wide_beat(wide_data, wide_sideband, last=False)

            # Receive narrow beats
            for i in range(self.width_ratio):
                narrow_data, narrow_sideband, narrow_last = await self.receive_narrow_beat()

                # Extract expected narrow data slice
                expected_data = (wide_data >> (i * self.narrow_width)) & ((1 << self.narrow_width) - 1)

                assert narrow_data == expected_data, \
                    f"Beat {i}: Data mismatch - expected 0x{expected_data:x}, got 0x{narrow_data:x}"

                # Verify sideband
                if self.narrow_sb_width > 0:
                    if self.sb_broadcast:
                        # Broadcast mode: all narrow beats get same sideband
                        expected_sb = wide_sideband
                    else:
                        # Slice mode: extract appropriate slice
                        expected_sb = (wide_sideband >> (i * self.narrow_sb_width)) & ((1 << self.narrow_sb_width) - 1)

                    assert narrow_sideband == expected_sb, \
                        f"Beat {i}: Sideband mismatch - expected 0x{expected_sb:x}, got 0x{narrow_sideband:x}"

    async def test_last_propagation(self, num_transactions=5):
        """
        Test that wide_last propagates to last narrow beat
        (only for simple mode, not burst tracking mode)
        """
        if self.track_bursts:
            # Skip this test in burst tracking mode
            return

        for txn in range(num_transactions):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)

            # Send wide beat with last=1
            await self.send_wide_beat(wide_data, sideband=0, last=True)

            # Receive narrow beats
            for i in range(self.width_ratio):
                narrow_data, narrow_sideband, narrow_last = await self.receive_narrow_beat()

                # Only last narrow beat should have narrow_last=1
                if i == self.width_ratio - 1:
                    assert narrow_last == True, f"Expected narrow_last=1 on final beat"
                else:
                    assert narrow_last == False, f"Unexpected narrow_last=1 on beat {i}"

    async def test_burst_tracking(self, num_bursts=10):
        """
        Test burst tracking mode: verify LAST on correct beat
        (only for TRACK_BURSTS=1 mode)
        """
        if not self.track_bursts:
            # Skip this test if not in burst tracking mode
            return

        for burst_idx in range(num_bursts):
            # Random burst length (1-16 narrow beats)
            total_narrow_beats = random.randint(1, 16)
            burst_len = total_narrow_beats - 1  # Encoded as (beats-1)

            # Start burst
            await self.start_burst(burst_len)

            # Calculate how many wide beats needed
            num_wide_beats = (total_narrow_beats + self.width_ratio - 1) // self.width_ratio

            # Send wide beats
            for wide_idx in range(num_wide_beats):
                wide_data = random.randint(0, (1 << self.wide_width) - 1)
                await self.send_wide_beat(wide_data, sideband=0, last=False)

            # Receive narrow beats and verify LAST on correct beat
            for narrow_idx in range(total_narrow_beats):
                narrow_data, narrow_sideband, narrow_last = await self.receive_narrow_beat()

                # Check LAST on final beat
                if narrow_idx == total_narrow_beats - 1:
                    assert narrow_last == True, \
                        f"Burst {burst_idx}: Expected narrow_last=1 on beat {narrow_idx}"
                else:
                    assert narrow_last == False, \
                        f"Burst {burst_idx}: Unexpected narrow_last=1 on beat {narrow_idx}"

    async def test_backpressure(self, num_transactions=5):
        """
        Test backpressure: delay narrow_ready randomly
        """
        for txn in range(num_transactions):
            wide_data = random.randint(0, (1 << self.wide_width) - 1)

            # Send wide beat
            await self.send_wide_beat(wide_data, sideband=0, last=False)

            # Receive narrow beats with random delays
            for i in range(self.width_ratio):
                # Random delay before asserting ready
                delay_cycles = random.randint(1, 10)
                await self.wait_clocks(delay_cycles)

                narrow_data, narrow_sideband, narrow_last = await self.receive_narrow_beat()

    async def test_continuous_streaming(self, num_wide_beats=20):
        """
        Test continuous streaming: no gaps between transactions
        """
        # Start receiver task
        received_beats = []

        async def receiver():
            self.dut.narrow_ready.value = 1
            for _ in range(num_wide_beats * self.width_ratio):
                await RisingEdge(self.clk)
                while self.dut.narrow_valid.value == 0:
                    await RisingEdge(self.clk)
                data = int(self.dut.narrow_data.value)
                received_beats.append(data)

        receiver_task = cocotb.start_soon(receiver())

        # Send wide beats continuously
        for wide_idx in range(num_wide_beats):
            wide_data = wide_idx << 4  # Unique pattern per wide beat
            self.dut.wide_valid.value = 1
            self.dut.wide_data.value = wide_data
            self.dut.wide_last.value = 0
            await RisingEdge(self.clk)
            while self.dut.wide_ready.value == 0:
                await RisingEdge(self.clk)

        self.dut.wide_valid.value = 0

        # Wait for receiver to finish
        await receiver_task

        # Verify we received all beats
        expected_narrow_beats = num_wide_beats * self.width_ratio
        assert len(received_beats) == expected_narrow_beats, \
            f"Expected {expected_narrow_beats} narrow beats, got {len(received_beats)}"
