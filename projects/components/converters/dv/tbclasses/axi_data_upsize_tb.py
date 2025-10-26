"""
Testbench for axi_data_upsize module
Tests narrow→wide accumulator with various configurations
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random


class AXIDataUpsizeTB:
    """
    Testbench class for axi_data_upsize module

    Provides methods to drive narrow input and monitor wide output.
    Supports both WSTRB concatenation and RRESP OR modes.
    """

    def __init__(self, dut):
        self.dut = dut
        self.clk = dut.aclk
        self.rst_n = dut.aresetn

        # Extract parameters from DUT
        try:
            self.narrow_width = int(dut.NARROW_WIDTH.value)
            self.wide_width = int(dut.WIDE_WIDTH.value)
            self.narrow_sb_width = int(dut.NARROW_SB_WIDTH.value) if hasattr(dut, 'NARROW_SB_WIDTH') else 0
            self.wide_sb_width = int(dut.WIDE_SB_WIDTH.value) if hasattr(dut, 'WIDE_SB_WIDTH') else 0
            self.sb_or_mode = bool(int(dut.SB_OR_MODE.value)) if hasattr(dut, 'SB_OR_MODE') else False
            self.width_ratio = self.wide_width // self.narrow_width
        except:
            # Fallback if parameters not accessible
            self.narrow_width = 32
            self.wide_width = 128
            self.narrow_sb_width = 4
            self.wide_sb_width = 16
            self.sb_or_mode = False
            self.width_ratio = 4

        # Statistics
        self.narrow_beats_sent = 0
        self.wide_beats_received = 0

    async def setup_clocks_and_reset(self, period_ns=10):
        """Initialize clocks and perform reset"""
        # Start clock
        cocotb.start_soon(Clock(self.clk, period_ns, units='ns').start())

        # Initialize signals
        self.dut.narrow_valid.value = 0
        self.dut.narrow_data.value = 0
        self.dut.narrow_sideband.value = 0
        self.dut.narrow_last.value = 0
        self.dut.wide_ready.value = 0

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

    async def send_narrow_beat(self, data, sideband=0, last=False):
        """
        Send a narrow beat on the input

        Args:
            data: Data value
            sideband: Sideband value (WSTRB or RRESP)
            last: Assert narrow_last
        """
        self.dut.narrow_valid.value = 1
        self.dut.narrow_data.value = data
        if self.narrow_sb_width > 0:
            self.dut.narrow_sideband.value = sideband
        self.dut.narrow_last.value = 1 if last else 0

        # Wait for handshake
        await RisingEdge(self.clk)
        while self.dut.narrow_ready.value == 0:
            await RisingEdge(self.clk)

        # Deassert after accepted
        self.dut.narrow_valid.value = 0
        self.dut.narrow_last.value = 0
        self.narrow_beats_sent += 1

    async def receive_wide_beat(self, timeout_cycles=100):
        """
        Receive a wide beat from output

        Returns:
            (data, sideband, last) tuple
        """
        # Assert ready
        self.dut.wide_ready.value = 1

        # Wait for valid
        cycles = 0
        await RisingEdge(self.clk)
        while self.dut.wide_valid.value == 0:
            await RisingEdge(self.clk)
            cycles += 1
            if cycles > timeout_cycles:
                raise TimeoutError(f"Timeout waiting for wide_valid after {timeout_cycles} cycles")

        # Capture data
        data = int(self.dut.wide_data.value)
        sideband = int(self.dut.wide_sideband.value) if self.wide_sb_width > 0 else 0
        last = bool(self.dut.wide_last.value)

        # Wait one more cycle with ready asserted
        await RisingEdge(self.clk)

        # Deassert ready
        self.dut.wide_ready.value = 0
        self.wide_beats_received += 1

        return (data, sideband, last)

    async def test_basic_accumulation(self, num_transactions=10):
        """
        Test basic accumulation: send WIDTH_RATIO narrow beats,
        expect 1 wide beat with accumulated data
        """
        for txn in range(num_transactions):
            # Generate narrow beats
            narrow_beats = []
            for i in range(self.width_ratio):
                data = random.randint(0, (1 << self.narrow_width) - 1)
                sideband = random.randint(0, (1 << self.narrow_sb_width) - 1) if self.narrow_sb_width > 0 else 0
                narrow_beats.append((data, sideband))

            # Send narrow beats
            for i, (data, sideband) in enumerate(narrow_beats):
                is_last = (i == self.width_ratio - 1)
                await self.send_narrow_beat(data, sideband, last=False)

            # Receive wide beat
            wide_data, wide_sideband, wide_last = await self.receive_wide_beat()

            # Verify accumulation
            expected_data = 0
            for i, (data, _) in enumerate(narrow_beats):
                expected_data |= (data << (i * self.narrow_width))

            assert wide_data == expected_data, \
                f"Data mismatch: expected 0x{expected_data:x}, got 0x{wide_data:x}"

            # Verify sideband
            if self.narrow_sb_width > 0:
                if self.sb_or_mode:
                    # OR mode: expected is OR of all narrow sidebands
                    expected_sb = 0
                    for _, sb in narrow_beats:
                        expected_sb |= sb
                else:
                    # Concatenate mode: pack sidebands
                    expected_sb = 0
                    for i, (_, sb) in enumerate(narrow_beats):
                        expected_sb |= (sb << (i * self.narrow_sb_width))

                assert wide_sideband == expected_sb, \
                    f"Sideband mismatch: expected 0x{expected_sb:x}, got 0x{wide_sideband:x}"

    async def test_early_last(self, num_transactions=10):
        """
        Test early termination: send fewer than WIDTH_RATIO beats with last=1
        """
        for txn in range(num_transactions):
            # Send random number of beats (1 to WIDTH_RATIO-1)
            num_beats = random.randint(1, self.width_ratio - 1)

            narrow_beats = []
            for i in range(num_beats):
                data = random.randint(0, (1 << self.narrow_width) - 1)
                sideband = random.randint(0, (1 << self.narrow_sb_width) - 1) if self.narrow_sb_width > 0 else 0
                narrow_beats.append((data, sideband))

            # Send narrow beats (last one with last=1)
            for i, (data, sideband) in enumerate(narrow_beats):
                is_last = (i == num_beats - 1)
                await self.send_narrow_beat(data, sideband, last=is_last)

            # Receive wide beat
            wide_data, wide_sideband, wide_last = await self.receive_wide_beat()

            # Verify it arrived
            assert wide_last == True, f"Expected wide_last=1 for early termination"

    async def test_backpressure(self, num_transactions=5):
        """
        Test backpressure: delay wide_ready randomly
        """
        for txn in range(num_transactions):
            # Send WIDTH_RATIO narrow beats
            for i in range(self.width_ratio):
                data = random.randint(0, (1 << self.narrow_width) - 1)
                await self.send_narrow_beat(data, sideband=0, last=False)

            # Add random delay before asserting wide_ready
            delay_cycles = random.randint(5, 20)
            await self.wait_clocks(delay_cycles)

            # Now receive
            wide_data, wide_sideband, wide_last = await self.receive_wide_beat()

    async def test_continuous_streaming(self, num_wide_beats=20):
        """
        Test continuous streaming: no gaps between transactions
        """
        # Start receiver task
        received_beats = []

        async def receiver():
            self.dut.wide_ready.value = 1
            for _ in range(num_wide_beats):
                await RisingEdge(self.clk)
                while self.dut.wide_valid.value == 0:
                    await RisingEdge(self.clk)
                data = int(self.dut.wide_data.value)
                received_beats.append(data)

        receiver_task = cocotb.start_soon(receiver())

        # Send narrow beats continuously
        for wide_beat in range(num_wide_beats):
            for narrow_beat in range(self.width_ratio):
                data = (wide_beat << 8) | narrow_beat  # Unique pattern
                self.dut.narrow_valid.value = 1
                self.dut.narrow_data.value = data
                self.dut.narrow_last.value = 0
                await RisingEdge(self.clk)
                while self.dut.narrow_ready.value == 0:
                    await RisingEdge(self.clk)

        self.dut.narrow_valid.value = 0

        # Wait for receiver to finish
        await receiver_task

        # Verify we received all beats
        assert len(received_beats) == num_wide_beats, \
            f"Expected {num_wide_beats} wide beats, got {len(received_beats)}"
