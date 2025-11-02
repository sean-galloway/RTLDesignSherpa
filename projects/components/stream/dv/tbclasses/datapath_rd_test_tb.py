"""
Testbench class for datapath_rd_test module.

Purpose: Test wrapper for read data path streaming performance validation.
         Tests AXI Read Engine → SRAM Controller → SRAM integration.

Author: sean galloway
Created: 2025-10-26
"""

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.clock import Clock
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../../'))
sys.path.insert(0, repo_root)

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead
from CocoTBFramework.components.shared.memory_model import MemoryModel


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

        # Clock and reset
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # Parameters
        self.num_channels = 8
        self.data_width = 512
        self.addr_width = 64
        self.id_width = 8
        self.sram_depth = 4096

        # Memory model for AXI slave
        self.memory_model = MemoryModel(size=1024*1024*16)  # 16MB

        # AXI slave (simulates memory on read side)
        self.axi_slave = None  # Created in setup

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset."""
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize control inputs
        self.dut.datard_valid.value = 0
        self.dut.datard_addr.value = 0
        self.dut.datard_beats_remaining.value = 0
        self.dut.datard_burst_len.value = 0
        self.dut.datard_channel_id.value = 0

        # Create AXI slave
        self.axi_slave = AXI4SlaveRead(
            clock=self.clk,
            reset=self.rst_n,
            data_bus_width=self.data_width,
            addr_bus_width=self.addr_width,
            id_bus_width=self.id_width,
            dut=self.dut,
            prefix='m_axi',
            memory_model=self.memory_model
        )

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert reset signal."""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal."""
        self.rst_n.value = 1

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
                # Create incrementing pattern
                data = bytearray()
                for byte_idx in range(bytes_per_beat):
                    data.append((beat + byte_idx) & 0xFF)
            elif pattern == 'fixed':
                # Fixed pattern for easy verification
                data = bytearray([0xAA] * bytes_per_beat)
            else:
                # Random pattern
                import random
                data = bytearray([random.randint(0, 255) for _ in range(bytes_per_beat)])

            # Write to memory model
            self.memory_model.write(addr, bytes(data))

    async def issue_read_request(self, channel_id, src_addr, beats, burst_len):
        """Issue read request to data path.

        Args:
            channel_id: Channel ID (0-7)
            src_addr: Source address
            beats: Total beats to read
            burst_len: Burst length per AXI transaction
        """
        # Wait for ready
        while self.dut.datard_ready.value == 0:
            await RisingEdge(self.clk)

        # Issue request
        self.dut.datard_valid.value = 1
        self.dut.datard_channel_id.value = channel_id
        self.dut.datard_addr.value = src_addr
        self.dut.datard_beats_remaining.value = beats
        self.dut.datard_burst_len.value = burst_len

        # Wait for handshake
        await RisingEdge(self.clk)
        while self.dut.datard_ready.value == 0:
            await RisingEdge(self.clk)

        # Deassert valid
        self.dut.datard_valid.value = 0

    async def wait_for_completion(self, timeout_cycles=10000):
        """Wait for read operation to complete.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            (success, beats_done, error, error_resp)
        """
        cycles = 0
        total_beats = 0

        while cycles < timeout_cycles:
            await RisingEdge(self.clk)
            cycles += 1

            # Check for completion strobe
            if self.dut.datard_done_strobe.value == 1:
                beats_done = int(self.dut.datard_beats_done.value)
                total_beats += beats_done
                error = int(self.dut.datard_error.value)
                error_resp = int(self.dut.datard_error_resp.value)

                if error:
                    return (False, total_beats, error, error_resp)

                # Check if operation complete
                if beats_done > 0:
                    return (True, total_beats, 0, 0)

        # Timeout
        return (False, total_beats, 1, 0)

    async def check_sram_fill(self, channel_id, expected_count=None):
        """Check SRAM fill level for channel.

        Args:
            channel_id: Channel ID to check
            expected_count: Expected count (None = any count)

        Returns:
            Current count
        """
        await RisingEdge(self.clk)

        # Check valid flag
        valid = (int(self.dut.sram_rd_valid.value) >> channel_id) & 1

        # Get count
        count = int(self.dut.sram_rd_count.value >> (channel_id * 13)) & 0x1FFF

        if expected_count is not None:
            assert count == expected_count, \
                f"Channel {channel_id} count mismatch: got {count}, expected {expected_count}"

        return count

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
