"""
Testbench class for datapath_wr_test module.

Purpose: Test wrapper for write data path streaming performance validation.
         Tests SRAM → SRAM Controller → AXI Write Engine integration.

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
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveWrite
from CocoTBFramework.components.shared.memory_model import MemoryModel


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

        # AXI slave (simulates memory on write side)
        self.axi_slave = None  # Created in setup

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset."""
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize control inputs
        self.dut.datawr_valid.value = 0
        self.dut.datawr_addr.value = 0
        self.dut.datawr_beats_remaining.value = 0
        self.dut.datawr_burst_len.value = 0
        self.dut.datawr_channel_id.value = 0

        # Initialize SRAM preload
        self.dut.sram_preload_en.value = 0
        self.dut.sram_preload_addr.value = 0
        self.dut.sram_preload_data.value = 0

        # Create AXI slave
        self.axi_slave = AXI4SlaveWrite(
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

    async def preload_sram(self, start_addr, num_beats, pattern='increment'):
        """Preload SRAM with test data.

        Args:
            start_addr: Starting SRAM address
            num_beats: Number of beats to preload
            pattern: 'increment', 'random', or 'fixed'
        """
        bytes_per_beat = self.data_width // 8

        for beat in range(num_beats):
            sram_addr = start_addr + beat

            if pattern == 'increment':
                # Create incrementing pattern
                data = 0
                for byte_idx in range(bytes_per_beat):
                    data |= ((beat + byte_idx) & 0xFF) << (byte_idx * 8)
            elif pattern == 'fixed':
                # Fixed pattern for easy verification
                data = int('AA' * bytes_per_beat, 16)
            else:
                # Random pattern
                import random
                data = random.randint(0, (1 << self.data_width) - 1)

            # Preload SRAM
            self.dut.sram_preload_en.value = 1
            self.dut.sram_preload_addr.value = sram_addr
            self.dut.sram_preload_data.value = data

            await RisingEdge(self.clk)

        # Disable preload
        self.dut.sram_preload_en.value = 0
        await RisingEdge(self.clk)

    async def issue_write_request(self, channel_id, dst_addr, beats, burst_len):
        """Issue write request to data path.

        Args:
            channel_id: Channel ID (0-7)
            dst_addr: Destination address
            beats: Total beats to write
            burst_len: Burst length per AXI transaction
        """
        # Wait for ready
        while self.dut.datawr_ready.value == 0:
            await RisingEdge(self.clk)

        # Issue request
        self.dut.datawr_valid.value = 1
        self.dut.datawr_channel_id.value = channel_id
        self.dut.datawr_addr.value = dst_addr
        self.dut.datawr_beats_remaining.value = beats
        self.dut.datawr_burst_len.value = burst_len

        # Wait for handshake
        await RisingEdge(self.clk)
        while self.dut.datawr_ready.value == 0:
            await RisingEdge(self.clk)

        # Deassert valid
        self.dut.datawr_valid.value = 0

    async def wait_for_completion(self, timeout_cycles=10000):
        """Wait for write operation to complete.

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
            if self.dut.datawr_done_strobe.value == 1:
                beats_done = int(self.dut.datawr_beats_done.value)
                total_beats += beats_done
                error = int(self.dut.datawr_error.value)
                error_resp = int(self.dut.datawr_error_resp.value)

                if error:
                    return (False, total_beats, error, error_resp)

                # Check if operation complete
                if beats_done > 0:
                    return (True, total_beats, 0, 0)

        # Timeout
        return (False, total_beats, 1, 0)

    async def verify_memory_contents(self, dst_addr, num_beats, pattern='increment'):
        """Verify memory contents after write.

        Args:
            dst_addr: Starting destination address
            num_beats: Number of beats to verify
            pattern: Expected pattern

        Returns:
            (success, mismatches)
        """
        bytes_per_beat = self.data_width // 8
        mismatches = []

        for beat in range(num_beats):
            addr = dst_addr + (beat * bytes_per_beat)

            # Read from memory model
            actual_data = self.memory_model.read(addr, bytes_per_beat)

            # Generate expected pattern
            if pattern == 'increment':
                expected_data = bytearray()
                for byte_idx in range(bytes_per_beat):
                    expected_data.append((beat + byte_idx) & 0xFF)
            elif pattern == 'fixed':
                expected_data = bytearray([0xAA] * bytes_per_beat)
            else:
                # Can't verify random pattern
                continue

            # Compare
            if actual_data != expected_data:
                mismatches.append({
                    'beat': beat,
                    'addr': addr,
                    'expected': expected_data,
                    'actual': actual_data
                })

        success = (len(mismatches) == 0)
        return (success, mismatches)

    async def verify_continuous_streaming(self, total_beats, timeout_cycles=20000):
        """Verify W channel valid stays high continuously during streaming.

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

            w_valid = int(self.dut.m_axi_wvalid.value)
            w_ready = int(self.dut.m_axi_wready.value)

            if w_valid:
                consecutive_valid += 1
                if w_ready:
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
        # Wait for first W beat
        start_cycle = 0
        beats_transferred = 0
        cycles = 0

        while cycles < timeout_cycles:
            await RisingEdge(self.clk)
            cycles += 1

            w_valid = int(self.dut.m_axi_wvalid.value)
            w_ready = int(self.dut.m_axi_wready.value)

            if w_valid and w_ready:
                if start_cycle == 0:
                    start_cycle = cycles
                beats_transferred += 1

                if beats_transferred >= total_beats:
                    break

        actual_cycles = cycles - start_cycle + 1 if start_cycle > 0 else cycles
        theoretical_cycles = total_beats  # Perfect: 1 beat/cycle

        bandwidth_utilization = (theoretical_cycles / actual_cycles * 100) if actual_cycles > 0 else 0

        return (actual_cycles, bandwidth_utilization, beats_transferred)

    async def measure_burst_to_burst_latency(self, channel_id, dst_addr, burst_len, num_bursts):
        """Measure cycles between consecutive bursts.

        Args:
            channel_id: Channel ID
            dst_addr: Starting destination address
            burst_len: Burst length
            num_bursts: Number of bursts to measure

        Returns:
            (gaps_list, avg_gap, max_gap)
        """
        burst_end_cycles = []
        burst_start_cycles = []

        for burst in range(num_bursts):
            addr = dst_addr + (burst * burst_len * (self.data_width // 8))

            # Preload SRAM for this burst
            sram_offset = channel_id * (self.sram_depth // self.num_channels)
            await self.preload_sram(sram_offset, burst_len, pattern='increment')

            # Issue request
            await self.issue_write_request(channel_id, addr, burst_len, burst_len)

            # Track when first W data appears
            while True:
                await RisingEdge(self.clk)
                if int(self.dut.m_axi_wvalid.value):
                    burst_start_cycles.append(len(burst_start_cycles) + len(burst_end_cycles))
                    break

            # Track when burst completes
            while True:
                await RisingEdge(self.clk)
                if int(self.dut.datawr_done_strobe.value):
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

    async def run_streaming_test(self, channel_id, dst_addr, total_beats, burst_len,
                                 check_stalls=True):
        """Run streaming performance test.

        Args:
            channel_id: Channel ID
            dst_addr: Destination address
            total_beats: Total beats to transfer
            burst_len: Burst length
            check_stalls: Check for AXI stalls

        Returns:
            (success, total_cycles, stall_cycles, data_match)
        """
        # Preload SRAM with test data
        sram_offset = channel_id * (self.sram_depth // self.num_channels)
        await self.preload_sram(sram_offset, total_beats, pattern='increment')

        # Issue request
        await self.issue_write_request(channel_id, dst_addr, total_beats, burst_len)

        # Monitor streaming performance
        start_cycle = 0
        stall_cycles = 0
        aw_active = False
        w_active = False

        cycles = 0
        while cycles < 10000:
            await RisingEdge(self.clk)
            cycles += 1

            # Track AXI activity
            aw_valid = int(self.dut.m_axi_awvalid.value)
            aw_ready = int(self.dut.m_axi_awready.value)
            w_valid = int(self.dut.m_axi_wvalid.value)
            w_ready = int(self.dut.m_axi_wready.value)

            if aw_valid:
                aw_active = True
                if start_cycle == 0:
                    start_cycle = cycles
                if aw_ready == 0:
                    stall_cycles += 1

            if w_valid:
                w_active = True
                if w_ready == 0:
                    stall_cycles += 1

            # Check for completion
            if self.dut.datawr_done_strobe.value == 1:
                total_cycles = cycles - start_cycle
                success = (int(self.dut.datawr_error.value) == 0)

                # Verify data
                data_success, mismatches = await self.verify_memory_contents(
                    dst_addr, total_beats, pattern='increment')

                if check_stalls:
                    # Streaming should have minimal stalls
                    stall_ratio = stall_cycles / total_cycles if total_cycles > 0 else 0
                    print(f"Streaming test: {total_cycles} cycles, "
                          f"{stall_cycles} stalls ({stall_ratio*100:.1f}%), "
                          f"data_match={data_success}")

                return (success and data_success, total_cycles, stall_cycles, data_success)

        # Timeout
        return (False, cycles, stall_cycles, False)
