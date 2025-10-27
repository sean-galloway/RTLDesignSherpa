"""
Testbench class for integrated datapath module.

Purpose: Test wrapper for complete datapath integration.
         Tests Memory → AXI Read Engine → SRAM → AXI Write Engine → Memory.

Author: sean galloway
Created: 2025-10-27
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
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead, AXI4SlaveWrite
from CocoTBFramework.components.shared.memory_model import MemoryModel


class DatapathTB(TBBase):
    """Testbench for integrated datapath module (read + write + SRAM)."""

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

        # Unified memory model for both read and write
        self.memory_model = MemoryModel(size=1024*1024*32)  # 32MB

        # AXI slaves (simulates memory)
        self.axi_read_slave = None  # Created in setup
        self.axi_write_slave = None  # Created in setup

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset."""
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize monitor configuration (disable all monitors for clean tests)
        self.dut.cfg_rdmon_err_enable.value = 0
        self.dut.cfg_rdmon_compl_enable.value = 0
        self.dut.cfg_rdmon_timeout_enable.value = 0
        self.dut.cfg_rdmon_perf_enable.value = 0
        self.dut.cfg_rdmon_debug_enable.value = 0
        self.dut.cfg_rdmon_timeout_cycles.value = 1000

        self.dut.cfg_wrmon_err_enable.value = 0
        self.dut.cfg_wrmon_compl_enable.value = 0
        self.dut.cfg_wrmon_timeout_enable.value = 0
        self.dut.cfg_wrmon_perf_enable.value = 0
        self.dut.cfg_wrmon_debug_enable.value = 0
        self.dut.cfg_wrmon_timeout_cycles.value = 1000

        # Initialize control inputs
        self.dut.datard_valid.value = 0
        self.dut.datard_addr.value = 0
        self.dut.datard_beats_remaining.value = 0
        self.dut.datard_burst_len.value = 0
        self.dut.datard_channel_id.value = 0

        self.dut.datawr_valid.value = 0
        self.dut.datawr_addr.value = 0
        self.dut.datawr_beats_remaining.value = 0
        self.dut.datawr_burst_len.value = 0
        self.dut.datawr_channel_id.value = 0

        # Monitor bus
        self.dut.mon_ready.value = 1  # Always accept monitor packets

        # Create AXI slaves
        self.axi_read_slave = AXI4SlaveRead(
            clock=self.clk,
            reset=self.rst_n,
            data_bus_width=self.data_width,
            addr_bus_width=self.addr_width,
            id_bus_width=self.id_width,
            dut=self.dut,
            prefix='m_axi_rd',
            memory_model=self.memory_model
        )

        self.axi_write_slave = AXI4SlaveWrite(
            clock=self.clk,
            reset=self.rst_n,
            data_bus_width=self.data_width,
            addr_bus_width=self.addr_width,
            id_bus_width=self.id_width,
            dut=self.dut,
            prefix='m_axi_wr',
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

    async def populate_source_memory(self, start_addr, num_beats, pattern='increment'):
        """Populate source memory with test data.

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

    async def issue_copy_operation(self, channel_id, src_addr, dst_addr, beats, burst_len):
        """Issue complete copy operation (read then write).

        Args:
            channel_id: Channel ID (0-7)
            src_addr: Source address
            dst_addr: Destination address
            beats: Total beats to transfer
            burst_len: Burst length per AXI transaction
        """
        # Issue read request
        await self.issue_read_request(channel_id, src_addr, beats, burst_len)

        # Wait for read completion
        await self.wait_for_read_completion()

        # Issue write request
        await self.issue_write_request(channel_id, dst_addr, beats, burst_len)

        # Wait for write completion
        await self.wait_for_write_completion()

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

    async def wait_for_read_completion(self, timeout_cycles=20000):
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

    async def wait_for_write_completion(self, timeout_cycles=20000):
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

    async def verify_memory_contents(self, src_addr, dst_addr, num_beats, pattern='increment'):
        """Verify destination memory matches source after copy.

        Args:
            src_addr: Source address
            dst_addr: Destination address
            num_beats: Number of beats to verify
            pattern: Expected pattern

        Returns:
            (success, mismatches)
        """
        bytes_per_beat = self.data_width // 8
        mismatches = []

        for beat in range(num_beats):
            src = src_addr + (beat * bytes_per_beat)
            dst = dst_addr + (beat * bytes_per_beat)

            # Read from memory model
            src_data = self.memory_model.read(src, bytes_per_beat)
            dst_data = self.memory_model.read(dst, bytes_per_beat)

            # Compare
            if src_data != dst_data:
                mismatches.append({
                    'beat': beat,
                    'src_addr': src,
                    'dst_addr': dst,
                    'src_data': src_data,
                    'dst_data': dst_data
                })

        success = (len(mismatches) == 0)
        return (success, mismatches)

    async def measure_end_to_end_bandwidth(self, total_beats, timeout_cycles=40000):
        """Measure complete pipeline bandwidth (read + SRAM + write).

        Args:
            total_beats: Total beats to transfer
            timeout_cycles: Maximum cycles to wait

        Returns:
            (actual_cycles, bandwidth_utilization_percent, beats_transferred)
        """
        # Wait for first data movement (either R or W)
        start_cycle = 0
        cycles = 0
        read_complete = False
        write_complete = False

        while cycles < timeout_cycles:
            await RisingEdge(self.clk)
            cycles += 1

            # Track first activity
            r_valid = int(self.dut.m_axi_rd_rvalid.value)
            r_ready = int(self.dut.m_axi_rd_rready.value)
            w_valid = int(self.dut.m_axi_wr_wvalid.value)
            w_ready = int(self.dut.m_axi_wr_wready.value)

            if (r_valid and r_ready) or (w_valid and w_ready):
                if start_cycle == 0:
                    start_cycle = cycles

            # Check for read completion
            if self.dut.datard_done_strobe.value == 1:
                read_complete = True

            # Check for write completion
            if self.dut.datawr_done_strobe.value == 1:
                write_complete = True
                if read_complete:
                    break

        actual_cycles = cycles - start_cycle + 1 if start_cycle > 0 else cycles
        theoretical_cycles = total_beats  # Perfect: 1 beat/cycle for complete pipeline

        bandwidth_utilization = (theoretical_cycles / actual_cycles * 100) if actual_cycles > 0 else 0

        return (actual_cycles, bandwidth_utilization, total_beats if (read_complete and write_complete) else 0)

    async def measure_pipeline_latency(self, channel_id, src_addr, dst_addr, burst_len):
        """Measure latency from read start to write completion.

        Args:
            channel_id: Channel ID
            src_addr: Source address
            dst_addr: Destination address
            burst_len: Burst length

        Returns:
            (read_latency, write_latency, total_latency)
        """
        # Populate source
        await self.populate_source_memory(src_addr, burst_len, pattern='increment')

        # Issue read
        issue_cycle = 0
        read_first_data_cycle = 0
        read_complete_cycle = 0
        write_first_data_cycle = 0
        write_complete_cycle = 0

        await self.issue_read_request(channel_id, src_addr, burst_len, burst_len)
        issue_cycle = 0

        # Track read
        cycles = 0
        while cycles < 10000:
            await RisingEdge(self.clk)
            cycles += 1

            if int(self.dut.m_axi_rd_rvalid.value) and read_first_data_cycle == 0:
                read_first_data_cycle = cycles

            if self.dut.datard_done_strobe.value == 1:
                read_complete_cycle = cycles
                break

        # Issue write
        await self.issue_write_request(channel_id, dst_addr, burst_len, burst_len)

        # Track write
        while cycles < 20000:
            await RisingEdge(self.clk)
            cycles += 1

            if int(self.dut.m_axi_wr_wvalid.value) and write_first_data_cycle == 0:
                write_first_data_cycle = cycles

            if self.dut.datawr_done_strobe.value == 1:
                write_complete_cycle = cycles
                break

        read_latency = read_complete_cycle - issue_cycle
        write_latency = write_complete_cycle - read_complete_cycle
        total_latency = write_complete_cycle - issue_cycle

        return (read_latency, write_latency, total_latency)
