"""
AXI Read Engine Testbench

Reusable testbench class for validating STREAM axi_read_engine.sv module.

Key Features:
- Provides AXI4 R channel slave responder (memory model)
- Provides SRAM write sink (monitors/captures written data)
- Drives datard_* scheduler interface
- Verifies completion strobes and beat counting
- Tests error handling (SLVERR, DECERR)

Design Pattern:
- Testbench: Infrastructure and BFMs (this file)
- Scoreboard: Verification logic (separate file)
- Test Runner: Test intelligence and parameters

Author: RTL Design Sherpa
Created: 2025-10-19
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random
from collections import deque
from enum import Enum

# Framework imports
import os
import sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class TestScenario(Enum):
    """Test scenario definitions"""
    BASIC_SINGLE_BURST = "basic_single_burst"    # Single burst, no backpressure
    MULTIPLE_BURSTS = "multiple_bursts"          # Multiple bursts to complete transfer
    SRAM_BACKPRESSURE = "sram_backpressure"      # SRAM randomly not ready
    AXI_BACKPRESSURE = "axi_backpressure"        # AXI R channel backpressure
    ERROR_RESPONSE = "error_response"            # AXI error responses (SLVERR)
    MAX_BURST_LIMIT = "max_burst_limit"          # Test burst length capping


class AXIReadEngineTB(TBBase):
    """
    Testbench class for STREAM AXI Read Engine

    Provides:
    - AXI4 R channel responder (memory model)
    - SRAM write sink (data capture)
    - Scheduler interface driver
    - Completion verification
    """

    def __init__(self, dut, **kwargs):
        """Initialize testbench"""
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # Memory model for AXI reads
        self.memory = {}  # addr -> data dictionary

        # SRAM write capture
        self.sram_data_written = []  # List of (addr, data) tuples

        # AXI AR channel tracking
        self.ar_requests = deque()  # Queue of pending AR requests

        # Completion tracking
        self.completion_strobes = []  # List of (beats_done, timestamp)

        # Test configuration
        self.sram_ready_probability = 1.0  # Default: always ready
        self.axi_r_ready_probability = 1.0  # Default: always ready (driven by DUT)
        self.inject_error = False
        self.error_response = 0  # 0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - start clocks and perform reset sequence

        MANDATORY METHOD - Required by TBBase pattern
        """
        # Start clock (10ns period = 100MHz)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all input signals BEFORE reset
        self.dut.datard_valid.value = 0
        self.dut.datard_addr.value = 0
        self.dut.datard_beats_remaining.value = 0
        self.dut.datard_burst_len.value = 0
        self.dut.datard_channel_id.value = 0

        self.dut.m_axi_rvalid.value = 0
        self.dut.m_axi_rid.value = 0
        self.dut.m_axi_rdata.value = 0
        self.dut.m_axi_rresp.value = 0
        self.dut.m_axi_rlast.value = 0

        self.dut.sram_wr_ready.value = 1

        # Perform reset
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)  # Hold reset
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)   # Stabilization

        # Start background responders
        cocotb.start_soon(self.axi_ar_monitor())
        cocotb.start_soon(self.axi_r_responder())
        cocotb.start_soon(self.sram_write_monitor())
        cocotb.start_soon(self.completion_monitor())

    async def assert_reset(self):
        """
        Assert reset signal

        MANDATORY METHOD - Required by TBBase pattern
        """
        self.rst_n.value = 0

    async def deassert_reset(self):
        """
        Deassert reset signal

        MANDATORY METHOD - Required by TBBase pattern
        """
        self.rst_n.value = 1

    def initialize_memory(self, base_addr: int, num_beats: int, data_width: int):
        """
        Initialize memory with test data

        Args:
            base_addr: Starting address (must be aligned!)
            num_beats: Number of beats to initialize
            data_width: Data width in bits
        """
        bytes_per_beat = data_width // 8

        for beat_idx in range(num_beats):
            addr = base_addr + (beat_idx * bytes_per_beat)

            # Generate test pattern: incremental data
            test_data = (beat_idx << 32) | (addr & 0xFFFFFFFF)

            # Store in memory model
            self.memory[addr] = test_data

        self.log.info(f"Initialized memory: base=0x{base_addr:X}, beats={num_beats}, pattern=incremental")

    async def axi_ar_monitor(self):
        """
        Monitor AXI AR channel and capture read requests

        Runs continuously in background
        """
        while True:
            await RisingEdge(self.clk)

            # Check for AR handshake
            if int(self.dut.m_axi_arvalid.value) == 1 and int(self.dut.m_axi_arready.value) == 1:
                ar_req = {
                    'addr': int(self.dut.m_axi_araddr.value),
                    'len': int(self.dut.m_axi_arlen.value),
                    'size': int(self.dut.m_axi_arsize.value),
                    'id': int(self.dut.m_axi_arid.value),
                    'burst': int(self.dut.m_axi_arburst.value),
                }

                self.ar_requests.append(ar_req)
                self.log.info(f"AR Request captured: addr=0x{ar_req['addr']:X}, len={ar_req['len']}, id={ar_req['id']}")

    async def axi_r_responder(self):
        """
        AXI R channel responder - provides read data from memory model

        Runs continuously in background
        """
        # Always accept AR requests
        self.dut.m_axi_arready.value = 1

        while True:
            await RisingEdge(self.clk)

            # Check if we have pending AR requests
            if self.ar_requests:
                ar_req = self.ar_requests.popleft()

                # Respond with R channel data
                await self.send_r_data(ar_req)

    async def send_r_data(self, ar_req: dict):
        """
        Send R channel data in response to AR request

        Args:
            ar_req: AR request dictionary
        """
        addr = ar_req['addr']
        burst_len = ar_req['len'] + 1  # arlen is (beats - 1)
        axi_id = ar_req['id']
        bytes_per_beat = 2 ** ar_req['size']

        for beat_idx in range(burst_len):
            # Read data from memory model
            if addr in self.memory:
                data = self.memory[addr]
            else:
                # Uninitialized memory - return zeros with warning
                data = 0
                self.log.warning(f"Reading uninitialized memory at 0x{addr:X}")

            # Determine if this is the last beat
            is_last = (beat_idx == burst_len - 1)

            # Determine response
            if self.inject_error and beat_idx == 0:
                resp = self.error_response
            else:
                resp = 0  # OKAY

            # Wait for DUT to be ready (check m_axi_rready)
            while int(self.dut.m_axi_rready.value) != 1:
                await RisingEdge(self.clk)

            # Drive R channel
            self.dut.m_axi_rvalid.value = 1
            self.dut.m_axi_rid.value = axi_id
            self.dut.m_axi_rdata.value = data
            self.dut.m_axi_rresp.value = resp
            self.dut.m_axi_rlast.value = 1 if is_last else 0

            await RisingEdge(self.clk)

            # Update address for next beat
            addr += bytes_per_beat

        # Clear R channel signals
        self.dut.m_axi_rvalid.value = 0
        self.dut.m_axi_rlast.value = 0

    async def sram_write_monitor(self):
        """
        Monitor SRAM write interface and capture written data

        Runs continuously in background
        """
        while True:
            await RisingEdge(self.clk)

            # Apply SRAM backpressure if configured
            if random.random() < self.sram_ready_probability:
                self.dut.sram_wr_ready.value = 1
            else:
                self.dut.sram_wr_ready.value = 0
                continue  # Skip this cycle

            # Check for SRAM write
            if int(self.dut.sram_wr_en.value) == 1 and int(self.dut.sram_wr_ready.value) == 1:
                wr_addr = int(self.dut.sram_wr_addr.value)
                wr_data = int(self.dut.sram_wr_data.value)

                self.sram_data_written.append((wr_addr, wr_data))

                if len(self.sram_data_written) % 16 == 1:
                    self.log.info(f"SRAM write {len(self.sram_data_written)}: addr={wr_addr}, data=0x{wr_data:X}")

    async def completion_monitor(self):
        """
        Monitor completion strobes from read engine

        Runs continuously in background
        """
        while True:
            await RisingEdge(self.clk)

            # Check for completion strobe
            if int(self.dut.datard_done_strobe.value) == 1:
                beats_done = int(self.dut.datard_beats_done.value)
                timestamp = cocotb.utils.get_sim_time(units='ns')

                self.completion_strobes.append((beats_done, timestamp))
                self.log.info(f"✓ Completion strobe: beats_done={beats_done} @ {timestamp}ns")

    async def request_read(self, addr: int, beats_remaining: int, burst_len: int = 16, channel_id: int = 0):
        """
        Request a read operation via datard_* interface

        Args:
            addr: Source address (must be aligned!)
            beats_remaining: Total beats remaining to read
            burst_len: Requested burst length
            channel_id: Channel ID
        """
        # Wait for engine to be ready
        while int(self.dut.datard_ready.value) != 1:
            await RisingEdge(self.clk)

        # Drive request
        self.dut.datard_valid.value = 1
        self.dut.datard_addr.value = addr
        self.dut.datard_beats_remaining.value = beats_remaining
        self.dut.datard_burst_len.value = burst_len
        self.dut.datard_channel_id.value = channel_id

        await RisingEdge(self.clk)

        # Wait for handshake
        while not (int(self.dut.datard_valid.value) == 1 and int(self.dut.datard_ready.value) == 1):
            await RisingEdge(self.clk)

        # Clear request
        self.dut.datard_valid.value = 0

        self.log.info(f"Read request: addr=0x{addr:X}, beats={beats_remaining}, burst_len={burst_len}")

    async def wait_for_completion(self, expected_completions: int, timeout_cycles: int = 1000):
        """
        Wait for expected number of completion strobes

        Args:
            expected_completions: Number of completion strobes to wait for
            timeout_cycles: Maximum cycles to wait

        Returns:
            bool: True if all completions received, False on timeout
        """
        for cycle in range(timeout_cycles):
            await RisingEdge(self.clk)

            if len(self.completion_strobes) >= expected_completions:
                self.log.info(f"✓ All {expected_completions} completions received")
                return True

        self.log.error(f"✗ Timeout waiting for completions: got {len(self.completion_strobes)}/{expected_completions}")
        return False

    async def run_basic_single_burst(self, addr: int = 0x1000, burst_len: int = 16):
        """
        Test basic single burst read operation

        Args:
            addr: Source address
            burst_len: Burst length

        Returns:
            bool: True if test passed
        """
        self.log.info("=== Basic Single Burst Test ===")

        # Initialize memory
        self.initialize_memory(addr, burst_len, int(self.dut.DATA_WIDTH.value))

        # Request read
        await self.request_read(addr, burst_len, burst_len, channel_id=0)

        # Wait for completion
        success = await self.wait_for_completion(expected_completions=1, timeout_cycles=500)

        if not success:
            return False

        # Verify correct number of SRAM writes
        if len(self.sram_data_written) != burst_len:
            self.log.error(f"✗ Expected {burst_len} SRAM writes, got {len(self.sram_data_written)}")
            return False

        self.log.info(f"✓ Basic single burst test passed: {burst_len} beats transferred")
        return True

    def get_test_report(self):
        """
        Generate test report

        Returns:
            dict: Test statistics
        """
        return {
            'ar_requests_captured': len(self.ar_requests),
            'sram_writes_captured': len(self.sram_data_written),
            'completion_strobes': len(self.completion_strobes),
            'total_beats_completed': sum(beats for beats, _ in self.completion_strobes),
        }
