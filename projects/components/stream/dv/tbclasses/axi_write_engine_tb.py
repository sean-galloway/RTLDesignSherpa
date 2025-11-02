"""
AXI Write Engine Testbench

Reusable testbench class for validating STREAM axi_write_engine.sv module.

Key Features:
- Provides AXI4 AW/W/B channel slave responder (memory model)
- Provides SRAM read data source (simulates SRAM)
- Drives datawr_* scheduler interface
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
    SRAM_BACKPRESSURE = "sram_backpressure"      # SRAM data not always valid
    AXI_BACKPRESSURE = "axi_backpressure"        # AXI W channel backpressure
    ERROR_RESPONSE = "error_response"            # AXI error responses (SLVERR)
    MAX_BURST_LIMIT = "max_burst_limit"          # Test burst length capping


class AXIWriteEngineTB(TBBase):
    """
    Testbench class for STREAM AXI Write Engine

    Provides:
    - AXI4 AW/W/B channel responder (memory model)
    - SRAM read data source (test data)
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

        # Memory model for AXI writes (captures written data)
        self.memory = {}  # addr -> data dictionary

        # SRAM test data
        self.sram_data = []  # List of data to provide via SRAM interface

        # AXI AW channel tracking
        self.aw_requests = deque()  # Queue of pending AW requests

        # AXI W channel tracking
        self.w_data_received = []  # List of (data, last) tuples

        # Completion tracking
        self.completion_strobes = []  # List of (beats_done, timestamp)

        # Test configuration
        self.sram_valid_probability = 1.0  # Default: always valid
        self.axi_w_ready_probability = 1.0  # Default: always ready
        self.axi_b_delay = 0  # Cycles to delay B response
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
        self.dut.datawr_valid.value = 0
        self.dut.datawr_addr.value = 0
        self.dut.datawr_beats_remaining.value = 0
        self.dut.datawr_burst_len.value = 0
        self.dut.datawr_channel_id.value = 0

        self.dut.m_axi_awready.value = 1
        self.dut.m_axi_wready.value = 1
        self.dut.m_axi_bvalid.value = 0
        self.dut.m_axi_bid.value = 0
        self.dut.m_axi_bresp.value = 0

        self.dut.sram_rd_data.value = 0
        self.dut.sram_rd_valid.value = 0

        # Perform reset
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)  # Hold reset
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)   # Stabilization

        # Start background responders
        cocotb.start_soon(self.axi_aw_monitor())
        cocotb.start_soon(self.axi_w_monitor())
        cocotb.start_soon(self.axi_b_responder())
        cocotb.start_soon(self.sram_read_responder())
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

    def initialize_sram_data(self, num_beats: int, data_width: int):
        """
        Initialize SRAM with test data

        Args:
            num_beats: Number of beats to generate
            data_width: Data width in bits
        """
        self.sram_data = []

        for beat_idx in range(num_beats):
            # Generate test pattern: incremental data
            test_data = (beat_idx << 32) | (beat_idx & 0xFFFFFFFF)
            self.sram_data.append(test_data)

        self.log.info(f"Initialized SRAM data: {num_beats} beats, pattern=incremental")

    async def axi_aw_monitor(self):
        """
        Monitor AXI AW channel and capture write requests

        Runs continuously in background
        """
        while True:
            await RisingEdge(self.clk)

            # Check for AW handshake
            if int(self.dut.m_axi_awvalid.value) == 1 and int(self.dut.m_axi_awready.value) == 1:
                aw_req = {
                    'addr': int(self.dut.m_axi_awaddr.value),
                    'len': int(self.dut.m_axi_awlen.value),
                    'size': int(self.dut.m_axi_awsize.value),
                    'id': int(self.dut.m_axi_awid.value),
                    'burst': int(self.dut.m_axi_awburst.value),
                }

                self.aw_requests.append(aw_req)
                self.log.info(f"AW Request captured: addr=0x{aw_req['addr']:X}, len={aw_req['len']}, id={aw_req['id']}")

    async def axi_w_monitor(self):
        """
        Monitor AXI W channel and capture write data

        Runs continuously in background
        """
        while True:
            await RisingEdge(self.clk)

            # Apply W channel backpressure if configured
            if random.random() < self.axi_w_ready_probability:
                self.dut.m_axi_wready.value = 1
            else:
                self.dut.m_axi_wready.value = 0
                continue  # Skip this cycle

            # Check for W handshake
            if int(self.dut.m_axi_wvalid.value) == 1 and int(self.dut.m_axi_wready.value) == 1:
                w_data = int(self.dut.m_axi_wdata.value)
                w_strb = int(self.dut.m_axi_wstrb.value)
                w_last = int(self.dut.m_axi_wlast.value)

                self.w_data_received.append((w_data, w_last))

                if len(self.w_data_received) % 16 == 1:
                    self.log.info(f"W beat {len(self.w_data_received)}: data=0x{w_data:X}, last={w_last}")

    async def axi_b_responder(self):
        """
        AXI B channel responder - provides write responses

        Runs continuously in background
        """
        while True:
            await RisingEdge(self.clk)

            # Check if we have completed write bursts (W last seen)
            if self.w_data_received and self.w_data_received[-1][1] == 1:
                # W last was seen, need to provide B response

                # Apply configured delay
                if self.axi_b_delay > 0:
                    await self.wait_clocks(self.clk_name, self.axi_b_delay)

                # Get corresponding AW request
                if self.aw_requests:
                    aw_req = self.aw_requests.popleft()
                    axi_id = aw_req['id']

                    # Determine response
                    if self.inject_error:
                        resp = self.error_response
                    else:
                        resp = 0  # OKAY

                    # Drive B channel
                    self.dut.m_axi_bvalid.value = 1
                    self.dut.m_axi_bid.value = axi_id
                    self.dut.m_axi_bresp.value = resp

                    await RisingEdge(self.clk)

                    # Wait for B ready
                    while int(self.dut.m_axi_bready.value) != 1:
                        await RisingEdge(self.clk)

                    # Clear B channel
                    self.dut.m_axi_bvalid.value = 0

                    self.log.info(f"✓ B response sent: id={axi_id}, resp={resp}")

    async def sram_read_responder(self):
        """
        SRAM read data source - provides test data when requested

        SRAM has 1-cycle latency: data valid on cycle AFTER rd_en

        Runs continuously in background
        """
        sram_idx = 0
        pending_read = False
        pending_idx = 0

        while True:
            await RisingEdge(self.clk)

            # Check for new SRAM read request (drives data NEXT cycle)
            if int(self.dut.sram_rd_en.value) == 1:
                pending_read = True
                pending_idx = sram_idx
                sram_idx += 1

            # Provide data from PREVIOUS cycle's read request (1-cycle latency)
            if pending_read:
                # Provide data from our test array
                if pending_idx < len(self.sram_data):
                    self.dut.sram_rd_data.value = self.sram_data[pending_idx]
                    self.dut.sram_rd_valid.value = 1
                else:
                    # Out of data - provide zeros
                    self.dut.sram_rd_data.value = 0
                    self.dut.sram_rd_valid.value = 1
                    self.log.warning(f"SRAM read beyond test data (idx={pending_idx})")
                pending_read = False
            else:
                # No pending read - set valid low
                self.dut.sram_rd_valid.value = 0

    async def completion_monitor(self):
        """
        Monitor completion strobes from write engine

        Runs continuously in background
        """
        while True:
            await RisingEdge(self.clk)

            # Check for completion strobe
            if int(self.dut.datawr_done_strobe.value) == 1:
                beats_done = int(self.dut.datawr_beats_done.value)
                timestamp = cocotb.utils.get_sim_time(units='ns')

                self.completion_strobes.append((beats_done, timestamp))
                self.log.info(f"✓ Completion strobe: beats_done={beats_done} @ {timestamp}ns")

    async def request_write(self, addr: int, beats_remaining: int, burst_len: int = 16, channel_id: int = 0):
        """
        Request a write operation via datawr_* interface

        Args:
            addr: Destination address (must be aligned!)
            beats_remaining: Total beats remaining to write
            burst_len: Requested burst length
            channel_id: Channel ID
        """
        # Wait for engine to be ready
        while int(self.dut.datawr_ready.value) != 1:
            await RisingEdge(self.clk)

        # Drive request
        self.dut.datawr_valid.value = 1
        self.dut.datawr_addr.value = addr
        self.dut.datawr_beats_remaining.value = beats_remaining
        self.dut.datawr_burst_len.value = burst_len
        self.dut.datawr_channel_id.value = channel_id

        await RisingEdge(self.clk)

        # Wait for handshake
        while not (int(self.dut.datawr_valid.value) == 1 and int(self.dut.datawr_ready.value) == 1):
            await RisingEdge(self.clk)

        # Clear request
        self.dut.datawr_valid.value = 0

        self.log.info(f"Write request: addr=0x{addr:X}, beats={beats_remaining}, burst_len={burst_len}")

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

    async def run_basic_single_burst(self, addr: int = 0x2000, burst_len: int = 16):
        """
        Test basic single burst write operation

        Args:
            addr: Destination address
            burst_len: Burst length

        Returns:
            bool: True if test passed
        """
        self.log.info("=== Basic Single Burst Write Test ===")

        # Initialize SRAM with test data
        self.initialize_sram_data(burst_len, int(self.dut.DATA_WIDTH.value))

        # Request write
        await self.request_write(addr, burst_len, burst_len, channel_id=0)

        # Wait for completion
        success = await self.wait_for_completion(expected_completions=1, timeout_cycles=500)

        if not success:
            return False

        # Verify correct number of W beats
        if len(self.w_data_received) != burst_len:
            self.log.error(f"✗ Expected {burst_len} W beats, got {len(self.w_data_received)}")
            return False

        # Verify data matches SRAM source
        for i, (w_data, w_last) in enumerate(self.w_data_received):
            expected_data = self.sram_data[i]
            if w_data != expected_data:
                self.log.error(f"✗ W beat {i}: expected 0x{expected_data:X}, got 0x{w_data:X}")
                return False

            # Check LAST flag
            expected_last = 1 if i == (burst_len - 1) else 0
            if w_last != expected_last:
                self.log.error(f"✗ W beat {i}: expected LAST={expected_last}, got {w_last}")
                return False

        self.log.info(f"✓ Basic single burst write test passed: {burst_len} beats transferred")
        return True

    def get_test_report(self):
        """
        Generate test report

        Returns:
            dict: Test statistics
        """
        return {
            'aw_requests_captured': len(self.aw_requests),
            'w_beats_received': len(self.w_data_received),
            'completion_strobes': len(self.completion_strobes),
            'total_beats_completed': sum(beats for beats, _ in self.completion_strobes),
        }
