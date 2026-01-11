# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BeatsDrainCtrlTB
# Purpose: RAPIDS Beats Drain Control Testbench - Phase 1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Drain Control Testbench - Phase 1

Testbench for the drain_ctrl_beats module (Virtual FIFO for data availability tracking).
Tests data write tracking and drain request handling without data storage.

Use Case: Pre-reservation for AXI write engines to prevent underflow

Interface:
  - Write side: Data enters FIFO (single-beat via wr_valid)
  - Read side: Drain requests (variable-size via rd_valid + rd_size)
"""

import os
import random
import cocotb
from typing import Dict, List, Optional

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class DrainCtrlBeatsTB(TBBase):
    """
    RAPIDS Beats Drain Control testbench.

    Tests comprehensive drain control functionality:
    - Data write tracking (single-beat entries)
    - Drain requests (variable-size requests)
    - Full/empty detection
    - Data availability tracking
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '512'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.clk = clk if clk else dut.axi_aclk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'axi_aclk'
        self.rst_n = rst_n if rst_n else dut.axi_aresetn

        # Calculate address width from DEPTH
        self.addr_width = (self.TEST_DEPTH - 1).bit_length()

        # Test tracking
        self.writes_sent = 0
        self.drains_sent = 0
        self.test_errors = []

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks AND performs reset sequence"""
        # Start clock
        await self.start_clock(self.clk_name, freq=self.TEST_CLK_PERIOD, units='ns')

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

    async def assert_reset(self):
        """Assert reset signal"""
        self.mark_progress("assert_reset")
        self.rst_n.value = 0

        # Clear inputs during reset
        self.dut.wr_valid.value = 0
        self.dut.rd_valid.value = 0
        self.dut.rd_size.value = 0

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.mark_progress("deassert_reset")
        self.rst_n.value = 1
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset deasserted")

    async def initialize_test(self):
        """Initialize test environment"""
        self.log.info("=== Initializing Beats Drain Control Test ===")
        self.log.info(f"  DEPTH: {self.TEST_DEPTH}")
        self.log.info(f"  ADDR_WIDTH: {self.addr_width}")

        # Clear inputs
        self.dut.wr_valid.value = 0
        self.dut.rd_valid.value = 0
        self.dut.rd_size.value = 0

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Beats drain control initialization completed")

    async def write_data(self) -> bool:
        """Write data into the FIFO (single beat).

        Returns:
            True if write accepted, False if timed out
        """
        self.dut.wr_valid.value = 1

        # Wait for ready handshake (with timeout)
        for _ in range(100):
            # Check ready first - transfer happens on clock edge when both valid and ready
            if int(self.dut.wr_ready.value) == 1:
                await self.wait_clocks(self.clk_name, 1)  # Complete handshake
                self.writes_sent += 1
                self.dut.wr_valid.value = 0
                return True
            await self.wait_clocks(self.clk_name, 1)

        self.log.warning("Write data timeout")
        self.dut.wr_valid.value = 0
        return False

    async def drain_data(self, size: int) -> bool:
        """Drain data from the FIFO (variable size).

        Args:
            size: Number of entries to drain (1-255)

        Returns:
            True if drain accepted, False if timed out
        """
        self.dut.rd_valid.value = 1
        self.dut.rd_size.value = size

        # Wait for ready handshake (with timeout)
        for _ in range(100):
            # Check ready first - transfer happens on clock edge when both valid and ready
            if int(self.dut.rd_ready.value) == 1:
                await self.wait_clocks(self.clk_name, 1)  # Complete handshake
                self.drains_sent += 1
                self.log.info(f"Drained {size} beats (total drains: {self.drains_sent})")
                self.dut.rd_valid.value = 0
                self.dut.rd_size.value = 0
                return True
            await self.wait_clocks(self.clk_name, 1)

        self.log.warning(f"Drain timeout for size={size}")
        self.dut.rd_valid.value = 0
        self.dut.rd_size.value = 0
        return False

    def get_data_available(self) -> int:
        """Get current data available."""
        return int(self.dut.data_available.value)

    def is_full(self) -> bool:
        """Check if FIFO is full."""
        return int(self.dut.wr_full.value) == 1

    def is_empty(self) -> bool:
        """Check if FIFO is empty."""
        return int(self.dut.rd_empty.value) == 1

    # ==========================================================================
    # TEST METHODS
    # ==========================================================================

    async def test_basic_write_drain(self, num_ops=10):
        """Test basic write and drain cycle."""
        self.log.info(f"=== Basic Write/Drain Test: {num_ops} operations ===")

        passed = 0
        failed = 0

        for i in range(num_ops):
            write_count = random.randint(1, 8)

            # Get initial data available
            initial_data = self.get_data_available()
            self.log.info(f"Op {i+1}: Writing {write_count} beats, data_available={initial_data}")

            # Write data (one beat at a time)
            for _ in range(write_count):
                if not await self.write_data():
                    self.log.error(f"Op {i+1}: Write failed")
                    failed += 1
                    break
                await self.wait_clocks(self.clk_name, 1)

            await self.wait_clocks(self.clk_name, 2)

            # Check data available increased
            after_write_data = self.get_data_available()
            expected_data = initial_data + write_count
            if after_write_data != expected_data:
                self.log.error(f"Op {i+1}: Data mismatch after write: "
                             f"got {after_write_data}, expected {expected_data}")
                failed += 1
                continue

            # Drain data
            if not await self.drain_data(write_count):
                self.log.error(f"Op {i+1}: Drain failed")
                failed += 1
                continue

            await self.wait_clocks(self.clk_name, 2)

            # Check data available restored
            after_drain_data = self.get_data_available()
            if after_drain_data != initial_data:
                self.log.error(f"Op {i+1}: Data mismatch after drain: "
                             f"got {after_drain_data}, expected {initial_data}")
                failed += 1
                continue

            passed += 1
            self.log.info(f"  Op {i+1}: PASS")

        self.log.info(f"Basic write/drain test: {passed}/{num_ops} passed")
        return failed == 0

    async def test_full_detection(self):
        """Test full flag detection."""
        self.log.info("=== Full Detection Test ===")

        # Fill up the FIFO with writes
        total_written = 0
        while not self.is_full() and total_written < self.TEST_DEPTH + 10:
            if not await self.write_data():
                break
            total_written += 1
            await self.wait_clocks(self.clk_name, 1)

        if self.is_full():
            self.log.info(f"Full flag asserted after writing {total_written} beats")
        else:
            self.log.error(f"Full flag not asserted (wrote {total_written})")
            return False

        # Verify write is rejected when full
        self.dut.wr_valid.value = 1
        await self.wait_clocks(self.clk_name, 2)
        if int(self.dut.wr_ready.value) == 0:
            self.log.info("Write correctly rejected when full")
        else:
            self.log.error("Write accepted when full")
            self.dut.wr_valid.value = 0
            return False
        self.dut.wr_valid.value = 0

        # Drain and verify not full
        if await self.drain_data(1):
            await self.wait_clocks(self.clk_name, 2)
            if not self.is_full():
                self.log.info("Full flag cleared after drain")
                return True
            else:
                self.log.error("Full flag still set after drain")
                return False

        return False

    async def test_empty_detection(self):
        """Test empty flag detection."""
        self.log.info("=== Empty Detection Test ===")

        # Should start empty
        if self.is_empty():
            self.log.info("Empty flag set at start")
        else:
            self.log.error("Empty flag not set at start")
            return False

        # Write some data
        for _ in range(4):
            if not await self.write_data():
                self.log.error("Initial write failed")
                return False
            await self.wait_clocks(self.clk_name, 1)

        await self.wait_clocks(self.clk_name, 2)

        # Should not be empty now
        if not self.is_empty():
            self.log.info("Empty flag cleared after writes")
        else:
            self.log.error("Empty flag still set after writes")
            return False

        # Drain all
        if not await self.drain_data(4):
            self.log.error("Drain failed")
            return False

        await self.wait_clocks(self.clk_name, 2)

        # Should be empty again
        if self.is_empty():
            self.log.info("Empty flag set after full drain")
            return True
        else:
            self.log.error("Empty flag not set after full drain")
            return False

    async def test_variable_size_drain(self):
        """Test variable-size drains."""
        self.log.info("=== Variable Size Drain Test ===")

        test_sizes = [1, 2, 4, 8, 16, 32, 64]
        passed = 0

        for size in test_sizes:
            # Fill with exact amount
            for _ in range(size):
                if not await self.write_data():
                    self.log.error(f"  Size {size}: fill failed")
                    break
                await self.wait_clocks(self.clk_name, 1)

            await self.wait_clocks(self.clk_name, 2)
            initial_data = self.get_data_available()

            if initial_data != size:
                self.log.error(f"  Size {size}: unexpected data_available={initial_data}")
                continue

            # Drain all at once
            if await self.drain_data(size):
                await self.wait_clocks(self.clk_name, 2)
                final_data = self.get_data_available()

                if final_data == 0:
                    self.log.info(f"  Size {size}: drain successful")
                    passed += 1
                else:
                    self.log.error(f"  Size {size}: data_available={final_data} after drain")
            else:
                self.log.error(f"  Size {size}: drain failed")

            await self.wait_clocks(self.clk_name, 5)

        self.log.info(f"Variable size test: {passed}/{len(test_sizes)} passed")
        return passed == len(test_sizes)

    async def test_stress_rapid_operations(self, num_ops=50):
        """Stress test with rapid write/drain operations."""
        self.log.info(f"=== Stress Test: {num_ops} rapid operations ===")

        pending_beats = 0
        errors = 0

        for i in range(num_ops):
            # Randomly write or drain
            op = random.choice(['write', 'write', 'drain'])  # Bias toward write

            if op == 'write' and not self.is_full():
                if await self.write_data():
                    pending_beats += 1
                else:
                    errors += 1

            elif op == 'drain' and pending_beats > 0 and not self.is_empty():
                max_drain = min(32, pending_beats)
                size = random.randint(1, max_drain)
                if await self.drain_data(size):
                    pending_beats -= size
                else:
                    errors += 1

            await self.wait_clocks(self.clk_name, random.randint(1, 3))

        # Drain remaining
        while pending_beats > 0 and not self.is_empty():
            drain_size = min(pending_beats, 64)
            if await self.drain_data(drain_size):
                pending_beats -= drain_size
            else:
                break
            await self.wait_clocks(self.clk_name, 2)

        self.log.info(f"Stress test completed: errors={errors}, pending={pending_beats}")
        return errors == 0 and pending_beats == 0

    def generate_test_report(self):
        """Generate comprehensive test report."""
        self.log.info("\n" + "=" * 60)
        self.log.info("BEATS DRAIN CONTROL TEST REPORT")
        self.log.info("=" * 60)
        self.log.info(f"Writes sent: {self.writes_sent}")
        self.log.info(f"Drains sent: {self.drains_sent}")

        if self.test_errors:
            self.log.error(f"Test errors ({len(self.test_errors)}):")
            for error in self.test_errors:
                self.log.error(f"  - {error}")
            self.log.info("=" * 60)
            return False
        else:
            self.log.info("ALL TESTS PASSED SUCCESSFULLY!")
            self.log.info("=" * 60)
            return True
