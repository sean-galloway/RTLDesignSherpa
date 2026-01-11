# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BeatsAllocCtrlTB
# Purpose: RAPIDS Beats Allocation Control Testbench - Phase 1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Allocation Control Testbench - Phase 1

Testbench for the alloc_ctrl_beats module (Virtual FIFO for space tracking).
Tests allocation requests and actual data writes without data storage.

Use Case: Pre-allocation for AXI read engines to prevent race conditions

Interface:
  - Write side: Allocation requests (reserves space via wr_valid + wr_size)
  - Read side: Actual data writes (releases reservation via rd_valid)
"""

import os
import random
import cocotb
from typing import Dict, List, Optional

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class AllocCtrlBeatsTB(TBBase):
    """
    RAPIDS Beats Allocation Control testbench.

    Tests comprehensive allocation control functionality:
    - Space allocation (variable-size requests)
    - Data write acknowledgment (single-beat releases)
    - Full/empty detection
    - Space tracking accuracy
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
        self.allocs_sent = 0
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
        self.dut.wr_size.value = 0
        self.dut.rd_valid.value = 0

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
        self.log.info("=== Initializing Beats Alloc Control Test ===")
        self.log.info(f"  DEPTH: {self.TEST_DEPTH}")
        self.log.info(f"  ADDR_WIDTH: {self.addr_width}")

        # Clear inputs
        self.dut.wr_valid.value = 0
        self.dut.wr_size.value = 0
        self.dut.rd_valid.value = 0

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Beats alloc control initialization completed")

    async def allocate_space(self, size: int) -> bool:
        """Allocate space (send allocation request).

        Args:
            size: Number of entries to allocate (1-255)

        Returns:
            True if allocation accepted, False if timed out
        """
        self.dut.wr_valid.value = 1
        self.dut.wr_size.value = size

        # Wait for ready handshake (with timeout)
        for _ in range(100):
            # Check ready first - transfer happens on clock edge when both valid and ready
            if int(self.dut.wr_ready.value) == 1:
                await self.wait_clocks(self.clk_name, 1)  # Complete handshake
                self.allocs_sent += 1
                self.log.info(f"Allocated {size} beats (total allocs: {self.allocs_sent})")
                self.dut.wr_valid.value = 0
                self.dut.wr_size.value = 0
                return True
            await self.wait_clocks(self.clk_name, 1)

        self.log.warning(f"Allocation timeout for size={size}")
        self.dut.wr_valid.value = 0
        self.dut.wr_size.value = 0
        return False

    async def write_data(self) -> bool:
        """Signal that data has been written (releases reservation).

        Returns:
            True if write accepted, False if timed out
        """
        self.dut.rd_valid.value = 1

        # Wait for ready handshake (with timeout)
        for _ in range(100):
            # Check ready first - transfer happens on clock edge when both valid and ready
            if int(self.dut.rd_ready.value) == 1:
                await self.wait_clocks(self.clk_name, 1)  # Complete handshake
                self.drains_sent += 1
                self.dut.rd_valid.value = 0
                return True
            await self.wait_clocks(self.clk_name, 1)

        self.log.warning("Write data timeout")
        self.dut.rd_valid.value = 0
        return False

    def get_space_free(self) -> int:
        """Get current free space."""
        return int(self.dut.space_free.value)

    def is_full(self) -> bool:
        """Check if FIFO is full."""
        return int(self.dut.wr_full.value) == 1

    def is_empty(self) -> bool:
        """Check if FIFO is empty."""
        return int(self.dut.rd_empty.value) == 1

    # ==========================================================================
    # TEST METHODS
    # ==========================================================================

    async def test_basic_alloc_drain(self, num_ops=10):
        """Test basic allocation and drain cycle."""
        self.log.info(f"=== Basic Alloc/Drain Test: {num_ops} operations ===")

        passed = 0
        failed = 0

        for i in range(num_ops):
            alloc_size = random.randint(1, 8)

            # Get initial space
            initial_space = self.get_space_free()
            self.log.info(f"Op {i+1}: Allocating {alloc_size}, space_free={initial_space}")

            # Allocate space
            if not await self.allocate_space(alloc_size):
                self.log.error(f"Op {i+1}: Allocation failed")
                failed += 1
                continue

            await self.wait_clocks(self.clk_name, 2)

            # Check space decreased
            after_alloc_space = self.get_space_free()
            expected_space = initial_space - alloc_size
            if after_alloc_space != expected_space:
                self.log.error(f"Op {i+1}: Space mismatch after alloc: "
                             f"got {after_alloc_space}, expected {expected_space}")
                failed += 1
                continue

            # Write data to release reservation (one beat at a time)
            for _ in range(alloc_size):
                if not await self.write_data():
                    self.log.error(f"Op {i+1}: Write failed")
                    failed += 1
                    break
                await self.wait_clocks(self.clk_name, 1)

            await self.wait_clocks(self.clk_name, 2)

            # Check space restored
            after_drain_space = self.get_space_free()
            if after_drain_space != initial_space:
                self.log.error(f"Op {i+1}: Space mismatch after drain: "
                             f"got {after_drain_space}, expected {initial_space}")
                failed += 1
                continue

            passed += 1
            self.log.info(f"  Op {i+1}: PASS")

        self.log.info(f"Basic alloc/drain test: {passed}/{num_ops} passed")
        return failed == 0

    async def test_full_detection(self):
        """Test full flag detection."""
        self.log.info("=== Full Detection Test ===")

        # Fill up the FIFO with allocations
        total_allocated = 0
        while not self.is_full() and total_allocated < self.TEST_DEPTH + 10:
            alloc_size = min(64, self.get_space_free())
            if alloc_size == 0:
                break
            if not await self.allocate_space(alloc_size):
                break
            total_allocated += alloc_size
            await self.wait_clocks(self.clk_name, 2)

        if self.is_full():
            self.log.info(f"Full flag asserted after allocating {total_allocated} beats")
        else:
            self.log.error(f"Full flag not asserted (allocated {total_allocated})")
            return False

        # Verify write is rejected when full
        self.dut.wr_valid.value = 1
        self.dut.wr_size.value = 1
        await self.wait_clocks(self.clk_name, 2)
        if int(self.dut.wr_ready.value) == 0:
            self.log.info("Write correctly rejected when full")
        else:
            self.log.error("Write accepted when full")
            self.dut.wr_valid.value = 0
            return False
        self.dut.wr_valid.value = 0

        # Drain and verify not full
        if await self.write_data():
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

        # Allocate some space
        if not await self.allocate_space(4):
            self.log.error("Initial allocation failed")
            return False

        await self.wait_clocks(self.clk_name, 2)

        # Should not be empty now
        if not self.is_empty():
            self.log.info("Empty flag cleared after allocation")
        else:
            self.log.error("Empty flag still set after allocation")
            return False

        # Drain all
        for _ in range(4):
            if not await self.write_data():
                self.log.error("Drain failed")
                return False
            await self.wait_clocks(self.clk_name, 1)

        await self.wait_clocks(self.clk_name, 2)

        # Should be empty again
        if self.is_empty():
            self.log.info("Empty flag set after full drain")
            return True
        else:
            self.log.error("Empty flag not set after full drain")
            return False

    async def test_variable_size_alloc(self):
        """Test variable-size allocations."""
        self.log.info("=== Variable Size Allocation Test ===")

        test_sizes = [1, 2, 4, 8, 16, 32, 64]
        passed = 0

        for size in test_sizes:
            initial_space = self.get_space_free()
            if initial_space < size:
                self.log.info(f"  Skipping size={size}, not enough space")
                continue

            if await self.allocate_space(size):
                await self.wait_clocks(self.clk_name, 2)
                new_space = self.get_space_free()
                expected = initial_space - size

                if new_space == expected:
                    self.log.info(f"  Size {size}: space {initial_space} -> {new_space}")
                    passed += 1

                    # Drain to reset
                    for _ in range(size):
                        await self.write_data()
                        await self.wait_clocks(self.clk_name, 1)
                else:
                    self.log.error(f"  Size {size}: got {new_space}, expected {expected}")
            else:
                self.log.error(f"  Size {size}: allocation failed")

            await self.wait_clocks(self.clk_name, 5)

        self.log.info(f"Variable size test: {passed}/{len(test_sizes)} passed")
        return passed == len(test_sizes)

    async def test_stress_rapid_operations(self, num_ops=50):
        """Stress test with rapid alloc/drain operations."""
        self.log.info(f"=== Stress Test: {num_ops} rapid operations ===")

        pending_beats = 0
        errors = 0

        for i in range(num_ops):
            # Randomly allocate or drain
            op = random.choice(['alloc', 'drain', 'drain'])  # Bias toward drain

            if op == 'alloc' and not self.is_full():
                max_alloc = min(32, self.get_space_free())
                if max_alloc > 0:
                    size = random.randint(1, max_alloc)
                    if await self.allocate_space(size):
                        pending_beats += size
                    else:
                        errors += 1

            elif op == 'drain' and pending_beats > 0 and not self.is_empty():
                if await self.write_data():
                    pending_beats -= 1
                else:
                    errors += 1

            await self.wait_clocks(self.clk_name, random.randint(1, 3))

        # Drain remaining
        while pending_beats > 0 and not self.is_empty():
            if await self.write_data():
                pending_beats -= 1
            else:
                break
            await self.wait_clocks(self.clk_name, 1)

        self.log.info(f"Stress test completed: errors={errors}, pending={pending_beats}")
        return errors == 0 and pending_beats == 0

    def generate_test_report(self):
        """Generate comprehensive test report."""
        self.log.info("\n" + "=" * 60)
        self.log.info("BEATS ALLOC CONTROL TEST REPORT")
        self.log.info("=" * 60)
        self.log.info(f"Allocations sent: {self.allocs_sent}")
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
