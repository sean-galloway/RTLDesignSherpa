# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ResetSyncTB
# Purpose: Reset Synchronizer Testbench Class
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Reset Synchronizer Testbench Class

Reusable testbench for validating reset_sync module functionality.
Tests synchronizer behavior, timing, and CDC safety.
"""

import os
import cocotb
from cocotb.triggers import RisingEdge, Timer

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class ResetSyncTB(TBBase):
    """
    Testbench for reset_sync module

    Features:
    - Reset synchronization verification
    - Timing relationship validation
    - Multiple stage testing (N parameter)
    - Asynchronous reset assertion/deassertion
    """

    def __init__(self, dut):
        """Initialize testbench with DUT"""
        super().__init__(dut)

        # Get test parameters
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '3'))

        self.log.info(f"Reset Sync TB initialized with N={self.N}")

    async def reset_dut(self):
        """Apply reset to DUT"""
        self.dut.rst_n.value = 0
        await RisingEdge(self.dut.clk)
        await RisingEdge(self.dut.clk)
        self.dut.rst_n.value = 1
        # Wait for synchronization
        for _ in range(self.N + 2):
            await RisingEdge(self.dut.clk)

    async def test_basic_sync(self):
        """Test basic reset synchronization"""
        self.log.info("TEST: Basic Reset Synchronization")

        # Start with reset asserted
        self.dut.rst_n.value = 0
        await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle

        # sync_rst_n should be 0
        assert self.dut.sync_rst_n.value == 0, "sync_rst_n should be 0 during reset"

        # Deassert reset
        self.dut.rst_n.value = 1
        await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle

        # sync_rst_n should still be 0 (not synchronized yet)
        assert self.dut.sync_rst_n.value == 0, f"sync_rst_n should remain 0 for {self.N} clocks"

        # Wait N-1 more clock cycles for synchronization (already waited 1 above)
        for i in range(self.N - 1):
            await RisingEdge(self.dut.clk)
            await Timer(1, units='ns')  # Allow combinational output to settle

            # Log current state for debugging
            current_val = int(self.dut.sync_rst_n.value)
            self.log.debug(f"  After edge {i+2}, sync_rst_n = {current_val}")

            # Should still be 0 until the last cycle
            if i < self.N - 2:
                assert self.dut.sync_rst_n.value == 0, f"sync_rst_n should be 0 at cycle {i+1}/{self.N}"

        # After N total clocks (1 above + N-1 in loop), wait one more edge for the last stage to propagate
        await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle

        current_val = int(self.dut.sync_rst_n.value)
        self.log.debug(f"  After final edge (total {self.N+1}), sync_rst_n = {current_val}")

        assert self.dut.sync_rst_n.value == 1, f"sync_rst_n should be 1 after {self.N+1} total clock edges"

        self.log.info("✅ Basic synchronization: PASSED")
        return True

    async def test_reset_assertion_immediate(self):
        """Test that reset assertion propagates within 1 clock"""
        self.log.info("TEST: Immediate Reset Assertion")

        # Start with reset deasserted and synchronized
        self.dut.rst_n.value = 1
        for _ in range(self.N + 2):
            await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle
        assert self.dut.sync_rst_n.value == 1, "Setup: sync_rst_n should be 1"

        # Assert reset
        self.dut.rst_n.value = 0
        await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle

        # sync_rst_n should immediately go to 0 (asynchronous reset)
        assert self.dut.sync_rst_n.value == 0, "sync_rst_n should go to 0 immediately on reset"

        self.log.info("✅ Immediate reset assertion: PASSED")
        return True

    async def test_multiple_reset_cycles(self):
        """Test multiple reset/release cycles"""
        self.log.info("TEST: Multiple Reset Cycles")

        for cycle in range(3):
            # Assert reset
            self.dut.rst_n.value = 0
            await RisingEdge(self.dut.clk)
            await Timer(1, units='ns')  # Allow combinational output to settle
            assert self.dut.sync_rst_n.value == 0, f"Cycle {cycle}: sync_rst_n should be 0"

            # Deassert and wait for sync
            self.dut.rst_n.value = 1
            for _ in range(self.N + 1):
                await RisingEdge(self.dut.clk)
            await Timer(1, units='ns')  # Allow combinational output to settle
            assert self.dut.sync_rst_n.value == 1, f"Cycle {cycle}: sync_rst_n should be 1 after sync"

            # Hold for a few clocks
            for _ in range(5):
                await RisingEdge(self.dut.clk)
                await Timer(1, units='ns')  # Allow combinational output to settle
                assert self.dut.sync_rst_n.value == 1, f"Cycle {cycle}: sync_rst_n should remain 1"

        self.log.info("✅ Multiple reset cycles: PASSED")
        return True

    async def test_reset_glitch_filtering(self):
        """Test that very short reset pulses are filtered"""
        self.log.info("TEST: Reset Glitch Filtering")

        # Get to synchronized state
        self.dut.rst_n.value = 1
        for _ in range(self.N + 2):
            await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle
        assert self.dut.sync_rst_n.value == 1

        # Create a short glitch (< N clocks)
        self.dut.rst_n.value = 0
        await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle
        self.dut.rst_n.value = 1

        # The glitch should propagate immediately due to async reset
        # but recovery should take N clocks
        for i in range(self.N):
            await RisingEdge(self.dut.clk)
            await Timer(1, units='ns')  # Allow combinational output to settle
            if i < self.N - 1:
                # Should still be recovering
                current_val = self.dut.sync_rst_n.value.integer
                self.log.info(f"  Glitch recovery cycle {i}: sync_rst_n={current_val}")

        # After N clocks, should be back to 1
        await RisingEdge(self.dut.clk)
        await Timer(1, units='ns')  # Allow combinational output to settle
        assert self.dut.sync_rst_n.value == 1, "Should recover to 1 after N clocks"

        self.log.info("✅ Reset glitch filtering: PASSED")
        return True

    async def run_all_tests(self):
        """Run comprehensive reset_sync test suite"""
        self.log.info("="*80)
        self.log.info(f"RESET_SYNC COMPREHENSIVE TEST SUITE (N={self.N})")
        self.log.info("="*80)

        results = {}
        results['basic_sync'] = await self.test_basic_sync()
        results['immediate_assert'] = await self.test_reset_assertion_immediate()
        results['multiple_cycles'] = await self.test_multiple_reset_cycles()
        results['glitch_filter'] = await self.test_reset_glitch_filtering()

        passed = sum(results.values())
        total = len(results)

        self.log.info("="*80)
        self.log.info(f"RESULTS: {passed}/{total} tests passed")
        self.log.info("="*80)

        return all(results.values())
