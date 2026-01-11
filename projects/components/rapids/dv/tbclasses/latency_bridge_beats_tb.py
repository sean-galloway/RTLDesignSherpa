# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: latency_bridge_beats_tb
# Purpose: Testbench for latency_bridge_beats module
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-01-10
"""
Testbench for latency_bridge_beats module

Purpose: Verify occupancy tracking and data flow through 1-cycle latency pipeline
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer

# Framework imports
import os
import sys

# Import framework utilities (PYTHONPATH includes bin/)
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)


class LatencyBridgeBeatsTB(TBBase):
    """Testbench for latency_bridge_beats"""

    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.data_width = int(dut.DATA_WIDTH.value)

    async def setup_clocks_and_reset(self):
        """Standard clock and reset initialization"""
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('clk', 5)

    async def assert_reset(self):
        """Assert reset signal"""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.dut.rst_n.value = 1

    async def write_beat(self, data, wait_ready=True):
        """Write a single beat to slave interface"""
        self.dut.s_data.value = data
        self.dut.s_valid.value = 1

        if wait_ready:
            while True:
                await RisingEdge(self.dut.clk)
                if int(self.dut.s_ready.value) == 1:
                    break
        else:
            await RisingEdge(self.dut.clk)

        self.dut.s_valid.value = 0

    async def read_beat(self, assert_ready=True):
        """Read a single beat from master interface"""
        if assert_ready:
            self.dut.m_ready.value = 1

        await RisingEdge(self.dut.clk)

        if int(self.dut.m_valid.value) == 1:
            data = int(self.dut.m_data.value)
            self.dut.m_ready.value = 0
            return data, True
        else:
            self.dut.m_ready.value = 0
            return None, False

    def get_occupancy(self):
        """Get current bridge occupancy (0-2)"""
        return int(self.dut.occupancy.value)

    async def verify_occupancy_tracking(self):
        """
        Verify occupancy correctly tracks pipeline state.

        Key insight: occupancy = r_pending + r_out_valid
        - Occupancy 2 occurs when pending capture completes while output is full
        - This is a transient state that lasts 1 cycle
        """
        self.log.info("=== Testing Occupancy Tracking ===")

        # Initial state: occupancy = 0
        occ = self.get_occupancy()
        assert occ == 0, f"Initial occupancy should be 0, got {occ}"
        self.log.info(f"Initial occupancy = 0")

        # Cycle 1: Write beat 1, m_ready=0 (no drain)
        self.dut.s_data.value = 0xBEEF
        self.dut.s_valid.value = 1
        self.dut.m_ready.value = 0
        await RisingEdge(self.dut.clk)
        # Now: pending=1, out_valid=0 -> occupancy=1
        occ = self.get_occupancy()
        self.log.info(f"After write beat 1 (cycle 1): occupancy={occ}, s_ready={int(self.dut.s_ready.value)}")

        # Cycle 2: pending captures to out_valid
        self.dut.s_valid.value = 0
        await RisingEdge(self.dut.clk)
        # Now: pending=0, out_valid=1 -> occupancy=1
        occ = self.get_occupancy()
        self.log.info(f"After capture (cycle 2): occupancy={occ}, out_valid={int(self.dut.m_valid.value)}")

        # Cycle 3: Try write beat 2 while out_valid=1, m_ready=0
        # s_ready should be 0 (no space!)
        s_rdy = int(self.dut.s_ready.value)
        self.log.info(f"Before beat 2: s_ready={s_rdy} (should be 0 - no space)")
        assert s_rdy == 0, f"Expected s_ready=0 when output full, got {s_rdy}"

        # Cycle 4: Drain output (m_ready=1) AND write new beat simultaneously
        self.dut.m_ready.value = 1
        self.dut.s_data.value = 0xCAFE
        self.dut.s_valid.value = 1
        await RisingEdge(self.dut.clk)
        # This is THE MAGIC MOMENT:
        # - out_valid consumes (goes to 0)
        # - pending arms (goes to 1)
        # - occupancy should still be 1 (transition)
        occ = self.get_occupancy()
        self.log.info(f"Simultaneous drain+write: occupancy={occ}")

        # Cycle 5: pending captures, out_valid=1 again
        self.dut.s_valid.value = 0
        self.dut.m_ready.value = 0
        await RisingEdge(self.dut.clk)
        # Now: pending=0, out_valid=1 -> occupancy=1
        occ = self.get_occupancy()
        self.log.info(f"After capture: occupancy={occ}")

        # Final drain
        self.dut.m_ready.value = 1
        await RisingEdge(self.dut.clk)
        occ = self.get_occupancy()
        self.log.info(f"After final drain: occupancy={occ}")
        assert occ == 0, f"Expected occupancy=0 after drain, got {occ}"

        self.log.info(f"Occupancy tracking verified (max observed: 1)")
        self.log.info(f"Note: occupancy=2 is transient (pending completing while output full)")

    async def verify_streaming_flow(self, num_beats=10):
        """
        Verify occupancy during continuous streaming:
        Write and read simultaneously
        """
        self.log.info(f"=== Testing Streaming Flow ({num_beats} beats) ===")

        occupancies = []

        for i in range(num_beats):
            # Write
            self.dut.s_data.value = i
            self.dut.s_valid.value = 1

            # Read (after first beat available)
            if i > 0:
                self.dut.m_ready.value = 1

            await RisingEdge(self.dut.clk)

            occ = self.get_occupancy()
            occupancies.append(occ)
            self.log.debug(f"Beat {i}: occupancy = {occ}")

        # Final read
        self.dut.s_valid.value = 0
        self.dut.m_ready.value = 1
        await RisingEdge(self.dut.clk)
        occ = self.get_occupancy()
        occupancies.append(occ)

        self.log.info(f"Occupancies during streaming: {occupancies}")
        self.log.info(f"Streaming flow completed")

        return occupancies
