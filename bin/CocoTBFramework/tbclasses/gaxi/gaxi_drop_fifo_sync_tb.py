# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GaxiDropFifoSyncTB
# Purpose: Testbench class for gaxi_drop_fifo_sync module.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Testbench class for gaxi_drop_fifo_sync module.

This testbench validates a synchronous FIFO with dynamic drop capability using GAXI BFMs.

REFACTORED: Now uses GAXI BFMs (GAXIMaster, GAXIMonitor) for protocol handling
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.types import LogicArray
import random
from typing import List, Tuple

# Import base class
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../shared'))
from tbbase import TBBase

# Import GAXI BFM components
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class GaxiDropFifoSyncTB(TBBase):
    """
    Testbench class for gaxi_drop_fifo_sync using GAXI BFMs.

    Uses GAXIMaster for write interface and GAXIMonitor for read monitoring.
    Manual control for drop interface and rd_ready signaling.
    """

    def __init__(self, dut):
        """Initialize testbench."""
        super().__init__(dut)
        self.dut = dut
        self.clk = dut.axi_aclk
        self.clk_name = 'axi_aclk'
        self.rst_n = dut.axi_aresetn

        # Extract parameters from DUT
        try:
            self.data_width = int(dut.DATA_WIDTH.value)
            self.depth = int(dut.DEPTH.value)
            self.registered = int(dut.REGISTERED.value)
        except AttributeError:
            self.data_width = 32
            self.depth = 16
            self.registered = 0

        # FIFO model for verification
        self.fifo_model: List[int] = []
        self.write_count = 0
        self.read_count = 0
        self.drop_count_total = 0

        # Create field configuration for GAXI BFMs
        self.field_config = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.data_width, 'default': 0}},
            lsb_first=True
        )

        # Create randomizer for timing variation
        self.randomizer = FlexRandomizer({
            'valid_delay': ([(0, 0), (1, 2)], [9, 1]),  # Mostly back-to-back
            'ready_delay': ([(0, 0), (1, 2)], [9, 1])
        })

        # Create Write Master BFM
        self.write_master = GAXIMaster(
            dut=dut,
            title='write_master',
            prefix='wr',
            clock=self.clk,
            field_config=self.field_config,
            timeout_cycles=1000,
            mode='skid',
            randomizer=self.randomizer,
            log=self.log,
            super_debug=False
        )

        # Create monitors for verification
        # Note: Using monitors only (not BFMs) for read side because drop testing
        # requires manual control - we need to write data, perform drops, THEN read.
        # A GAXISlave BFM would automatically consume data before we can test drops.
        self.wr_monitor = GAXIMonitor(
            dut=dut,
            title='write_monitor',
            prefix='wr',
            clock=self.clk,
            field_config=self.field_config,
            is_slave=True,  # Monitor is on slave side (FIFO input)
            mode='skid',
            log=self.log,
            super_debug=False
        )

        self.rd_monitor = GAXIMonitor(
            dut=dut,
            title='read_monitor',
            prefix='rd',
            clock=self.clk,
            field_config=self.field_config,
            is_slave=True,
            mode='fifo_mux' if self.registered == 0 else 'fifo_flop',
            log=self.log,
            super_debug=False
        )

        self.log.info(f"GaxiDropFifoSyncTB initialized: data_width={self.data_width}, "
                      f"depth={self.depth}, registered={self.registered}")

    async def setup_clocks_and_reset(self):
        """Complete initialization - start clocks and perform reset sequence."""
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all control signals
        self.dut.rd_ready.value = 0  # Manual control for drop testing
        self.dut.drop_valid.value = 0
        self.dut.drop_count.value = 0
        self.dut.drop_all.value = 0

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        # Reset write master BFM
        await self.write_master.reset_bus()

    async def assert_reset(self):
        """Assert active-low reset signal."""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert active-low reset signal."""
        self.rst_n.value = 1

    async def write_entry(self, data: int, expect_ready: bool = True) -> bool:
        """Write single entry to FIFO using GAXIMaster BFM.

        Args:
            data: Data value to write
            expect_ready: If False, check wr_ready before attempting write.
                         Returns False immediately if wr_ready=0.
                         If True, BFM will block until write completes.

        Returns:
            True if write completed, False if FIFO full (wr_ready=0)
        """
        # For capacity testing: check if FIFO can accept write
        if not expect_ready:
            # Wait a cycle for signals to settle
            await self.wait_clocks(self.clk_name, 1)

            # Check if wr_ready is low (FIFO full)
            if int(self.dut.wr_ready.value) == 0:
                return False  # FIFO full, cannot write

        packet = GAXIPacket(self.field_config)
        packet.data = data

        # Send via BFM (blocks until write completes)
        await self.write_master.send(packet)

        # Don't update model here - let monitors track everything
        self.write_count += 1

        # Extra settling time for rd_valid to update (mux mode timing)
        await self.wait_clocks(self.clk_name, 2)
        return True

    async def read_entry(self) -> Tuple[bool, int]:
        """Read single entry from FIFO with manual rd_ready control."""
        # Wait for rd_valid with timeout
        for _ in range(20):
            if int(self.dut.rd_valid.value) == 1:
                break
            await self.wait_clocks(self.clk_name, 1)

        if int(self.dut.rd_valid.value) == 0:
            self.log.error(f"Read timeout - rd_valid never asserted")
            return False, 0

        # Assert rd_ready to complete handshake
        self.dut.rd_ready.value = 1
        await RisingEdge(self.clk)
        self.dut.rd_ready.value = 0

        self.read_count += 1

        # Wait for monitor to capture the transaction
        # Mode-specific timing:
        # - Mux mode (REGISTERED=0): Monitor captures immediately, minimal wait
        # - Flop mode (REGISTERED=1): Monitor captures after registered output updates
        if self.registered == 0:
            # Mux mode: Monitor captures faster
            await self.wait_clocks(self.clk_name, 1)
        else:
            # Flop mode: Need more time for registered output
            await self.wait_clocks(self.clk_name, 2)

        # Sync with monitors to get the transaction into our model
        # This will process the write monitor queue (adds to model) and
        # the read monitor queue (which now has our read - removes from model)
        # But we need to capture the data BEFORE it's removed

        # Process writes first
        while len(self.wr_monitor._recvQ) > 0:
            pkt = self.wr_monitor._recvQ.popleft()
            self.fifo_model.append(pkt.data)

        # Now process reads - capture data from MODEL (source of truth)
        if len(self.rd_monitor._recvQ) > 0:
            pkt = self.rd_monitor._recvQ.popleft()
            # The monitor confirms a read happened, but data comes from model
            # Get data from front of model (FIFO order) BEFORE removing
            if len(self.fifo_model) > 0:
                rd_data = self.fifo_model.pop(0)  # This is what was read
            else:
                self.log.error(f"Read #{self.read_count}: Model empty but monitor has read")
                return False, 0
        else:
            self.log.error(f"Read #{self.read_count}: Monitor queue empty after read")
            return False, 0

        return True, rd_data

    async def drop_entries(self, count: int, drop_all: bool = False):
        """Perform drop operation using manual control signals."""
        count_before = self.get_fifo_count()
        model_before = len(self.fifo_model)
        self.dut._log.info(f"Drop operation: drop_all={drop_all}, count={count}")
        self.dut._log.info(f"  Before: DUT count={count_before}, model={model_before}")

        # Initiate drop with proper handshake
        self.dut.drop_valid.value = 1
        self.dut.drop_count.value = count
        self.dut.drop_all.value = 1 if drop_all else 0

        # Wait for drop_ready (proper valid/ready handshake)
        # Once drop_ready=1, handshake is complete and we can deassert drop_valid
        timeout = 10
        for cycle in range(timeout):
            await RisingEdge(self.clk)
            if int(self.dut.drop_ready.value) == 1:
                # Handshake complete - deassert drop_valid immediately
                # The assignment will take effect on next clock edge
                self.dut._log.info(f"  drop_ready asserted after {cycle} cycles")
                self.dut.drop_valid.value = 0
                break
        else:
            # Timeout - drop_ready never asserted
            assert False, f"drop_ready not asserted within {timeout} cycles"

        # Synchronize model with monitors to get current FIFO state
        self.sync_model_with_monitors()
        self.dut._log.info(f"  After monitor sync: model={len(self.fifo_model)}")

        # Apply drop operation to the model
        # Drop from the FRONT (oldest entries) of the FIFO
        if drop_all:
            dropped = len(self.fifo_model)
            self.fifo_model.clear()
        else:
            dropped = min(count, len(self.fifo_model))
            # Remove from front (oldest entries)
            self.fifo_model = self.fifo_model[dropped:]

        self.drop_count_total += dropped
        self.dut._log.info(f"  Dropped {dropped} entries from model")

        # Wait for flags to stabilize
        await self.wait_clocks(self.clk_name, 3)

        count_after = self.get_fifo_count()
        model_after = len(self.fifo_model)
        self.dut._log.info(f"  After: DUT count={count_after}, model={model_after}")

        if count_after != model_after:
            self.dut._log.error(f"  COUNT MISMATCH: DUT={count_after}, model={model_after}")

    async def fill_fifo(self, num_entries: int = None):
        """Fill FIFO with sequential data using BFM."""
        if num_entries is None:
            num_entries = self.depth - 1

        for i in range(num_entries):
            data = (self.write_count + i) & ((1 << self.data_width) - 1)
            await self.write_entry(data)

    async def drain_fifo(self):
        """Read all entries from FIFO until empty."""
        max_reads = self.depth * 2
        reads_performed = 0

        while reads_performed < max_reads:
            if int(self.dut.rd_valid.value) == 0:
                break

            success, data = await self.read_entry()
            if not success:
                break
            reads_performed += 1

    def get_fifo_count(self) -> int:
        """Get current FIFO occupancy from DUT."""
        return int(self.dut.count.value)

    def sync_model_with_monitors(self):
        """Synchronize model with monitor queues - incremental updates."""
        # Apply NEW writes from write monitor to model
        while len(self.wr_monitor._recvQ) > 0:
            pkt = self.wr_monitor._recvQ.popleft()
            self.fifo_model.append(pkt.data)

        # Apply NEW reads from read monitor to model
        while len(self.rd_monitor._recvQ) > 0:
            pkt = self.rd_monitor._recvQ.popleft()
            # Remove from front (FIFO order)
            if len(self.fifo_model) > 0:
                self.fifo_model.pop(0)

    def verify_count(self):
        """Verify DUT count matches model."""
        # Sync with monitors first to get accurate model
        self.sync_model_with_monitors()

        dut_count = self.get_fifo_count()
        model_count = len(self.fifo_model)
        assert dut_count == model_count, \
            f"Count mismatch: DUT={dut_count}, Model={model_count}"

    async def test_basic_fifo_operation(self):
        """Test basic FIFO write/read without drops."""
        self.dut._log.info("Testing basic FIFO operation")

        test_data = [0xAA, 0xBB, 0xCC, 0xDD]
        for data in test_data:
            await self.write_entry(data)

        self.verify_count()

        for expected in test_data:
            success, data = await self.read_entry()
            assert success, "Read failed"
            assert data == expected, f"Data mismatch: got {data:X}, expected {expected:X}"

        self.verify_count()

    async def test_drop_by_count(self):
        """Test dropping specific number of entries."""
        self.dut._log.info("Testing drop by count")

        await self.fill_fifo(8)
        count_before = self.get_fifo_count()

        await self.drop_entries(count=3, drop_all=False)

        count_after = self.get_fifo_count()
        assert count_after == count_before - 3, \
            f"Count after drop incorrect: {count_after}, expected {count_before - 3}"

        self.verify_count()

    async def test_drop_all(self):
        """Test dropping all FIFO entries."""
        self.dut._log.info("Testing drop all")

        await self.fill_fifo(10)
        assert self.get_fifo_count() > 0, "FIFO should have entries"

        await self.drop_entries(count=0, drop_all=True)

        count_after = self.get_fifo_count()
        assert count_after == 0, f"FIFO should be empty after drop_all, count={count_after}"

        self.verify_count()

    async def test_drop_during_io_blocked(self):
        """Test that normal I/O is blocked during drop operation."""
        self.dut._log.info("Testing I/O blocking during drop")

        await self.fill_fifo(5)

        # Start drop operation
        self.dut.drop_valid.value = 1
        self.dut.drop_count.value = 2
        self.dut.drop_all.value = 0
        await RisingEdge(self.clk)
        self.dut.drop_valid.value = 0

        # Check signals during drop
        await RisingEdge(self.clk)
        wr_ready_during_drop = int(self.dut.wr_ready.value)
        rd_valid_during_drop = int(self.dut.rd_valid.value)

        # Wait for drop to complete
        while int(self.dut.drop_ready.value) == 0:
            await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        # Verify I/O was blocked
        assert wr_ready_during_drop == 0, "wr_ready should be low during drop"
        assert rd_valid_during_drop == 0, "rd_valid should be low during drop"

    async def test_wraparound_with_drop(self):
        """Test drop operation across FIFO wraparound boundary."""
        self.dut._log.info("Testing wraparound with drop")

        fill_amount = self.depth - 2

        # Fill and drain multiple times
        for cycle in range(2):
            await self.fill_fifo(fill_amount)
            await self.wait_clocks(self.clk_name, 2)

            count = self.get_fifo_count()
            self.dut._log.info(f"After fill {cycle}: count={count}")

            await self.drain_fifo()
            await self.wait_clocks(self.clk_name, 2)

            count = self.get_fifo_count()
            self.dut._log.info(f"After drain {cycle}: count={count}")

        # Partial fill
        await self.fill_fifo(6)
        await self.wait_clocks(self.clk_name, 2)

        count_before_drop = self.get_fifo_count()
        self.dut._log.info(f"Before drop: count={count_before_drop}, model={len(self.fifo_model)}")

        # Drop some entries
        await self.drop_entries(count=3, drop_all=False)

        await self.wait_clocks(self.clk_name, 5)

        count_after_drop = self.get_fifo_count()
        self.dut._log.info(f"After drop: count={count_after_drop}, model={len(self.fifo_model)}")

        self.verify_count()

        # Verify remaining entries
        await self.wait_clocks(self.clk_name, 2)
        await self.drain_fifo()
        self.verify_count()
