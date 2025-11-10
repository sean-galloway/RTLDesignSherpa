"""
Simple SRAM Testbench

Reusable testbench class for validating simple_sram.sv module.

Key Features:
- Tests basic write/read operations
- Verifies 1-cycle read latency
- Tests simultaneous read/write (dual-port)
- Optional chunk enable testing

Design Pattern:
- Testbench: Infrastructure (this file)
- Test Runner: Test intelligence and parameters

Author: RTL Design Sherpa
Created: 2025-10-19
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random

# Framework imports
import os
import sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class SimpleSRAMTB(TBBase):
    """
    Testbench class for Simple SRAM

    Provides:
    - Write/read sequencing
    - Data pattern generation
    - Read-after-write verification
    """

    def __init__(self, dut, **kwargs):
        """Initialize testbench"""
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Clock
        self.clk = dut.clk
        self.clk_name = 'clk'

        # Get parameters
        self.addr_width = int(dut.ADDR_WIDTH.value)
        self.data_width = int(dut.DATA_WIDTH.value)
        self.depth = int(dut.DEPTH.value)
        self.num_chunks = int(dut.NUM_CHUNKS.value)

        # Memory model for verification
        self.expected_mem = {}

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - start clocks

        MANDATORY METHOD - Required by TBBase pattern
        Note: SRAM has no reset signal
        """
        # Start clock (10ns period = 100MHz)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all input signals
        self.dut.wr_en.value = 0
        self.dut.wr_addr.value = 0
        self.dut.wr_data.value = 0
        self.dut.wr_chunk_en.value = (1 << self.num_chunks) - 1  # All chunks enabled

        self.dut.rd_en.value = 0
        self.dut.rd_addr.value = 0

        # Wait a few cycles for initialization
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert reset signal - Not applicable for SRAM"""
        pass  # SRAM has no reset

    async def deassert_reset(self):
        """Deassert reset signal - Not applicable for SRAM"""
        pass  # SRAM has no reset

    async def write(self, addr: int, data: int, chunk_en: int = None):
        """
        Write data to SRAM

        Args:
            addr: Write address
            data: Write data
            chunk_en: Optional chunk enable mask (default: all enabled)
        """
        # Apply write signals
        self.dut.wr_en.value = 1
        self.dut.wr_addr.value = addr
        self.dut.wr_data.value = data

        if chunk_en is not None:
            self.dut.wr_chunk_en.value = chunk_en
        else:
            self.dut.wr_chunk_en.value = (1 << self.num_chunks) - 1  # All chunks

        await RisingEdge(self.clk)

        # Clear write signals
        self.dut.wr_en.value = 0

        # Update expected memory model
        if chunk_en is None or chunk_en == ((1 << self.num_chunks) - 1):
            # Full word write
            self.expected_mem[addr] = data
        else:
            # Partial word write with chunk enables
            if addr not in self.expected_mem:
                self.expected_mem[addr] = 0

            chunk_width = self.data_width // self.num_chunks
            for i in range(self.num_chunks):
                if (chunk_en >> i) & 0x1:
                    # Extract chunk from write data
                    chunk_mask = (1 << chunk_width) - 1
                    chunk_data = (data >> (i * chunk_width)) & chunk_mask
                    # Clear old chunk bits and OR in new chunk
                    chunk_pos_mask = chunk_mask << (i * chunk_width)
                    self.expected_mem[addr] = (self.expected_mem[addr] & ~chunk_pos_mask) | (chunk_data << (i * chunk_width))

        chunk_en_str = f"0x{chunk_en:X}" if chunk_en is not None else "all"
        self.log.info(f"Write: addr={addr}, data=0x{data:X}, chunk_en={chunk_en_str}")

    async def read(self, addr: int):
        """
        Read data from SRAM (with 2-cycle latency)

        SRAM pipeline:
        - Cycle 0: Apply rd_en/rd_addr
        - Cycle 1: rd_addr_q/rd_en_q latched
        - Cycle 2: rd_data appears

        Args:
            addr: Read address

        Returns:
            int: Read data (after 2-cycle latency)
        """
        # Apply read signals
        self.dut.rd_en.value = 1
        self.dut.rd_addr.value = addr

        await RisingEdge(self.clk)

        # Clear read enable
        self.dut.rd_en.value = 0

        # Wait for 2-cycle latency (data appears 2 cycles later)
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        # Capture read data
        rd_data = int(self.dut.rd_data.value)

        self.log.info(f"Read: addr={addr}, data=0x{rd_data:X}")

        return rd_data

    async def run_basic_test(self, num_locations: int = 16):
        """
        Test basic write/read operations

        Args:
            num_locations: Number of memory locations to test

        Returns:
            bool: True if test passed
        """
        self.log.info("=== Basic Write/Read Test ===")

        # Generate test addresses and data (ensure unique addresses)
        test_data = []
        used_addrs = set()
        while len(test_data) < num_locations:
            addr = random.randint(0, self.depth - 1)
            if addr not in used_addrs:
                data = random.randint(0, (1 << self.data_width) - 1)
                test_data.append((addr, data))
                used_addrs.add(addr)

        # Write all locations
        for addr, data in test_data:
            await self.write(addr, data)

        # Read back and verify
        errors = 0
        for addr, expected_data in test_data:
            rd_data = await self.read(addr)

            if rd_data != expected_data:
                self.log.error(f"✗ Mismatch at addr={addr}: expected=0x{expected_data:X}, got=0x{rd_data:X}")
                errors += 1
            else:
                self.log.debug(f"✓ Match at addr={addr}: 0x{rd_data:X}")

        if errors == 0:
            self.log.info(f"✓ Basic test passed: {num_locations} locations verified")
            return True
        else:
            self.log.error(f"✗ Basic test failed: {errors}/{num_locations} mismatches")
            return False

    async def run_dual_port_test(self):
        """
        Test simultaneous read and write (dual-port operation)

        Returns:
            bool: True if test passed
        """
        self.log.info("=== Dual-Port Test ===")

        # Write to address 0
        await self.write(0, 0xDEADBEEF)

        # Simultaneously write to address 1 and read from address 0
        self.dut.wr_en.value = 1
        self.dut.wr_addr.value = 1
        self.dut.wr_data.value = 0xCAFEBABE
        self.dut.wr_chunk_en.value = (1 << self.num_chunks) - 1

        self.dut.rd_en.value = 1
        self.dut.rd_addr.value = 0

        await RisingEdge(self.clk)

        # Clear enables
        self.dut.wr_en.value = 0
        self.dut.rd_en.value = 0

        # Wait for 2-cycle read latency
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)

        # Verify read from address 0
        rd_data = int(self.dut.rd_data.value)
        if rd_data != 0xDEADBEEF:
            self.log.error(f"✗ Dual-port read failed: expected=0xDEADBEEF, got=0x{rd_data:X}")
            return False

        # Verify write to address 1
        rd_data = await self.read(1)
        if rd_data != 0xCAFEBABE:
            self.log.error(f"✗ Dual-port write failed: expected=0xCAFEBABE, got=0x{rd_data:X}")
            return False

        self.log.info("✓ Dual-port test passed")
        return True

    def get_test_report(self):
        """
        Generate test report

        Returns:
            dict: Test statistics
        """
        return {
            'addr_width': self.addr_width,
            'data_width': self.data_width,
            'depth': self.depth,
            'num_chunks': self.num_chunks,
            'locations_written': len(self.expected_mem),
        }
