# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeCamTB
# Purpose: Testbench class for bridge_cam module
#
# Documentation: projects/components/bridge/CLAUDE.md
# Subsystem: bridge/dv/tbclasses
#
# Author: sean galloway
# Created: 2025-10-26

import os
import sys
import random

from cocotb.utils import get_sim_time
from cocotb.triggers import ReadOnly

# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class BridgeCamTB(TBBase):
    """
    Testbench for the bridge_cam module.
    Supports two operational modes:
    - Mode 1 (ALLOW_DUPLICATES=0): Block duplicate IDs via cam_hit
    - Mode 2 (ALLOW_DUPLICATES=1): Allow duplicates with FIFO ordering
    """

    def __init__(self, dut):
        TBBase.__init__(self, dut)

        # Get test parameters from environment
        self.TAG_WIDTH = self.convert_to_int(os.environ.get('PARAM_TAG_WIDTH', '8'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('PARAM_DATA_WIDTH', '8'))
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '16'))
        self.ALLOW_DUPLICATES = self.convert_to_int(os.environ.get('PARAM_ALLOW_DUPLICATES', '0'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '0'))

        # Initialize random generator
        random.seed(self.SEED)

        # Calculate max values
        self.max_tag = (1 << self.TAG_WIDTH) - 1
        self.max_data = (1 << self.DATA_WIDTH) - 1

        # Log configuration
        self.log.info(f"Bridge CAM TB initialized:")
        self.log.info(f"  TAG_WIDTH={self.TAG_WIDTH}, DATA_WIDTH={self.DATA_WIDTH}")
        self.log.info(f"  DEPTH={self.DEPTH}, ALLOW_DUPLICATES={self.ALLOW_DUPLICATES}")
        self.log.info(f"  SEED={self.SEED}")

        # Test completion flag
        self.done = False

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug('Starting reset_dut')

        # Reset DUT control signals
        self.dut.rst_n.value = 0
        self.clear_interface()

        # Hold reset for multiple cycles
        await self.wait_clocks('clk', 10)

        # Release reset
        self.dut.rst_n.value = 1

        # Wait for stabilization
        await self.wait_clocks('clk', 10)

        self.log.debug('Ending reset_dut')

    def clear_interface(self):
        """Clear all interface signals"""
        self.dut.allocate.value = 0
        self.dut.allocate_tag.value = 0
        self.dut.allocate_data.value = 0
        self.dut.deallocate.value = 0
        self.dut.deallocate_tag.value = 0

    # =========================================================================
    # Status Checks
    # =========================================================================

    def check_empty(self):
        """Verify CAM is empty"""
        assert self.dut.tags_empty.value == 1, \
            f"CAM should be empty, but is not.{self.get_time_ns_str()}"

    def check_not_empty(self):
        """Verify CAM is not empty"""
        assert self.dut.tags_empty.value == 0, \
            f"CAM should not be empty, but is.{self.get_time_ns_str()}"

    def check_full(self):
        """Verify CAM is full"""
        assert self.dut.tags_full.value == 1, \
            f"CAM should be full, but is not.{self.get_time_ns_str()}"

    def check_not_full(self):
        """Verify CAM is not full"""
        assert self.dut.tags_full.value == 0, \
            f"CAM should not be full, but is.{self.get_time_ns_str()}"

    def check_cam_hit(self):
        """Verify cam_hit is asserted"""
        assert self.dut.cam_hit.value == 1, \
            f"cam_hit should be asserted, but is not.{self.get_time_ns_str()}"

    def check_cam_miss(self):
        """Verify cam_hit is not asserted"""
        assert self.dut.cam_hit.value == 0, \
            f"cam_hit should not be asserted, but is.{self.get_time_ns_str()}"

    # =========================================================================
    # Entry Port Operations (Allocation)
    # =========================================================================

    async def allocate_entry(self, tag, data):
        """
        Allocate a new entry in the CAM

        Args:
            tag: Transaction ID to store
            data: Associated data (master_index)
        """
        self.log.info(f"Allocating: tag=0x{tag:X}, data=0x{data:X}{self.get_time_ns_str()}")

        self.dut.allocate.value = 1
        self.dut.allocate_tag.value = tag
        self.dut.allocate_data.value = data
        await self.wait_clocks('clk', 1)

        self.dut.allocate.value = 0
        self.dut.allocate_tag.value = 0
        self.dut.allocate_data.value = 0

    # =========================================================================
    # Eviction Port Operations (Deallocation)
    # =========================================================================

    async def deallocate_entry(self, tag):
        """
        Deallocate an entry from the CAM

        Args:
            tag: Transaction ID to free

        Returns:
            tuple: (valid, data, count) from eviction port outputs
        """
        self.log.info(f"Deallocating: tag=0x{tag:X}{self.get_time_ns_str()}")

        self.dut.deallocate.value = 1
        self.dut.deallocate_tag.value = tag

        # Wait for combinational logic to settle
        await ReadOnly()

        # Capture eviction port outputs (combinational, before clock edge)
        valid = int(self.dut.deallocate_valid.value)
        data = int(self.dut.deallocate_data.value) if valid else 0
        count = int(self.dut.deallocate_count.value) if valid else 0

        # Wait for clock edge to allow sequential logic to update
        await self.wait_clocks('clk', 1)

        self.dut.deallocate.value = 0
        self.dut.deallocate_tag.value = 0

        return (valid, data, count)

    # =========================================================================
    # Test Sequences
    # =========================================================================

    async def run_basic_test(self):
        """Run basic functionality test"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting basic CAM functionality test @ {time_ns}ns")

        # Initial state checks
        self.check_empty()
        self.check_not_full()
        self.check_cam_miss()  # No entries, so no hit

        # Test with specific patterns
        tag1 = self.generate_alternating_ones(self.TAG_WIDTH)
        data1 = 0x5  # Master index
        tag2 = self.invert_bits(tag1, self.TAG_WIDTH)
        data2 = 0x3  # Different master

        # Allocate first entry
        await self.allocate_entry(tag1, data1)
        self.check_not_empty()
        self.check_not_full()

        # Try to allocate same tag (cam_hit should assert)
        self.dut.allocate_tag.value = tag1
        await self.wait_clocks('clk', 1)
        if self.ALLOW_DUPLICATES == 0:
            self.check_cam_hit()  # Mode 1: Hit should assert
        else:
            self.check_cam_hit()  # Mode 2: Hit also asserts (but allowed)

        # Clear signal
        self.dut.allocate_tag.value = 0

        # Allocate different tag
        await self.allocate_entry(tag2, data2)

        # Deallocate first entry and verify data
        valid, data, count = await self.deallocate_entry(tag1)
        assert valid == 1, f"Deallocation should succeed for tag 0x{tag1:X}"
        assert data == data1, f"Retrieved data {data} != expected {data1}"

        # Deallocate second entry
        valid, data, count = await self.deallocate_entry(tag2)
        assert valid == 1, f"Deallocation should succeed for tag 0x{tag2:X}"
        assert data == data2, f"Retrieved data {data} != expected {data2}"

        # Verify CAM is empty
        self.check_empty()
        self.check_not_full()

        time_ns = get_sim_time('ns')
        self.log.info(f"Basic CAM functionality test completed @ {time_ns}ns")

    async def run_capacity_test(self):
        """Test CAM to full capacity"""
        time_ns = get_sim_time('ns')
        self.log.info(f"Starting CAM capacity test @ {time_ns}ns")

        # Generate unique tag/data pairs
        entries = []
        for i in range(self.DEPTH):
            tag = self.generate_unique_tag([e[0] for e in entries])
            data = i  # Use index as master_index
            entries.append((tag, data))

        # Fill CAM to capacity
        self.log.info(f"Filling CAM with {self.DEPTH} unique entries")
        for i, (tag, data) in enumerate(entries):
            self.log.debug(f"Adding entry {i}: tag=0x{tag:X}, data=0x{data:X}")
            await self.allocate_entry(tag, data)

            # Verify correct status
            if i == self.DEPTH - 1:
                self.check_full()
            else:
                self.check_not_full()
            self.check_not_empty()

        # Try to add one more (should fail in Mode 1, succeed in Mode 2)
        extra_tag = self.generate_unique_tag([e[0] for e in entries])
        extra_data = self.max_data  # Use max value for this width
        self.log.info(f"Attempting to add extra entry to full CAM")
        await self.allocate_entry(extra_tag, extra_data)

        # Verify CAM is still full
        self.check_full()

        # Remove entries in random order
        random.shuffle(entries)
        self.log.info("Removing entries and verifying CAM status")
        for i, (tag, data) in enumerate(entries):
            self.log.debug(f"Removing entry {i}: tag=0x{tag:X}")
            valid, ret_data, count = await self.deallocate_entry(tag)

            assert valid == 1, f"Deallocation should succeed for tag 0x{tag:X}"
            assert ret_data == data, f"Retrieved data {ret_data} != expected {data}"

            # Verify correct status
            if i == 0:
                self.check_not_full()
            if i == self.DEPTH - 1:
                self.check_empty()
            else:
                self.check_not_empty()

        time_ns = get_sim_time('ns')
        self.log.info(f"CAM capacity test completed @ {time_ns}ns")

    async def run_mode2_test(self):
        """Test Mode 2 specific functionality (duplicate IDs with FIFO ordering)"""
        if self.ALLOW_DUPLICATES == 0:
            self.log.info("Skipping Mode 2 test (ALLOW_DUPLICATES=0)")
            return

        time_ns = get_sim_time('ns')
        self.log.info(f"Starting Mode 2 duplicate handling test @ {time_ns}ns")

        tag = self.max_tag - 1  # Use a valid tag for current TAG_WIDTH
        data_list = [0x0, 0x1, 0x2]  # Different masters (use values within DATA_WIDTH)

        # Allocate same tag three times
        self.log.info(f"Allocating tag 0x{tag:X} three times with different data")
        for i, data in enumerate(data_list):
            await self.allocate_entry(tag, data)
            self.check_cam_hit()  # Should always hit after first
            self.check_not_empty()

        # Deallocate three times (should return in FIFO order: 0, 1, 2)
        self.log.info("Deallocating in FIFO order (count=0 first)")
        for expected_data in data_list:
            valid, ret_data, count = await self.deallocate_entry(tag)

            assert valid == 1, f"Deallocation should succeed"
            assert ret_data == expected_data, \
                f"Expected data {expected_data}, got {ret_data} (FIFO violation!)"

            self.log.info(f"  Retrieved data=0x{ret_data:X}, count was {count}")

        # Verify CAM is empty
        self.check_empty()

        time_ns = get_sim_time('ns')
        self.log.info(f"Mode 2 duplicate handling test completed @ {time_ns}ns")

    async def cleanup_cam(self):
        """Clear all entries from the CAM"""
        self.log.info("Cleaning up CAM - removing all entries")

        # Try to deallocate all possible tags
        # This is a brute-force approach for cleanup
        for tag in range(min(256, 1 << self.TAG_WIDTH)):  # Limit to 256 max
            await self.deallocate_entry(tag)

        # Clear interface signals
        self.clear_interface()
        await self.wait_clocks('clk', 1)

        # Verify CAM is empty
        try:
            self.check_empty()
            self.log.info("CAM successfully cleaned up")
        except AssertionError:
            self.log.warning("CAM could not be completely cleaned up via deallocations")
            # Do a hardware reset as a last resort
            await self.reset_dut()

    # =========================================================================
    # Utility Methods
    # =========================================================================

    def generate_unique_tag(self, existing_tags=None):
        """Generate a tag not in the existing_tags list"""
        if existing_tags is None:
            existing_tags = []

        tag = random.randint(0, self.max_tag)

        while tag in existing_tags:
            tag = random.randint(0, self.max_tag)

        return tag

    def print_settings(self):
        """Print test configuration"""
        self.log.info('-------------------------------------------')
        self.log.info('Bridge CAM Settings:')
        self.log.info(f'    TAG_WIDTH:        {self.TAG_WIDTH}')
        self.log.info(f'    DATA_WIDTH:       {self.DATA_WIDTH}')
        self.log.info(f'    DEPTH:            {self.DEPTH}')
        self.log.info(f'    ALLOW_DUPLICATES: {self.ALLOW_DUPLICATES}')
        self.log.info(f'    SEED:             {self.SEED}')
        self.log.info('-------------------------------------------')
