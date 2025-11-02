# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CamTB
# Purpose: self.log.info the settings of the CRCTesting class.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

import os
import random

from cocotb.utils import get_sim_time
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class CamTB(TBBase):

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '0'))
        self.DEPTH = self.convert_to_int(os.environ.get('PARAM_DEPTH', '0'))
        self.max_val = (2**self.N)-1


    async def main_loop(self):
        self.log.info("Main Test")
        tag_list = [random.randint(0x00, self.max_val) for _ in range(self.DEPTH)]
        self.log.info(f'{tag_list=}')
        for tag in tag_list:
            await self.mark_one_valid(tag)
        self.check_not_empty()
        self.check_full()
        random.shuffle(tag_list)
        tag = tag_list.pop()
        await self.mark_one_invalid(tag)
        self.check_not_empty()
        self.check_not_full()
        await self.mark_one_valid(tag)
        self.check_full()
        tag_list.append(tag)
        for tag in tag_list:
            await self.mark_one_invalid(tag)
        self.clear_interface()
        await self.wait_clocks('clk', 1)
        self.check_empty()
        self.check_not_full()

    async def main_loop(self):
        self.log.info("Main Test")
        # Generate DEPTH unique tags
        tag_list = []
        while len(tag_list) < self.DEPTH:
            tag = random.randint(0x00, self.max_val)
            if tag not in tag_list:
                tag_list.append(tag)

        self.log.info(f'{tag_list=}')

        # Track which tags are actually added successfully
        valid_tags = []

        # Add tags to the CAM
        for tag in tag_list:
            await self.mark_one_valid(tag)
            # Verify tag was added successfully
            self.dut.tag_in_status.value = tag
            await self.wait_clocks('clk', 1)
            if self.dut.tag_status == 1:
                valid_tags.append(tag)

        self.check_not_empty()

        # Verify CAM is full if all tags were added
        if len(valid_tags) == self.DEPTH:
            self.check_full()

        # Process one tag
        random.shuffle(valid_tags)
        tag = valid_tags.pop()
        await self.mark_one_invalid(tag)
        self.check_not_empty()
        self.check_not_full()

        # Add tag back
        await self.mark_one_valid(tag)
        valid_tags.append(tag)

        # Check if CAM is full if we expect it to be
        if len(valid_tags) == self.DEPTH:
            self.check_full()

        # Remove all tags we know are valid
        for tag in valid_tags:
            await self.mark_one_invalid(tag)
            # Verify tag is removed
            self.dut.tag_in_status.value = tag
            await self.wait_clocks('clk', 1)
            assert self.dut.tag_status == 0, f"Tag 0x{tag:x} was not properly removed"

        self.clear_interface()
        await self.wait_clocks('clk', 1)
        self.check_empty()
        self.check_not_full()

    def clear_interface(self):
        self.dut.tag_in_status.value = 0
        self.dut.tag_in_valid.value = 0
        self.dut.tag_in_invalid.value = 0
        self.dut.mark_valid.value = 0
        self.dut.mark_invalid.value = 0


    def assert_reset(self):
        self.dut.rst_n.value = 0
        self.clear_interface()


    def deassert_reset(self):
        self.dut.rst_n.value = 1
        self.log.info("Reset complete.")


    def check_empty(self):
        assert self.dut.tags_empty == 1, f"CAM should be empty, but is not.{self.get_time_ns_str()}"


    def check_not_empty(self):
        assert self.dut.tags_empty == 0, f"CAM should not be empty, but is.{self.get_time_ns_str()}"


    def check_full(self):
        assert self.dut.tags_full == 1, f"CAM should be full, but is not.{self.get_time_ns_str()}"


    def check_not_full(self):
        assert self.dut.tags_full == 0, f"CAM should not be full, but is{self.get_time_ns_str()}."


    async def mark_one_valid(self, tag_value):
        self.log.info(f"Marking Valid {self.hex_format(tag_value, self.max_val)}{self.get_time_ns_str()}")
        self.dut.tag_in_valid.value = tag_value
        self.dut.mark_valid.value = 1
        await self.wait_clocks('clk', 1)
        self.dut.tag_in_valid.value = 0
        self.dut.mark_valid.value = 0


    async def mark_one_invalid(self, tag_value):
        self.log.info(f"Marking Invalid {self.hex_format(tag_value, self.max_val)}{self.get_time_ns_str()}")
        self.dut.tag_in_invalid.value = tag_value
        self.dut.mark_invalid.value = 1
        await self.wait_clocks('clk', 1)
        self.dut.tag_in_invalid.value = 0
        self.dut.mark_invalid.value = 0


    async def check_tag(self, tag_value, check):
        self.dut.tag_in_status.value = tag_value
        await self.wait_clocks('clk', 1)
        found = self.dut.tag_status
        if check == 1:
            msg = f"Expected tag({self.hex_format(tag_value, self.max_val)}) to be True{self.get_time_ns_str()}"
        else:
            msg = f"Expected tag({self.hex_format(tag_value, self.max_val)}) to be False{self.get_time_ns_str()}"
        assert found == check, msg


    def print_settings(self):
        """self.log.info the settings of the CRCTesting class.

        This method self.log.infos out the settings related to data width, chunks, CRC width, polynomial, initial polynomial value, input reflection, output reflection, and XOR output for CRC testing.

        Args:
            None
        Returns:
            None
        """
        self.log.info('-------------------------------------------')
        self.log.info('Settings:')
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    DEPTH: {self.DEPTH}')
        self.log.info('-------------------------------------------')

    async def cleanup_cam(self):
        """Clear all entries from the CAM"""
        self.log.info("Cleaning up CAM - removing all entries")

        # First, find all valid entries in the CAM by checking each possible tag
        valid_tags = []
        for tag in range(1 << self.N):
            self.dut.tag_in_status.value = tag
            await self.wait_clocks('clk', 1)
            if self.dut.tag_status == 1:
                valid_tags.append(tag)

        # Now invalidate all discovered valid tags
        for tag in valid_tags:
            self.log.debug(f"Cleanup: Removing tag 0x{tag:x}")
            await self.mark_one_invalid(tag)

        # Clear interface signals
        self.clear_interface()
        await self.wait_clocks('clk', 1)

        # Verify CAM is empty
        try:
            self.check_empty()
            self.log.info("CAM successfully cleaned up")
        except AssertionError:
            self.log.error("CAM could not be completely cleaned up!")
            # Do a hardware reset as a last resort
            await self.reset_dut()
