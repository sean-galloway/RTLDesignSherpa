# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: AXIS5MasterCGBasicTB
# Purpose: Testbench for axis5_master_cg
# Subsystem: framework
#
# Extracted from val/amba/test_axis5_master_cg.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from cocotb.triggers import Timer, RisingEdge
from TBClasses.shared.tbbase import TBBase


class AXIS5MasterCGBasicTB(TBBase):
    """Basic AXIS5 master clock-gated testbench."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.SKID_DEPTH = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH', '4'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.ENABLE_WAKEUP = self.convert_to_int(os.environ.get('TEST_ENABLE_WAKEUP', '1')) == 1
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        self.log.info("="*60)
        self.log.info(" AXIS5 Master CG Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" SKID_DEPTH:    {self.SKID_DEPTH}")
        self.log.info(f" DATA_WIDTH:    {self.DATA_WIDTH}")
        self.log.info(f" ENABLE_WAKEUP: {self.ENABLE_WAKEUP}")
        self.log.info(f" ENABLE_PARITY: {self.ENABLE_PARITY}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 5)

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def enable_clock_gating(self, enable=True):
        """Enable or disable clock gating."""
        self.dut.cfg_cg_enable.value = 1 if enable else 0
        await RisingEdge(self.dut.aclk)
        self.log.info(f"Clock gating {'enabled' if enable else 'disabled'}")
