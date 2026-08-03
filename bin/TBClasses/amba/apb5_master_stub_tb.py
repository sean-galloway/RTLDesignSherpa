# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: APB5MasterStubBasicTB
# Purpose: Testbench for apb5_master_stub
# Subsystem: framework
#
# Extracted from val/amba/test_apb5_master_stub.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from TBClasses.shared.tbbase import TBBase


class APB5MasterStubBasicTB(TBBase):
    """Basic APB5 master stub testbench."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '12'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.AUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_AUSER_WIDTH', '4'))
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1

        self.log.info("="*60)
        self.log.info(" APB5 Master Stub Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:    {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:    {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH:   {self.AUSER_WIDTH}")
        self.log.info(f" ENABLE_PARITY: {self.ENABLE_PARITY}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.presetn.value = 0
        await self.wait_clocks('pclk', 5)

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 5)

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('pclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()
