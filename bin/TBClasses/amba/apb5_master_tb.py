# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: APB5MasterBasicTB
# Purpose: Testbench for apb5_master
# Subsystem: framework
#
# Extracted from val/amba/test_apb5_master.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from cocotb.triggers import Timer, RisingEdge
from TBClasses.shared.tbbase import TBBase


class APB5MasterBasicTB(TBBase):
    """Basic APB5 master testbench for RTL verification."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '12'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.AUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_AUSER_WIDTH', '4'))
        self.WUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_WUSER_WIDTH', '4'))
        self.RUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_RUSER_WIDTH', '4'))
        self.BUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_BUSER_WIDTH', '4'))

        self.log.info("="*60)
        self.log.info(" APB5 Master Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:  {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:  {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH: {self.AUSER_WIDTH}")
        self.log.info(f" WUSER_WIDTH: {self.WUSER_WIDTH}")
        self.log.info(f" RUSER_WIDTH: {self.RUSER_WIDTH}")
        self.log.info(f" BUSER_WIDTH: {self.BUSER_WIDTH}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        # Drain responses. Nothing drove rsp_ready before, so the response
        # skid filled after RSP_DEPTH transfers and never emptied. The test
        # still passed, because the pre-2026-09-04 apb5_master held PSEL and
        # PENABLE asserted past PREADY when it could not enqueue, and
        # wait_for_transaction() below returns True on seeing PENABLE &&
        # PREADY -- so the suite was watching a protocol violation and
        # scoring it a pass. With the master fixed to gate its launch on
        # response space (TASK-068, as apb4_master already did), an
        # undrained skid correctly stalls instead, and the old TB times out.
        self.dut.rsp_ready.value = 1
        self.dut.presetn.value = 0
        await self.wait_clocks('pclk', 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 5)
        self.log.info("Reset deasserted")

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('pclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def drive_command(self, pwrite, paddr, pwdata=0, pstrb=0xF, pauser=0, pwuser=0):
        """Drive a command through the command interface."""
        # Wait for ready
        while not self.dut.cmd_ready.value:
            await RisingEdge(self.dut.pclk)

        # Drive command
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = pwrite
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = pwdata
        self.dut.cmd_pstrb.value = pstrb
        if hasattr(self.dut, 'cmd_pauser'):
            self.dut.cmd_pauser.value = pauser
        if hasattr(self.dut, 'cmd_pwuser'):
            self.dut.cmd_pwuser.value = pwuser

        await RisingEdge(self.dut.pclk)
        self.dut.cmd_valid.value = 0

        self.log.info(f"Command sent: {'WRITE' if pwrite else 'READ'} "
                     f"addr=0x{paddr:04X} data=0x{pwdata:08X}")

    async def wait_for_transaction(self, timeout_cycles=100):
        """Wait for APB transaction to complete."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.pclk)
            if hasattr(self.dut, 'm_apb_PENABLE') and self.dut.m_apb_PENABLE.value:
                if hasattr(self.dut, 'm_apb_PREADY') and self.dut.m_apb_PREADY.value:
                    return True
        return False
