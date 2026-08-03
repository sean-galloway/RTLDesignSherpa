# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: APB5SlaveBasicTB
# Purpose: Testbench for apb5_slave
# Subsystem: framework
#
# Extracted from val/amba/test_apb5_slave.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from TBClasses.shared.tbbase import TBBase


class APB5SlaveBasicTB(TBBase):
    """Basic APB5 slave testbench for RTL verification."""

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
        self.log.info(" APB5 Slave Testbench Configuration")
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

    async def drive_apb_write(self, paddr, pwdata, pstrb=0xF, pauser=0, pwuser=0):
        """Drive an APB5 write transaction."""
        # Setup phase
        self.dut.s_apb_PSEL.value = 1
        self.dut.s_apb_PENABLE.value = 0
        self.dut.s_apb_PWRITE.value = 1
        self.dut.s_apb_PADDR.value = paddr
        self.dut.s_apb_PWDATA.value = pwdata
        self.dut.s_apb_PSTRB.value = pstrb
        if hasattr(self.dut, 's_apb_PAUSER'):
            self.dut.s_apb_PAUSER.value = pauser
        if hasattr(self.dut, 's_apb_PWUSER'):
            self.dut.s_apb_PWUSER.value = pwuser

        await RisingEdge(self.dut.pclk)

        # Access phase
        self.dut.s_apb_PENABLE.value = 1
        await RisingEdge(self.dut.pclk)

        # Wait for PREADY
        timeout = 100
        while not self.dut.s_apb_PREADY.value and timeout > 0:
            await RisingEdge(self.dut.pclk)
            timeout -= 1

        # Capture response
        pslverr = int(self.dut.s_apb_PSLVERR.value)
        pbuser = int(self.dut.s_apb_PBUSER.value) if hasattr(self.dut, 's_apb_PBUSER') else 0

        # End transaction
        self.dut.s_apb_PSEL.value = 0
        self.dut.s_apb_PENABLE.value = 0
        await RisingEdge(self.dut.pclk)

        self.log.info(f"APB5 Write: addr=0x{paddr:04X} data=0x{pwdata:08X} "
                     f"err={pslverr} pbuser=0x{pbuser:X}")

        return timeout > 0, pslverr, pbuser

    async def drive_apb_read(self, paddr, pauser=0):
        """Drive an APB5 read transaction."""
        # Setup phase
        self.dut.s_apb_PSEL.value = 1
        self.dut.s_apb_PENABLE.value = 0
        self.dut.s_apb_PWRITE.value = 0
        self.dut.s_apb_PADDR.value = paddr
        if hasattr(self.dut, 's_apb_PAUSER'):
            self.dut.s_apb_PAUSER.value = pauser

        await RisingEdge(self.dut.pclk)

        # Access phase
        self.dut.s_apb_PENABLE.value = 1
        await RisingEdge(self.dut.pclk)

        # Wait for PREADY
        timeout = 100
        while not self.dut.s_apb_PREADY.value and timeout > 0:
            await RisingEdge(self.dut.pclk)
            timeout -= 1

        # Capture response
        prdata = int(self.dut.s_apb_PRDATA.value)
        pslverr = int(self.dut.s_apb_PSLVERR.value)
        pruser = int(self.dut.s_apb_PRUSER.value) if hasattr(self.dut, 's_apb_PRUSER') else 0

        # End transaction
        self.dut.s_apb_PSEL.value = 0
        self.dut.s_apb_PENABLE.value = 0
        await RisingEdge(self.dut.pclk)

        self.log.info(f"APB5 Read: addr=0x{paddr:04X} data=0x{prdata:08X} "
                     f"err={pslverr} pruser=0x{pruser:X}")

        return timeout > 0, prdata, pslverr, pruser

    async def drive_command_response(self, prdata, pslverr=0, pruser=0, pbuser=0, delay=0):
        """Drive response through command interface."""
        # Wait for command
        while not self.dut.cmd_valid.value:
            await RisingEdge(self.dut.pclk)

        # Accept command
        self.dut.cmd_ready.value = 1
        await RisingEdge(self.dut.pclk)
        self.dut.cmd_ready.value = 0

        # Add optional delay
        for _ in range(delay):
            await RisingEdge(self.dut.pclk)

        # Send response
        self.dut.rsp_valid.value = 1
        self.dut.rsp_prdata.value = prdata
        self.dut.rsp_pslverr.value = pslverr
        if hasattr(self.dut, 'rsp_pruser'):
            self.dut.rsp_pruser.value = pruser
        if hasattr(self.dut, 'rsp_pbuser'):
            self.dut.rsp_pbuser.value = pbuser

        # Wait for response acceptance
        while not self.dut.rsp_ready.value:
            await RisingEdge(self.dut.pclk)

        await RisingEdge(self.dut.pclk)
        self.dut.rsp_valid.value = 0
