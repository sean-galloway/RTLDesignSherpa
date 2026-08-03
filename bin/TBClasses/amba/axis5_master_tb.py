# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: AXIS5MasterBasicTB
# Purpose: Testbench for axis5_master
# Subsystem: framework
#
# Extracted from val/amba/test_axis5_master.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from cocotb.triggers import Timer, RisingEdge
from TBClasses.shared.tbbase import TBBase


class AXIS5MasterBasicTB(TBBase):
    """Basic AXIS5 master testbench for RTL verification."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.SKID_DEPTH = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH', '4'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.DEST_WIDTH = self.convert_to_int(os.environ.get('TEST_DEST_WIDTH', '4'))
        self.USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.ENABLE_WAKEUP = self.convert_to_int(os.environ.get('TEST_ENABLE_WAKEUP', '1')) == 1
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        self.log.info("="*60)
        self.log.info(" AXIS5 Master Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" SKID_DEPTH:    {self.SKID_DEPTH}")
        self.log.info(f" DATA_WIDTH:    {self.DATA_WIDTH}")
        self.log.info(f" ID_WIDTH:      {self.ID_WIDTH}")
        self.log.info(f" DEST_WIDTH:    {self.DEST_WIDTH}")
        self.log.info(f" USER_WIDTH:    {self.USER_WIDTH}")
        self.log.info(f" ENABLE_WAKEUP: {self.ENABLE_WAKEUP}")
        self.log.info(f" ENABLE_PARITY: {self.ENABLE_PARITY}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)
        self.log.info("Reset deasserted")

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def drive_fub_packet(self, data, last=1, id=0, dest=0, user=0, wakeup=0, strb=None):
        """Drive a packet through the FUB interface."""
        # Wait for ready
        while not self.dut.fub_axis_tready.value:
            await RisingEdge(self.dut.aclk)

        # Drive FUB signals
        self.dut.fub_axis_tvalid.value = 1
        self.dut.fub_axis_tdata.value = data
        self.dut.fub_axis_tlast.value = last
        self.dut.fub_axis_tstrb.value = strb if strb else (1 << self.STRB_WIDTH) - 1

        if hasattr(self.dut, 'fub_axis_tid'):
            self.dut.fub_axis_tid.value = id
        if hasattr(self.dut, 'fub_axis_tdest'):
            self.dut.fub_axis_tdest.value = dest
        if hasattr(self.dut, 'fub_axis_tuser'):
            self.dut.fub_axis_tuser.value = user
        if hasattr(self.dut, 'fub_axis_twakeup'):
            self.dut.fub_axis_twakeup.value = wakeup

        await RisingEdge(self.dut.aclk)
        self.dut.fub_axis_tvalid.value = 0

        self.log.info(f"FUB packet sent: data=0x{data:08X}, last={last}, wakeup={wakeup}")

    async def wait_for_transaction(self, timeout_cycles=100):
        """Wait for AXIS transaction to complete."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if self.dut.m_axis_tvalid.value and self.dut.m_axis_tready.value:
                return True
        return False
