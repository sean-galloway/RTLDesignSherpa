# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: APB5MonitorTB
# Purpose: Testbench for apb5_monitor
# Subsystem: framework
#
# Extracted from val/amba/test_apb5_monitor.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from TBClasses.shared.tbbase import TBBase


class APB5MonitorTB(TBBase):
    """APB5 monitor testbench for RTL verification."""

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
        self.log.info(" APB5 Monitor Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:  {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:  {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH: {self.AUSER_WIDTH}")
        self.log.info(f" WUSER_WIDTH: {self.WUSER_WIDTH}")
        self.log.info(f" RUSER_WIDTH: {self.RUSER_WIDTH}")
        self.log.info(f" BUSER_WIDTH: {self.BUSER_WIDTH}")
        self.log.info("="*60)

        # Track monitor packets
        self.monitor_packets = []

    # ------------------------------------------------------------------
    # 128-bit monitor packet decode (monitor_package_spec.md)
    #   [127:124] packet_type   [123:109] reserved   [108:105] protocol
    #   [104: 97] event_code    [ 96: 88] channel_id [ 87: 72] agent_id
    #   [ 71: 64] unit_id       [ 63:  0] event_data
    # ------------------------------------------------------------------
    @staticmethod
    def decode_packet(pkt: int) -> dict:
        """Decode a 128-bit monbus packet into its named fields.

        Delegates to TBClasses.monbus.parse -- the house-sanctioned decode
        chokepoint. Inline bit-twiddling here previously (a) duplicated the
        field layout so a packet-format change silently desynced this TB, and
        (b) escaped the MONBUS_COVERAGE packet-type coverage recorder, which
        instruments parse(). Same returned dict, same keys.
        """
        from TBClasses.monbus import parse
        mp = parse(pkt)
        return {
            'packet_type': int(mp.packet_type),
            'protocol':    int(mp.protocol),
            'event_code':  int(mp.event_code),
            'channel_id':  int(mp.channel_id),
            'agent_id':    int(mp.agent_id),
            'unit_id':     int(mp.unit_id),
            'event_data':  int(mp.event_data),
        }

    async def drive_mon_time(self):
        """Free-running monitor-time broadcast (normally from monbus_group)."""
        self.dut.i_mon_time.value = 0
        count = 0
        while True:
            await RisingEdge(self.dut.aclk)
            count = (count + 1) & ((1 << 64) - 1)
            self.dut.i_mon_time.value = count

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

    async def drive_cmd_write(self, paddr, pwdata, pstrb=0xF, pprot=0, pauser=0, pwuser=0):
        """Drive a write command through the command interface."""
        # Wait for ready
        while not self.dut.cmd_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive command
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = 1
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = pwdata
        self.dut.cmd_pstrb.value = pstrb
        self.dut.cmd_pprot.value = pprot
        self.dut.cmd_pauser.value = pauser
        self.dut.cmd_pwuser.value = pwuser

        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

        self.log.info(f"CMD Write: addr=0x{paddr:04X} data=0x{pwdata:08X}")

    async def drive_cmd_read(self, paddr, pprot=0, pauser=0):
        """Drive a read command through the command interface."""
        # Wait for ready
        while not self.dut.cmd_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive command
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = 0
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = 0
        self.dut.cmd_pstrb.value = 0
        self.dut.cmd_pprot.value = pprot
        self.dut.cmd_pauser.value = pauser
        self.dut.cmd_pwuser.value = 0

        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

        self.log.info(f"CMD Read: addr=0x{paddr:04X}")

    async def drive_rsp(self, prdata, pslverr=0, pruser=0, pbuser=0):
        """Drive a response through the response interface."""
        # Wait for ready
        while not self.dut.rsp_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive response
        self.dut.rsp_valid.value = 1
        self.dut.rsp_prdata.value = prdata
        self.dut.rsp_pslverr.value = pslverr
        self.dut.rsp_pruser.value = pruser
        self.dut.rsp_pbuser.value = pbuser

        await RisingEdge(self.dut.aclk)
        self.dut.rsp_valid.value = 0

        self.log.info(f"RSP: data=0x{prdata:08X} err={pslverr}")

    async def drive_wakeup(self, cycles=3):
        """Drive PWAKEUP signal."""
        self.dut.apb5_pwakeup.value = 1
        self.log.info("PWAKEUP asserted")
        await self.wait_clocks('aclk', cycles)
        self.dut.apb5_pwakeup.value = 0
        self.log.info("PWAKEUP deasserted")

    async def capture_monitor_output(self, timeout_cycles=10):
        """Capture monitor packet output."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if self.dut.monbus_valid.value:
                packet = int(self.dut.monbus_packet.value)
                self.monitor_packets.append(packet)
                self.log.info(f"Monitor packet captured: 0x{packet:016X}")
