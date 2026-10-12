# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: AXIS5SlaveBasicTB
# Purpose: Testbench for axis5_slave
# Subsystem: framework
#
# Extracted from val/amba/test_axis5_slave.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
from cocotb.triggers import Timer, RisingEdge
from TBClasses.shared.tbbase import TBBase
from TBClasses.axis5.axis5_chk_mixin import AXIS5ChkMixin


class AXIS5SlaveBasicTB(AXIS5ChkMixin, TBBase):
    """Basic AXIS5 slave testbench for RTL verification."""

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
        self.log.info(" AXIS5 Slave Testbench Configuration")
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

    async def drive_axis_packet(self, data, last=1, id=0, dest=0, user=0, wakeup=0, strb=None,
                         corrupt=None):
        """Drive a packet through the AXIS slave interface."""
        # Fit sideband values to the pin (a removed field is a 1-bit tie)
        id &= (1 << max(self.ID_WIDTH, 1)) - 1
        dest &= (1 << max(self.DEST_WIDTH, 1)) - 1
        user &= (1 << max(self.USER_WIDTH, 1)) - 1
        # Wait for ready
        while not int(self.dut.s_axis_tready.value):
            await RisingEdge(self.dut.aclk)

        # Drive AXIS signals
        self.dut.s_axis_tvalid.value = 1
        self.dut.s_axis_tdata.value = data
        self.dut.s_axis_tlast.value = last
        self.dut.s_axis_tstrb.value = strb if strb else (1 << self.STRB_WIDTH) - 1

        if hasattr(self.dut, 's_axis_tid'):
            self.dut.s_axis_tid.value = id
        if hasattr(self.dut, 's_axis_tdest'):
            self.dut.s_axis_tdest.value = dest
        if hasattr(self.dut, 's_axis_tuser'):
            self.dut.s_axis_tuser.value = user
        if hasattr(self.dut, 's_axis_twakeup'):
            self.dut.s_axis_twakeup.value = wakeup

        # IHI 0051B ch. 5 payload check signals (odd parity); `corrupt` maps a
        # field to an XOR mask for error injection
        if self.ENABLE_PARITY:
            strb_v = strb if strb else (1 << self.STRB_WIDTH) - 1
            self.drive_payload_chk('s_axis_', {'data': data, 'strb': strb_v, 'last': last,
                                              'id': id, 'dest': dest, 'user': user},
                                   corrupt)

        await RisingEdge(self.dut.aclk)
        self.dut.s_axis_tvalid.value = 0

        self.log.info(f"AXIS packet sent: data=0x{data:08X}, last={last}, wakeup={wakeup}")

    async def wait_for_fub_transaction(self, timeout_cycles=100):
        """Wait for FUB transaction to complete."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.fub_axis_tvalid.value) and int(self.dut.fub_axis_tready.value):
                return True
        return False

    # ------------------------------------------------------------------
    # IHI 0051B ch. 5 interface parity (ENABLE_PARITY=1)
    # ------------------------------------------------------------------

    async def run_chk_test(self, num_beats=24):
        """
        Directed check-signal test for the s_axis side.

        1. Odd-parity beats with TVALIDCHK/TWAKEUPCHK driven correctly never
           set parity_error; TREADYCHK = ~TREADY every cycle; the payload
           checks arrive at fub_axis still odd.
        2. A corrupted TSTRBCHK sets parity_error.
        3. A TVALIDCHK equal to TVALID sets parity_error.
        """
        import random
        d = self.dut
        rng = random.Random(int(os.environ.get('SEED', '1')))
        vmirror = self.start_chk_mirror(d.aclk, 's_axis_', 'valid')
        self.start_chk_mirror(d.aclk, 's_axis_', 'wakeup')
        # TVALIDCHK/TWAKEUPCHK are checked from reset release (Check Enable =
        # ARESETn): their drivers run first, then reset.
        await self.assert_reset()
        await self.deassert_reset()
        d.fub_axis_tready.value = 1
        await self.wait_clocks('aclk', 2)

        checked = 0
        for i in range(num_beats):
            await self.drive_axis_packet(
                data=rng.getrandbits(self.DATA_WIDTH), last=rng.getrandbits(1),
                id=rng.getrandbits(max(self.ID_WIDTH, 1)),
                dest=rng.getrandbits(max(self.DEST_WIDTH, 1)),
                user=rng.getrandbits(max(self.USER_WIDTH, 1)),
                wakeup=rng.getrandbits(1) if self.ENABLE_WAKEUP else 0)
            for _ in range(4):
                await RisingEdge(d.aclk)
                ctrl = self.ctrl_chk_mismatches('s_axis_', ('ready',))
                assert not ctrl, f"TREADYCHK wrong: {ctrl}"
                if int(d.fub_axis_tvalid.value) and int(d.fub_axis_tready.value):
                    bad = self.payload_chk_mismatches('fub_axis_')
                    assert not bad, f"beat {i}: {bad}"
                    checked += 1
        assert checked >= num_beats, f"only {checked}/{num_beats} beats checked"
        assert int(d.parity_error.value) == 0, "parity_error set on correct odd-parity traffic"
        self.log.info(f"{checked} beats: every check odd, parity_error clear")

        # Injection 1: one bad TSTRBCHK bit
        await self.drive_axis_packet(data=0xA5A5A5A5, last=1, corrupt={'strb': 0x1})
        await self.wait_clocks('aclk', 3)
        assert int(d.parity_error.value) == 1, "corrupted TSTRBCHK not detected"

        # Injection 2: TVALIDCHK == TVALID while idle (reset first: sticky)
        await self.assert_reset()
        await self.deassert_reset()
        await self.wait_clocks('aclk', 3)
        assert int(d.parity_error.value) == 0
        vmirror.cancel()
        d.s_axis_tvalidchk.value = int(d.s_axis_tvalid.value)
        await self.wait_clocks('aclk', 3)
        assert int(d.parity_error.value) == 1, "bad TVALIDCHK not detected"
        self.log.info("Injected TSTRBCHK and TVALIDCHK errors both detected")
