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
from TBClasses.axis5.axis5_chk_mixin import AXIS5ChkMixin


class AXIS5MasterCGBasicTB(AXIS5ChkMixin, TBBase):
    """Basic AXIS5 master clock-gated testbench."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.SKID_DEPTH = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH', '4'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.ENABLE_WAKEUP = self.convert_to_int(os.environ.get('TEST_ENABLE_WAKEUP', '1')) == 1
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        # The runner does not override these: the RTL defaults
        self.ID_WIDTH, self.DEST_WIDTH, self.USER_WIDTH = 8, 4, 1

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

    # ------------------------------------------------------------------
    # IHI 0051B ch. 5 interface parity (ENABLE_PARITY=1)
    # ------------------------------------------------------------------

    async def run_chk_test(self):
        """
        Check signals through the clock-gated master: odd T*CHK on m_axis5,
        TVALIDCHK/TWAKEUPCHK = inversions while running AND while gated, and
        a corrupted TUSERCHK sets parity_error.
        """
        d = self.dut
        self.start_chk_mirror(d.aclk, 'm_axis5_', 'ready')
        d.cfg_cg_enable.value = 0
        d.cfg_cg_idle_count.value = 4
        d.m_axis5_tready.value = 1
        d.fub_axis5_tvalid.value = 0
        d.fub_axis5_twakeup.value = 0
        await self.assert_reset()
        await self.deassert_reset()

        beats = [dict(data=0x00000001, strb=0xF, last=0, id=0x81, dest=0x3, user=1),
                 dict(data=0xFFFF0000, strb=0x3, last=1, id=0x00, dest=0xF, user=0)]
        seen = 0
        for b in beats:
            assert await self.drive_beat(d.aclk, 'fub_axis5_', b), "FUB beat not accepted"
            for _ in range(4):
                await RisingEdge(d.aclk)
                bad = self.ctrl_chk_mismatches('m_axis5_', ('valid', 'wakeup'))
                assert not bad, bad
                if int(d.m_axis5_tvalid.value) and int(d.m_axis5_tready.value):
                    bad = self.payload_chk_mismatches('m_axis5_')
                    assert not bad, bad
                    seen += 1
        assert seen == len(beats), f"saw {seen}/{len(beats)} beats on m_axis5"

        # Gate the clock: the outputs still carry consistent checks
        d.cfg_cg_enable.value = 1
        for _ in range(60):
            await RisingEdge(d.aclk)
            if int(d.cg_gating.value):
                break
        assert int(d.cg_gating.value) == 1, "clock never gated"
        bad = self.ctrl_chk_mismatches('m_axis5_', ('valid', 'wakeup'))
        assert not bad, f"while gated: {bad}"
        d.cfg_cg_enable.value = 0
        await self.wait_clocks('aclk', 3)
        assert int(d.parity_error.value) == 0, "parity_error set on correct traffic"

        assert await self.drive_beat(d.aclk, 'fub_axis5_', beats[0], corrupt={'user': 1})
        await self.wait_clocks('aclk', 4)
        assert int(d.parity_error.value) == 1, "corrupted TUSERCHK not detected"
        self.log.info("master_cg: checks odd running and gated; TUSERCHK error detected")
