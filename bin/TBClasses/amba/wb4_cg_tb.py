# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Clock-gated Wishbone variants: the base master/slave testbenches plus the
three gating checks of the *_cg family, sampled every clock of the free
clock:

  gating never outlives pending work: work may appear while the clock is
  gated (a command offered, a cycle raised by the master) and the wake is
  registered once, so up to WAKE_CLOCKS clocks of overlap are legal, more
  is a stranded clock;
  gated after each phase drains (idle count + a few clocks), when enabled;
  never gated with cfg_cg_enable low.

`CG_ENABLE=0` runs the same traffic with gating disabled, which must be
indistinguishable from the base module.
"""
import os

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.amba.wb4_master_tb import WB4MasterTB
from TBClasses.amba.wb4_slave_tb import WB4SlaveTB


class _CGChecks:
    """Mixin: shares the gating checks between the master and slave TBs."""

    def _cg_init(self):
        self.cg_enable = os.environ.get('CG_ENABLE', '1') == '1'
        self.cg_idle_count = int(os.environ.get('CG_IDLE_COUNT', '4'))
        self.cg_stats = {'gated_clocks': 0, 'clocks': 0, 'gate_edges': 0, 'max_overlap': 0}
        self._cg_prev = 0
        self._overlap = 0
        self.WAKE_CLOCKS = 2      # wake term -> controller register -> ungate

    def _pre_reset(self):
        self.dut.cfg_cg_enable.value = int(self.cg_enable)
        self.dut.cfg_cg_idle_count.value = self.cg_idle_count

    def _cg_busy(self):
        """Work the clock must stay on for (the terms the wrapper wakes on)."""
        raise NotImplementedError

    async def cg_watch(self):
        d = self.dut
        while not getattr(self, 'done', False):
            await RisingEdge(self.clk)
            g = int(d.cg_gating.value)
            self.cg_stats['clocks'] += 1
            self.cg_stats['gated_clocks'] += g
            self.cg_stats['gate_edges'] += int(g and not self._cg_prev)
            self._cg_prev = g
            if g and not self.cg_enable:
                self.errors.append("clock gated with cfg_cg_enable low")
                self.cg_enable = True          # report once
            self._overlap = self._overlap + 1 if (g and self._cg_busy()) else 0
            self.cg_stats['max_overlap'] = max(self.cg_stats['max_overlap'], self._overlap)
            if self._overlap > self.WAKE_CLOCKS:
                self.errors.append(f"clock still gated {self._overlap} clocks after work appeared: "
                                   f"{self._cg_busy_str()}")
                break

    def _cg_busy_str(self):
        d = self.dut
        return (f"CYC={int(d.m_wb_CYC.value) if hasattr(d, 'm_wb_CYC') else int(d.s_wb_CYC.value)} "
                f"cmd_valid={int(d.cmd_valid.value)} rsp_valid={int(d.rsp_valid.value)}")

    async def expect_gated(self):
        """After a drain: the clock must gate within the idle count plus the
        controller's own latency; with gating disabled it must not."""
        for _ in range(self.cg_idle_count + 12):
            await RisingEdge(self.clk)
            if int(self.dut.cg_gating.value):
                break
        gated = int(self.dut.cg_gating.value)
        if self.cg_enable and not gated:
            self.errors.append(f"clock not gated {self.cg_idle_count + 12} clocks after the phase drained")
        if not self.cg_enable and gated:
            self.errors.append("clock gated with gating disabled")

    def cg_report(self):
        s = self.cg_stats
        self.log.info(f"clock gating: enable={self.cg_enable} idle_count={self.cg_idle_count} "
                      f"gated {s['gated_clocks']}/{s['clocks']} clocks, {s['gate_edges']} gate edges, "
                      f"longest gated-with-work overlap {s['max_overlap']} (limit {self.WAKE_CLOCKS})")


class WB4MasterCGTB(_CGChecks, WB4MasterTB):
    def __init__(self, dut):
        super().__init__(dut)
        self._cg_init()

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        cocotb.start_soon(self.cg_watch())

    def _cg_busy(self):
        d = self.dut
        return int(d.m_wb_CYC.value) or int(d.rsp_valid.value) or int(d.cmd_valid.value)


class WB4SlaveCGTB(_CGChecks, WB4SlaveTB):
    def __init__(self, dut):
        super().__init__(dut)
        self._cg_init()

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        cocotb.start_soon(self.cg_watch())

    def _cg_busy(self):
        d = self.dut
        return int(d.s_wb_CYC.value) or int(d.cmd_valid.value) or int(d.rsp_valid.value)
