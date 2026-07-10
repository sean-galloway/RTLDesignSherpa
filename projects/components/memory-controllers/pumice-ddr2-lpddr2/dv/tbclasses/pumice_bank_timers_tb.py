# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Testbench for `pumice_bank_timers` (open-page per-bank safe timers).

Headline check: after a non-AP RD/WR the bank stays ACTIVE and rdwr_ready
stays HIGH (column commands stream at tCCD, gated globally) — unlike the old
closed-page xbank_timers which dropped rdwr_ready for tRTP/tWR.
Also: tRCD gate, pre_ready gating (tRAS + tRTP/tWR), explicit PRE -> tRP/tRC ->
act_ready, and auto-precharge (RDA) returning the bank to IDLE with no PRE.
"""

import os
import sys
import subprocess

import cocotb
from cocotb.triggers import RisingEdge

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402

BANK_IDLE, BANK_ACTIVATING, BANK_ACTIVE, BANK_RD_BUSY, BANK_WR_BUSY, BANK_PRECHARGING = range(6)


class PumiceBankTimersTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_BANKS = self.convert_to_int(os.environ.get('NUM_BANKS', '8'))
        self.ROW_WIDTH = self.convert_to_int(os.environ.get('ROW_WIDTH', '14'))
        # timing (cycles)
        self.T_RCD = 3
        self.T_RP  = 3
        self.T_RAS = 5
        self.T_RC  = 8
        self.T_WR  = 4
        self.T_RTP = 2

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        self._drive_idle()
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 3)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def _drive_idle(self):
        self.dut.t_rcd_i.value = self.T_RCD
        self.dut.t_rp_i.value = self.T_RP
        self.dut.t_ras_i.value = self.T_RAS
        self.dut.t_rc_i.value = self.T_RC
        self.dut.t_wr_i.value = self.T_WR
        self.dut.t_rtp_i.value = self.T_RTP
        self.dut.evt_act_i.value = 0
        self.dut.evt_rd_i.value = 0
        self.dut.evt_wr_i.value = 0
        self.dut.evt_pre_i.value = 0
        self.dut.evt_ap_i.value = 0
        self.dut.evt_rank_i.value = 0
        self.dut.evt_bank_i.value = 0
        self.dut.evt_row_i.value = 0

    # ---- per-bank readout ---------------------------------------------------
    def _bit(self, sig, bank):
        return (int(sig.value) >> bank) & 1

    def act_ready(self, b):  return self._bit(self.dut.bank_act_ready_o, b)
    def rdwr_ready(self, b): return self._bit(self.dut.bank_rdwr_ready_o, b)
    def pre_ready(self, b):  return self._bit(self.dut.bank_pre_ready_o, b)
    def row_active(self, b): return self._bit(self.dut.bank_row_active_o, b)

    def state(self, b):
        return (int(self.dut.bank_state_o.value) >> (b * 3)) & 0x7

    def open_row(self, b):
        return (int(self.dut.bank_open_row_o.value) >> (b * self.ROW_WIDTH)) \
            & ((1 << self.ROW_WIDTH) - 1)

    # ---- event drivers (1-cycle strobes) ------------------------------------
    async def _pulse(self, **kw):
        for k, v in kw.items():
            getattr(self.dut, k).value = v
        await RisingEdge(self.dut.aclk)
        for k in kw:
            if k.startswith('evt_') and k.endswith('_i') and 'rank' not in k \
               and 'bank' not in k and 'row' not in k:
                getattr(self.dut, k).value = 0

    async def act(self, bank, row):
        await self._pulse(evt_act_i=1, evt_bank_i=bank, evt_row_i=row)

    async def rd(self, bank, ap=0):
        await self._pulse(evt_rd_i=1, evt_bank_i=bank, evt_ap_i=ap)

    async def wr(self, bank, ap=0):
        await self._pulse(evt_wr_i=1, evt_bank_i=bank, evt_ap_i=ap)

    async def pre(self, bank):
        await self._pulse(evt_pre_i=1, evt_bank_i=bank)
