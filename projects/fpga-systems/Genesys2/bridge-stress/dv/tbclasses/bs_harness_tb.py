# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""bs_harness testbench: the board's host library, over the sim UART.

The harness top (rtl/generated/bs_harness_<dut>/) is simulated whole -- UART
host link, configuration bridge, every stress block and the DUT bridge -- and
driven by bin/bstress.py, the same code the board program runs, through
UARTAxiBridge on a cocotb UART channel. A pass here is the same verdict the
board gives: StressHarness.verdict() over the registers read back by name.

aclk (the DUT clock) and cclk (the clock of every cdc port) are asynchronous:
100 MHz and 75 MHz, as on the board.
"""
from __future__ import annotations

import os

import cocotb
from cocotb._bridge import bridge
from cocotb.triggers import RisingEdge

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel
from TBClasses.shared.tbbase import TBBase

import bstress
from uart_axi_bridge import UARTAxiBridge


class BsHarnessTB(TBBase):
    def __init__(self, dut, toml: str):
        super().__init__(dut)
        self.aclk_ps = int(os.environ.get('ACLK_PERIOD_PS', '10000'))
        self.cclk_ps = int(os.environ.get('CCLK_PERIOD_PS', '13334'))
        self.clks_per_bit = int(os.environ.get('CLKS_PER_BIT', '4'))
        self.channel = make_uart_channel(dut, dut.aclk, self.clks_per_bit,
                                         rx_signal='i_uart_rx', tx_signal='o_uart_tx',
                                         log=self.log)
        self.bus = UARTAxiBridge(channel=self.channel)
        self.build = bstress.load_build(toml)
        self.h = bstress.StressHarness(self.bus, self.build,
                                       log=lambda m, _l=self.log: _l.info(m))
        self.failures: list[str] = []
        # wall-clock bound on one run's ALL_DONE poll (a hang must fail, not spin)
        self.timeout_s = float(os.environ.get('BS_TIMEOUT_S', '1200'))

    # ---- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self):
        self.dut.i_uart_rx.value = 1
        await self.start_clock('aclk', self.aclk_ps, 'ps')
        await self.start_clock('cclk', self.cclk_ps, 'ps')
        await self.assert_reset()
        await self.wait_clocks('aclk', 20)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 20)
        self.go_widths: list[int] = []
        self.go_c_count = 0
        cocotb.start_soon(self._watch_go_a())
        cocotb.start_soon(self._watch_go_c())

    # GO reaches cclk through a toggle synchronizer: a GO wider than one aclk
    # cycle toggles it twice and the cclk blocks never start. Every GO must be
    # one cycle wide and arrive in cclk exactly once.
    async def _watch_go_a(self):
        w = 0
        while True:
            await RisingEdge(self.dut.aclk)
            if int(self.dut.go_a.value):
                w += 1
            elif w:
                self.go_widths.append(w)
                w = 0

    async def _watch_go_c(self):
        while True:
            await RisingEdge(self.dut.cclk)
            self.go_c_count += int(self.dut.go_c.value)

    def check_go(self) -> None:
        bad = [w for w in self.go_widths if w != 1]
        if bad or self.go_c_count != len(self.go_widths):
            self.failures.append(f'GO: aclk pulse widths {self.go_widths}, '
                                 f'{self.go_c_count} arrived in cclk')

    async def assert_reset(self):
        self.dut.aresetn.value = 0
        self.dut.cresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1
        self.dut.cresetn.value = 1

    # ---- the board's library --------------------------------------------------
    async def identify(self):
        await bridge(self.h.identify)()

    async def run(self, profile: str, seed: int, txns: int) -> bool:
        prof = bstress.PROFILES[profile]
        if os.environ.get('BS_BURSTS'):          # e.g. 2 = INCR only, for triage
            prof = bstress.replace(prof, bursts=int(os.environ['BS_BURSTS'], 0))
        if os.environ.get('BS_FULL_AXI') == '1':  # lift path_caps (bridge BUG-018 repro)
            prof = bstress.replace(prof, full_axi=True)
        res = await bridge(lambda: self.h.run(prof, seed, txns, timeout_s=self.timeout_s,
                                              sleep=lambda s: None))()
        ok, why = self.h.verdict(res)
        self.log.info(f'GO pulses so far: widths {self.go_widths}, cclk arrivals {self.go_c_count}')
        self.log.info(self.h.summary(res, 1e12 / self.aclk_ps))
        if ok:
            self.log.info(f'PASS {profile} seed={seed}')
        else:
            for w in why:
                self.log.error(f'FAIL {profile} seed={seed}: {w}')
            self.failures.append(f'{profile}/{seed}: ' + '; '.join(why))
        return ok
