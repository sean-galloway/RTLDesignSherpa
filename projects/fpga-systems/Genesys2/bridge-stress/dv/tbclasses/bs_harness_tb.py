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

AXI5 coverage: a passing verdict is only worth something if the AXI5 features
were exercised, and the verdict cannot see that (a host write that failed to
enable atomics would pass every check). So every AXI5 master port's pins are
counted per run -- atomics by class and their read-returns, AxIDUNQ, poisoned
W / R beats -- and a run that should have produced one and did not fails.

build-xil (vendor ports): the AMD/Xilinx IP is not simulated. Each vendor
slave (a real memory on the board) is the framework's AXI4 slave BFM with a
memory model, each vendor master is held idle, the vendor control windows
are left unanswered (the host does not drive them here) and EXT_STS0 reports
DDR3 calibrated. What this proves is the harness plumbing, the mem windows
through the bridge and the fill / read sweeps; the BFM models aligned INCR
only, so build-xil sims run the clean profile.
"""
from __future__ import annotations

from collections import Counter

import os

import cocotb
from cocotb._bridge import bridge
from cocotb.triggers import RisingEdge

from TBClasses.harness.cocotb_axil_bridge import make_uart_channel
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd, create_axi4_slave_wr)

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
        self.mems: dict[str, MemoryModel] = {}
        self._vendor_bfms: list = []
        # wall-clock bound on one run's ALL_DONE poll (a hang must fail, not spin)
        self.timeout_s = float(os.environ.get('BS_TIMEOUT_S', '1200'))

    # ---- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self):
        self.dut.i_uart_rx.value = 1
        await self.start_clock('aclk', self.aclk_ps, 'ps')
        await self.start_clock('cclk', self.cclk_ps, 'ps')
        self._vendor_ports()
        await self.assert_reset()
        await self.wait_clocks('aclk', 20)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 20)
        self.go_widths: list[int] = []
        self.go_c_count = 0
        cocotb.start_soon(self._watch_go_a())
        cocotb.start_soon(self._watch_go_c())
        self.cov: dict[str, Counter] = {m.name: Counter() for m in self.build.masters}
        for m in self.build.masters:
            if m.protocol == 'axi5':
                cocotb.start_soon(self._watch_axi5(m))

    def _vendor_ports(self) -> None:
        """build-xil: BFM memories on the vendor slaves, idle vendor masters."""
        d = self.dut
        for s in self.build.memories:
            mem = MemoryModel(num_lines=(1 << s.mem_lg2) // (s.dw // 8),
                              bytes_per_line=s.dw // 8, log=self.log)
            self.mems[s.name] = mem
            kw = dict(dut=d, clock=d.aclk, prefix=f'{s.name}_axi', log=self.log,
                      id_width=s.iw, addr_width=32, data_width=s.dw, user_width=1,
                      memory_model=mem, base_addr=s.base)
            self._vendor_bfms += [create_axi4_slave_rd(**kw), create_axi4_slave_wr(**kw)]
        for m in self.build.masters:
            if not m.vendor:
                continue
            for n in ('awvalid', 'wvalid', 'arvalid'):
                getattr(d, f'{m.name}_axi_{n}').value = 0
            for n in ('bready', 'rready'):
                getattr(d, f'{m.name}_axi_{n}').value = 1
        if any(p.vendor for p in self.build.masters + self.build.slaves):
            for x in ('ext0', 'ext1'):
                for n in ('awready', 'wready', 'bvalid', 'arready', 'rvalid'):
                    getattr(d, f'{x}_axil_{n}').value = 0
            d.i_ext_sts.value = 1                  # EXT_STS0[0]: DDR3 calibrated

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

    def _sig(self, name: str):
        return getattr(self.dut, name)

    async def _watch_axi5(self, m):
        """Count what one AXI5 master port actually carried (aclk ports only:
        an AXI5 port cannot be a cdc port)."""
        p = f'{m.name}_axi_'
        f = set(m.features)
        c = self.cov[m.name]
        s = {n: self._sig(p + n) for n in
             ('awvalid', 'awready', 'arvalid', 'arready', 'wvalid', 'wready',
              'rvalid', 'rready', 'rid')}
        if 'atomic' in f:
            s['awatop'] = self._sig(p + 'awatop')
        if 'unique' in f:
            s['awidunq'] = self._sig(p + 'awidunq')
            s['aridunq'] = self._sig(p + 'aridunq')
        if 'poison' in f:
            s['wpoison'] = self._sig(p + 'wpoison')
            s['rpoison'] = self._sig(p + 'rpoison')
        if 'mte' in f:
            for n in ('awtagop', 'artagop', 'bvalid', 'bready', 'btagmatch'):
                s[n] = self._sig(p + n)
        msb = 1 << (m.iw - 1)
        while True:
            await RisingEdge(self.dut.aclk)
            v = {k: int(x.value) for k, x in s.items()}
            if v['awvalid'] and v['awready']:
                atop = v.get('awatop', 0)
                if atop:
                    c['atomic'] += 1
                    c['atomic_' + bstress.M.atop_class(atop)] += 1
                    c['atomic_rr'] += (atop >> 5) & 1
                c['awidunq'] += v.get('awidunq', 0)
                if 'mte' in f:
                    c[f"awtagop{v['awtagop']}"] += 1
            if v['arvalid'] and v['arready']:
                c['aridunq'] += v.get('aridunq', 0)
                if 'mte' in f:
                    c[f"artagop{v['artagop']}"] += 1
            if 'mte' in f and v['bvalid'] and v['bready']:
                c[f"btagmatch{v['btagmatch']}"] += 1
            if v['wvalid'] and v['wready']:
                c['wpoison'] += v.get('wpoison', 0)
            if v['rvalid'] and v['rready']:
                c['rpoison'] += v.get('rpoison', 0)
                if 'atomic' in f and (v['rid'] & msb):
                    c['atomic_r'] += 1

    def check_cov(self, prof, label: str) -> None:
        """Fail a run whose AXI5 features never reached the pins."""
        for m in self.build.masters:
            if m.protocol != 'axi5':
                continue
            c, f, miss = self.cov[m.name], set(m.features), []
            if 'atomic' in f and prof.wr and prof.atom_lg2:
                if not c['atomic']:
                    miss.append('no atomic issued')
                if c['atomic_r'] != c['atomic_rr']:
                    miss.append(f"{c['atomic_rr']} read-return atomics, "
                                f"{c['atomic_r']} R beats for them")
            # single_id keeps every burst on one ID, which is then almost never
            # idle, and AxIDUNQ is legal only on an idle ID
            if ('unique' in f and not prof.single_id
                    and not (c['awidunq'] if prof.wr else 0) + (c['aridunq'] if prof.rd else 0)):
                miss.append('no AxIDUNQ issued')
            if 'mte' in f:
                kinds = ((['awtagop1', 'awtagop2', 'awtagop3'] if prof.wr else [])
                         + (['artagop1', 'artagop3'] if prof.rd else []))
                gone = [k for k in kinds if not c[k]]
                if gone:
                    miss.append(f'MTE never issued {gone}')
            if 'poison' in f and prof.poison_lg2:
                if prof.wr and not c['wpoison']:
                    miss.append('no poisoned W beat')
                if prof.rd and not c['rpoison']:
                    miss.append('no poisoned R beat')
            self.log.info(f'{label} {m.name} AXI5 coverage: {dict(c)}')
            if miss:
                self.failures.append(f'{label}: {m.name}: ' + '; '.join(miss))

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
        for c in self.cov.values():
            c.clear()
        res = await bridge(lambda: self.h.run(prof, seed, txns, timeout_s=self.timeout_s,
                                              sleep=lambda s: None))()
        ok, why = self.h.verdict(res)
        n0 = len(self.failures)
        self.check_cov(prof, f'{profile}/{seed}')
        if len(self.failures) > n0:
            ok = False
            why = list(why) + self.failures[n0:]
            del self.failures[n0:]
        self.log.info(f'GO pulses so far: widths {self.go_widths}, cclk arrivals {self.go_c_count}')
        self.log.info(self.h.summary(res, 1e12 / self.aclk_ps))
        if ok:
            self.log.info(f'PASS {profile} seed={seed}')
        else:
            for w in why:
                self.log.error(f'FAIL {profile} seed={seed}: {w}')
            self.failures.append(f'{profile}/{seed}: ' + '; '.join(why))
        return ok
