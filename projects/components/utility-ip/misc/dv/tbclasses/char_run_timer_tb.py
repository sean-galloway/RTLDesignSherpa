# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""char_run_timer testbench: every output, every cycle, against a model.

The model is the module header's protocol written out cycle by cycle: START on
a rising edge of i_start, STOP when the registered write count reaches the
registered target, PASS = the CRC verdict SETTLE_CYCLES after STOP, stamps on
the registered counts. Stimulus is whole runs as a harness sees them -- a
start level held for a few cycles, read and write counts climbing at random
rates, CRCs that settle a cycle after the last beat -- plus clears mid-run,
second starts that must be ignored, an unarmed target, and runs whose CRC is
corrupted on one channel (any channel, ch0 included) so they must FAIL.

A pass must have shown both verdicts: at least one run done with pass=1 and
one done with pass=0, and the cycle comparison count is reported.
"""
from __future__ import annotations

import os
import random

from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge

from TBClasses.shared.tbbase import TBBase

M64 = (1 << 64) - 1


class CharRunTimerModel:
    def __init__(self, nc: int, settle: int):
        self.nc, self.settle = nc, settle
        self.reset()

    def reset(self):
        self.start_d = 0
        self.rd_q = self.wr_q = self.exp_q = 0
        self.running = self.done = self.passed = 0
        self.cycles = self.settle_cnt = 0
        self.rf = self.rl = self.wf = self.wl = 0
        self.rfs = self.wfs = self.rls = self.wls = 0

    def verdict(self, rd_crc, rd_v, wr_crc, wr_v):
        vmask = rd_v & wr_v
        mmask = sum(1 << c for c in range(self.nc)
                    if (vmask >> c) & 1 and rd_crc[c] == wr_crc[c])
        any_v = int(vmask != 0)
        match = int(any_v and not (vmask & ~mmask))
        return vmask, mmask, any_v, match

    def step(self, inp: dict):
        """Advance one rising edge with the inputs that were stable before it."""
        _, _, _, match = self.verdict(inp['rd_crc'], inp['rd_v'], inp['wr_crc'], inp['wr_v'])
        rise = inp['start'] and not self.start_d
        armed = self.exp_q != 0
        stop = armed and self.wr_q >= self.exp_q
        rfn = self.running and not self.rfs and self.rd_q != 0
        wfn = self.running and not self.wfs and self.wr_q != 0
        rln = self.running and not self.rls and armed and self.rd_q >= self.exp_q
        wln = self.running and not self.wls and stop
        if inp['clear']:
            keep = (self.start_d, self.rd_q, self.wr_q, self.exp_q)
            self.reset()
            self.start_d, self.rd_q, self.wr_q, self.exp_q = keep
        elif self.running:
            if rfn:
                self.rf, self.rfs = self.cycles, 1
            if wfn:
                self.wf, self.wfs = self.cycles, 1
            if rln:
                self.rl, self.rls = self.cycles, 1
            if wln:
                self.wl, self.wls = self.cycles, 1
            if stop:
                self.running, self.settle_cnt = 0, 1
            else:
                self.cycles = (self.cycles + 1) & M64
        elif self.settle_cnt:
            if self.settle_cnt == self.settle:
                self.settle_cnt, self.done, self.passed = 0, 1, match
            else:
                self.settle_cnt += 1
        elif not self.done and rise:
            self.running, self.cycles = 1, 1
        self.start_d = int(inp['start'])
        self.rd_q, self.wr_q, self.exp_q = inp['rd_beats'], inp['wr_beats'], inp['exp']


class CharRunTimerTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.nc = self.convert_to_int(os.environ.get('NUM_CHANNELS', '8'))
        self.settle = self.convert_to_int(os.environ.get('SETTLE_CYCLES', '5'))
        self.rng = random.Random(int(os.environ.get('SEED', '0')))
        self.model = CharRunTimerModel(self.nc, self.settle)
        self.errors: list[str] = []
        self.stats = {'cycles_checked': 0, 'runs': 0, 'pass1': 0, 'pass0': 0, 'clears': 0,
                      'verdict_cases': 0}
        self.inp = dict(clear=0, start=0, exp=0, rd_beats=0, wr_beats=0,
                        rd_crc=[0] * self.nc, rd_v=0, wr_crc=[0] * self.nc, wr_v=0)

    # ---- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self):
        self._drive()
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        await FallingEdge(self.dut.aclk)

    async def assert_reset(self):
        self.dut.aresetn.value = 0
        self.model.reset()

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- drive / check ------------------------------------------------------
    def _drive(self):
        d, i = self.dut, self.inp
        d.i_clear.value = i['clear']
        d.i_start.value = i['start']
        d.i_expected_beats.value = i['exp']
        d.i_rd_beat_count.value = i['rd_beats']
        d.i_wr_beat_count.value = i['wr_beats']
        d.i_rd_crc_value.value = sum(v << (32 * c) for c, v in enumerate(i['rd_crc']))
        d.i_wr_crc_value.value = sum(v << (32 * c) for c, v in enumerate(i['wr_crc']))
        d.i_rd_crc_valid.value = i['rd_v']
        d.i_wr_crc_valid.value = i['wr_v']

    async def cycle(self, **changes):
        """Drive at the falling edge, step the model over the rising edge, compare."""
        self.inp.update(changes)
        self._drive()
        await RisingEdge(self.dut.aclk)
        self.model.step(self.inp)
        await ReadOnly()
        self._compare()
        await FallingEdge(self.dut.aclk)

    def _compare(self):
        d, m = self.dut, self.model
        vm, mm, av, ma = m.verdict(self.inp['rd_crc'], self.inp['rd_v'],
                                   self.inp['wr_crc'], self.inp['wr_v'])
        want = {'o_crc_valid_mask': vm, 'o_crc_match_mask': mm, 'o_crc_any_valid': av,
                'o_crc_match': ma, 'o_running': m.running, 'o_done': m.done,
                'o_pass': m.passed, 'o_cycles': m.cycles, 'o_r_first': m.rf,
                'o_r_last': m.rl, 'o_w_first': m.wf, 'o_w_last': m.wl}
        self.stats['cycles_checked'] += 1
        for sig, exp in want.items():
            got = int(getattr(d, sig).value)
            if got != exp and len(self.errors) < 50:
                self.errors.append(f"t={self.stats['cycles_checked']} {sig}: got {got} want {exp}")

    # ---- scenarios ----------------------------------------------------------
    async def run_one(self, beats: int, corrupt: bool, clear_mid: bool, exp_zero: bool):
        """One run as a harness drives it, ending in a clear for the next one."""
        nc, rng = self.nc, self.rng
        active = rng.randrange(1, 1 << nc)
        await self.cycle(clear=1, start=0, exp=0 if exp_zero else beats, rd_beats=0, wr_beats=0,
                         rd_v=0, wr_v=0)
        await self.cycle(clear=0)
        for _ in range(rng.randrange(0, 4)):
            await self.cycle()
        crc = [rng.getrandbits(32) for _ in range(nc)]
        rd = wr = 0
        start_hold = rng.randrange(1, 4)
        restarted = False
        n = 0
        while wr < beats or n < 3:
            n += 1
            start = 1 if n <= start_hold else 0
            # a second start pulse mid-run must be ignored
            if not restarted and n > start_hold + 2 and rng.random() < 0.05:
                start, restarted = 1, True
            if n > start_hold:
                rd = min(beats, rd + rng.choice((0, 1, 1, 2)))
                wr = min(rd, wr + rng.choice((0, 1, 1, 2)))
            last = wr >= beats
            # CRCs settle a cycle after the last beat, as dataint_crc's register does
            rv = active if rd >= beats else 0
            wv = active if last and n > 1 else 0
            wcrc = list(crc)
            if corrupt and last:
                victim = rng.choice([c for c in range(nc) if (active >> c) & 1])
                wcrc[victim] ^= 1 << rng.randrange(32)
            await self.cycle(start=start, rd_beats=rd, wr_beats=wr, rd_crc=crc, rd_v=rv,
                             wr_crc=wcrc, wr_v=wv)
            if clear_mid and n == beats // 2:
                self.stats['clears'] += 1
                await self.cycle(clear=1, start=0)
                await self.cycle(clear=0)
                return
        for _ in range(self.settle + 4):
            await self.cycle(start=0)
        self.stats['runs'] += 1
        if self.model.done:
            self.stats['pass1' if self.model.passed else 'pass0'] += 1
            if self.model.passed == corrupt:
                self.errors.append(f"model verdict {self.model.passed} on a "
                                   f"{'corrupted' if corrupt else 'clean'} run")
        elif not exp_zero:
            self.errors.append(f"run of {beats} beats never reached done")

    async def run_verdict_sweep(self) -> bool:
        """Every channel in turn is the only mismatch, alone and among all-valid.

        Random corruption alone does not reach every channel at gate depth, and
        a verdict that ignores one channel (ch0 was once masked) passes it.
        """
        nc, rng = self.nc, self.rng
        full = (1 << nc) - 1
        for victim in range(nc):
            for active in (full, 1 << victim):
                crc = [rng.getrandbits(32) for _ in range(nc)]
                bad = list(crc)
                bad[victim] ^= 1 << rng.randrange(32)
                await self.cycle(rd_crc=crc, rd_v=active, wr_crc=bad, wr_v=active)
                if self.dut.o_crc_match.value != 0 or not (int(self.dut.o_crc_valid_mask.value) >> victim) & 1:
                    self.errors.append(f"verdict: ch{victim} mismatch with active 0x{active:X} not failed")
                await self.cycle(rd_crc=crc, rd_v=active, wr_crc=crc, wr_v=active)
                if self.dut.o_crc_match.value != 1:
                    self.errors.append(f"verdict: clean CRCs with active 0x{active:X} not matched")
                self.stats['verdict_cases'] += 2
        await self.cycle(rd_v=0, wr_v=0)
        return not self.errors

    async def run_all(self, runs: int) -> bool:
        if not await self.run_verdict_sweep():
            return False
        for k in range(runs):
            r = self.rng.random()
            await self.run_one(beats=self.rng.randrange(1, 200),
                               corrupt=r < 0.35,
                               clear_mid=0.35 <= r < 0.45,
                               exp_zero=0.45 <= r < 0.52)
            if self.errors:
                break
        return not self.errors

    def report(self) -> bool:
        self.log.info(f"char_run_timer NC={self.nc} SETTLE={self.settle}: {self.stats}")
        for e in self.errors[:20]:
            self.log.error(e)
        return not self.errors
