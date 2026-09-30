"""
rs_error_injector testbench

GAXIMaster drives `in_` with coded blocks (any symbols will do: the injector
does not decode), GAXISlave drains `out_`, and the difference between the two
symbol streams is scored against the configured mode:

  COUNT  exactly e differing symbols per block, all differences nonzero
  BURST  exactly e differing symbols, at consecutive positions
  RATE   the differing fraction over many blocks is near rate / 65536
  NONE   no differences

and the statistics outputs must agree with what was observed.

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import os
import random

from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class RSInjectorTB(TBBase):
    BLOCKS = {'gate': 4, 'func': 16, 'full': 64}
    NONE, COUNT, BURST, RATE = 0, 1, 2, 3

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.BLOCKS:
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.M = int(dut.SYMBOL_WIDTH.value)
        self.T = int(dut.T_SYMBOLS.value)
        self.N = int(dut.N_SYMBOLS.value)
        self.S = int(dut.SYMBOLS_PER_BEAT.value)
        self.Q = 1 << self.M
        self.checks = 0
        self.mismatches = 0
        self._init_bfms()

    def _init_bfms(self):
        for prefix, attr in (("in_", "master"), ("out_", "slave")):
            fc = FieldConfig()
            fc.add_field(FieldDefinition(name='data', bits=self.M * self.S, default=0))
            fc.add_field(FieldDefinition(name='keep', bits=self.S, default=(1 << self.S) - 1))
            fc.add_field(FieldDefinition(name='last', bits=1, default=0))
            cls = GAXIMaster if attr == "master" else GAXISlave
            setattr(self, attr, cls(dut=self.dut, title=prefix.upper(), prefix=prefix, clock=self.clk,
                                    field_config=fc, pkt_prefix="", multi_sig=True, log=self.log))
        cfg = quick_config(profiles=['constrained'], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg['constrained'])
        self.slave.set_randomizer(cfg['constrained'])

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        d = self.dut
        d.cfg_mode.value = 0
        d.cfg_count.value = 0
        d.cfg_rate.value = 0
        d.cfg_seed.value = 0xACE1
        d.cfg_seed_load.value = 0
        d.cfg_clear.value = 0
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 2)

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 10:
                self.log.error(f"{what}: got {got} expected {exp}")

    async def configure(self, mode, count=0, rate=0, seed=0xACE1):
        d = self.dut
        d.cfg_mode.value = mode
        d.cfg_count.value = count
        d.cfg_rate.value = rate
        d.cfg_seed.value = seed
        d.cfg_seed_load.value = 1
        d.cfg_clear.value = 1
        await RisingEdge(self.clk)
        d.cfg_seed_load.value = 0
        d.cfg_clear.value = 0
        await RisingEdge(self.clk)

    def beats_of(self, symbols):
        beats = []
        for i in range(0, len(symbols), self.S):
            chunk = symbols[i:i + self.S]
            data = 0
            for u, sym in enumerate(chunk):
                data |= sym << (u * self.M)
            beats.append((data, (1 << len(chunk)) - 1))
        return beats

    async def pass_block(self, symbols):
        beats = self.beats_of(symbols)
        for i, (dat, keep) in enumerate(beats):
            await self.master._driver_send(self.master.create_packet(
                data=dat, keep=keep, last=1 if i == len(beats) - 1 else 0), sync=True)
        waited = 0
        while len(self.slave._recvQ) < len(beats):
            await RisingEdge(self.clk)
            waited += 1
            if waited > 50 * len(beats) + 500:
                self.log.error("timeout waiting for the block")
                self.mismatches += 1
                break
        out = []
        while self.slave._recvQ:
            p = self.slave._recvQ.popleft()
            for u in range(self.S):
                if int(p.keep) >> u & 1:
                    out.append((int(p.data) >> (u * self.M)) & (self.Q - 1))
        return out

    def stats(self):
        d = self.dut
        return dict(symbols=int(d.o_inj_symbols.value), blocks=int(d.o_inj_blocks.value),
                    over_t=int(d.o_inj_over_t.value), last=int(d.o_last_block_errors.value))

    async def run_mode(self, mode, count=0, rate=0):
        await self.configure(mode, count, rate, seed=random.randrange(1, 1 << 32))
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        if mode == self.RATE:
            # a statistical check needs a sample: at least 2000 symbols
            n_blocks = max(n_blocks, (2000 + self.N - 1) // self.N)
        total = 0
        blocks_hit = 0
        over_t = 0
        last_e = 0
        for b in range(n_blocks):
            symbols = [random.randrange(self.Q) for _ in range(self.N)]
            out = await self.pass_block(symbols)
            self._score(f"mode {mode} block {b} length", len(out), self.N)
            if len(out) != self.N:
                continue
            diff = [j for j in range(self.N) if out[j] != symbols[j]]
            e = len(diff)
            total += e
            blocks_hit += 1 if e else 0
            over_t += 1 if e > self.T else 0
            last_e = e
            if mode == self.NONE:
                self._score(f"none block {b} differences", e, 0)
            elif mode == self.COUNT:
                self._score(f"count block {b} differences", e, count)
            elif mode == self.BURST:
                self._score(f"burst block {b} differences", e, count)
                if e:
                    self._score(f"burst block {b} consecutive", diff, list(range(diff[0], diff[0] + e)))
        if mode == self.RATE:
            # Bernoulli count: mean p*n, sigma sqrt(p*n*(1-p)); allow 4 sigma. The
            # lane LFSRs shift one bit per beat, so consecutive draws are
            # correlated and the true variance is somewhat above binomial.
            n_sym = self.N * n_blocks
            pr = rate / 65536
            expected = pr * n_sym
            sigma = (pr * n_sym * (1 - pr)) ** 0.5
            self.checks += 1
            if abs(total - expected) > 4 * sigma + 2:
                self.mismatches += 1
                self.log.error(f"rate: {total} differences, expected {expected:.0f} +- {4 * sigma:.0f}")
            else:
                self.log.info(f"rate: {total} differences over {n_sym} symbols, expected {expected:.0f} "
                              f"(sigma {sigma:.1f})")
        # the statistics must match what the stream showed
        await self.wait_clocks(self.clk_name, 2)
        st = self.stats()
        self._score(f"mode {mode} stats symbols", st['symbols'], total)
        self._score(f"mode {mode} stats blocks", st['blocks'], blocks_hit)
        self._score(f"mode {mode} stats over_t", st['over_t'], over_t)
        self._score(f"mode {mode} stats last", st['last'], last_e)
        return self.mismatches == 0

    async def run_all(self):
        ok = True
        ok &= await self.run_mode(self.NONE)
        for e in (1, self.T, self.T + 1, min(self.N, 2 * self.T + 3)):
            ok &= await self.run_mode(self.COUNT, count=e)
        ok &= await self.run_mode(self.BURST, count=self.T)
        ok &= await self.run_mode(self.RATE, rate=int(0.10 * 65536))
        return ok

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
