"""
rs_beat_packer testbench

Feeds the packer the beat layout rs_encoder_core actually produces -- data
phase, then parity starting on a FRESH beat -- and requires the output to obey
rs_decoder_core's in_keep contract: partial only on the block's last beat.

What is checked, and why each one:

  symbols     the symbol SEQUENCE is unchanged. The packer only moves beat
              boundaries; if it reordered or dropped a symbol the codeword
              would be silently wrong, which is worse than a framing error.
  contract    no beat except the last is partial, and keep is low-aligned.
              This is the whole reason the block exists.
  count       the output is exactly ceil(total/S) beats. The encoder's layout
              can be LONGER -- RS(15,9) at S=4 is 5 beats in, 4 out -- so a
              packer that merely passed beats through would be caught here.
  boundaries  out_last lands on the last beat of every block and nowhere else,
              across several blocks back to back, so the flush does not leak
              one block's tail into the next.

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class RSBeatPackerTB(TBBase):
    """Drives the encoder's beat layout in and checks the decoder's contract out."""

    BLOCKS = {'gate': 3, 'func': 12, 'full': 40}
    PROFILES = {'gate': ['backtoback'],
                'func': ['backtoback', 'constrained'],
                'full': ['backtoback', 'constrained', 'bursty', 'slow']}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.m = self.convert_to_int(os.environ.get('SYMBOL_WIDTH', 8))
        self.s = self.convert_to_int(os.environ.get('SYMBOLS_PER_BEAT', 4))
        self.k = self.convert_to_int(os.environ.get('K_SYMBOLS', 239))
        self.t = self.convert_to_int(os.environ.get('T_SYMBOLS', 8))
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.dw = self.m * self.s
        self.checks = 0
        self.mismatches = 0
        self._init_bfms()

    def _init_bfms(self):
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='data', bits=self.dw, default=0))
        fc.add_field(FieldDefinition(name='keep', bits=self.s, default=(1 << self.s) - 1))
        fc.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="PK_IN", prefix="in_", clock=self.dut.aclk,
                                 field_config=fc, pkt_prefix="", multi_sig=True, log=self.log)
        fc2 = FieldConfig()
        fc2.add_field(FieldDefinition(name='data', bits=self.dw, default=0))
        fc2.add_field(FieldDefinition(name='keep', bits=self.s, default=0))
        fc2.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="PK_OUT", prefix="out_", clock=self.dut.aclk,
                               field_config=fc2, pkt_prefix="", multi_sig=True, log=self.log)

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('aclk', period_ns, 'ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    def set_profile(self, name):
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    def _fail(self, msg):
        self.mismatches += 1
        self.log.error(msg)

    # -- the layout the encoder core actually emits ---------------------------
    def encoder_beats(self, symbols):
        """Data phase, then parity starting on a FRESH beat -- measured, not assumed."""
        out, pos = [], 0
        for phase_len in (self.k, 2 * self.t):
            phase = symbols[pos:pos + phase_len]; pos += phase_len
            for i in range(0, len(phase), self.s):
                out.append(phase[i:i + self.s])
        return out

    def _pack_word(self, syms):
        w = 0
        for j, sym in enumerate(syms):
            w |= (sym & ((1 << self.m) - 1)) << (j * self.m)
        return w, (1 << len(syms)) - 1

    async def run_blocks(self, profile='backtoback'):
        self.checks += 1
        self.set_profile(profile)
        self.slave._recvQ.clear()
        rnd = random.Random(0xBEEF + self.k * 31 + sum(map(ord, profile)))
        blocks = self.BLOCKS[self.level]
        n = self.k + 2 * self.t

        sent_syms, in_beats = [], []
        for _ in range(blocks):
            syms = [rnd.randrange(1 << self.m) for _ in range(n)]
            sent_syms.append(syms)
            in_beats.append(self.encoder_beats(syms))

        async def feed():
            for blk in in_beats:
                for i, chunk in enumerate(blk):
                    w, keep = self._pack_word(chunk)
                    await self.master.send(self.master.create_packet(
                        data=w, keep=keep, last=int(i == len(blk) - 1)))
        cocotb.start_soon(feed())

        want_per_block = -(-n // self.s)
        want_total = want_per_block * blocks
        got, waited = [], 0
        limit = 200 * want_total + 5000
        while len(got) < want_total and waited < limit:
            if self.slave._recvQ:
                p = self.slave._recvQ.popleft()
                got.append((int(p.data), int(p.keep), int(p.last)))
            else:
                await RisingEdge(self.dut.aclk)
                waited += 1

        label = f"{profile} {blocks} x RS({n},{self.k})"
        if len(got) != want_total:
            self._fail(f"{label}: {len(got)} beats out, expected {want_total} "
                       f"(ceil({n}/{self.s}) = {want_per_block} per block). The encoder's "
                       f"layout was {len(in_beats[0])} beats per block.")
            return

        full = (1 << self.s) - 1
        for b in range(blocks):
            beats = got[b * want_per_block:(b + 1) * want_per_block]
            # contract: partial only on the last beat, and low-aligned
            for i, (_, keep, _) in enumerate(beats):
                if keep & (keep + 1):
                    self._fail(f"{label} block {b} beat {i}: keep 0x{keep:X} is not low-aligned")
                if i < len(beats) - 1 and keep != full:
                    self._fail(f"{label} block {b} beat {i}: keep 0x{keep:X} is partial and "
                               f"it is NOT the last beat -- this is what rs_decoder_core rejects")
            # out_last exactly on the last beat
            lasts = [i for i, (_, _, l) in enumerate(beats) if l]
            if lasts != [len(beats) - 1]:
                self._fail(f"{label} block {b}: out_last on beats {lasts}, expected "
                           f"only {len(beats) - 1}")
            # the symbol sequence must be untouched
            syms = []
            for word, keep, _ in beats:
                for j in range(self.s):
                    if (keep >> j) & 1:
                        syms.append((word >> (j * self.m)) & ((1 << self.m) - 1))
            if syms != sent_syms[b]:
                first = next((i for i, (a, c) in enumerate(zip(syms, sent_syms[b])) if a != c),
                             min(len(syms), len(sent_syms[b])))
                self._fail(f"{label} block {b}: {len(syms)} symbols out of {n}, first "
                           f"difference at {first}")

    async def run_backpressure(self):
        for profile in self.PROFILES[self.level]:
            if profile == 'backtoback':
                continue
            await self.run_blocks(profile)
        return self.mismatches == 0

    def get_test_report(self):
        n = self.k + 2 * self.t
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'profile': f"RS({n},{self.k}) m={self.m} S={self.s}",
                'layout': f"encoder {len(self.encoder_beats(list(range(n))))} beats -> "
                          f"packed {-(-n // self.s)}"}
