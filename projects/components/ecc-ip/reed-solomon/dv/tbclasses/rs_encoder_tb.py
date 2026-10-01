"""
rs_encoder_core testbench

GAXIMaster drives the `in_` valid/ready port (data, keep, last), GAXISlave
drains the `out_` port, and every block is scored against reedsolo's
systematic encoder: rs_encode_msg(data, 2t, fcr=b) must equal the n symbols
the core emits, with out_last on the n-th. frame_err is sampled every clock.

Scenarios:
  blocks        random data blocks of exactly k symbols, back to back
  backpressure  the same under randomized valid/ready timing profiles
  framing       a short block and a long block: encoded as given, frame_err
                pulses once each, and the next good block is clean
  throughput    back-to-back both sides: one block must complete in n + margin
                cycles (the 2t drain is the only stall)

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge

import reedsolo

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class RSEncoderTB(TBBase):
    """Drives rs_encoder_core and scores it against reedsolo."""

    BLOCKS = {'gate': 4, 'func': 24, 'full': 96}
    PROFILES = {'gate': ['constrained'],
                'func': ['constrained', 'bursty', 'slow'],
                'full': ['constrained', 'bursty', 'slow', 'chaotic', 'backtoback']}

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
        self.PRIM = int(dut.PRIM_POLY.value)
        self.T = int(dut.T_SYMBOLS.value)
        self.N = int(dut.N_SYMBOLS.value)
        self.B = int(dut.FIRST_ROOT.value)
        self.K = self.N - 2 * self.T
        self.S = int(dut.SYMBOLS_PER_BEAT.value)
        self.Q = 1 << self.M

        # the golden model's tables for this field
        reedsolo.init_tables(prim=self.PRIM, generator=2, c_exp=self.M)

        self.checks = 0
        self.mismatches = 0
        self.frame_err_count = 0
        self._init_bfms()
        self.log.info(f"RSEncoderTB RS({self.N},{self.K}) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} b={self.B} level={self.TEST_LEVEL} seed={self.SEED}")

    # -- BFMs ----------------------------------------------------------------
    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.M * self.S, default=0))
        fc_in.add_field(FieldDefinition(name='keep', bits=self.S, default=(1 << self.S) - 1))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="RS_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='data', bits=self.M * self.S, default=0))
        fc_out.add_field(FieldDefinition(name='keep', bits=self.S, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="RS_OUT", prefix="out_", clock=self.clk,
                               field_config=fc_out, pkt_prefix="", multi_sig=True, log=self.log)

    def set_profile(self, name):
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    # -- mandatory ----------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 2)
        cocotb.start_soon(self._frame_err_monitor())

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    async def _frame_err_monitor(self):
        while True:
            await RisingEdge(self.clk)
            if int(self.dut.frame_err.value):
                self.frame_err_count += 1

    # -- golden --------------------------------------------------------------
    def gold_encode(self, data):
        enc = reedsolo.rs_encode_msg(bytearray(data) if self.M <= 8 else list(data),
                                     2 * self.T, fcr=self.B, generator=2)
        return list(enc)

    # -- driving / collecting -------------------------------------------------
    # -- beats ----------------------------------------------------------------------
    def beats_of(self, symbols):
        """Split a symbol list into (data, keep) beats of S, low lane first; only
        the last beat may be partial (low-aligned keep)."""
        beats = []
        for i in range(0, len(symbols), self.S):
            chunk = symbols[i:i + self.S]
            data = 0
            for u, sym in enumerate(chunk):
                data |= sym << (u * self.M)
            beats.append((data, (1 << len(chunk)) - 1))
        return beats

    def symbols_of(self, beats):
        """(data, keep) beats back to symbols; a partial beat may appear anywhere
        (the encoder's output has one at the end of the data and one at the
        end of the parity)."""
        out = []
        for data, keep in beats:
            for u in range(self.S):
                if keep >> u & 1:
                    out.append((data >> (u * self.M)) & (self.Q - 1))
        return out

    async def send_block(self, data, wait=True):
        """Queue one block as beats; last on the final beat."""
        beats = self.beats_of(data)
        for i, (d, k) in enumerate(beats):
            pkt = self.master.create_packet(data=d, keep=k, last=1 if i == len(beats) - 1 else 0)
            if wait:
                await self.master.send(pkt)
            else:
                await self.master._driver_send(pkt, sync=True)

    def expected_beats(self, n_symbols_data):
        """Beats the encoder emits for a block of that many data symbols."""
        return (n_symbols_data + self.S - 1) // self.S + (2 * self.T + self.S - 1) // self.S

    async def collect(self, count, timeout_cycles):
        """Wait for `count` output BEATS; return [(data, keep, last)]."""
        waited = 0
        while len(self.slave._recvQ) < count:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_cycles:
                self.log.error(f"timeout: {len(self.slave._recvQ)} of {count} beats after "
                               f"{timeout_cycles} cycles")
                self.mismatches += 1
                break
        out = []
        while self.slave._recvQ:
            pkt = self.slave._recvQ.popleft()
            out.append((int(pkt.data), int(pkt.keep), int(pkt.last)))
        return out

    def _score_block(self, label, data, out):
        exp = self.gold_encode(data)
        self.checks += 1
        got = self.symbols_of([(d, k) for d, k, _ in out])
        lasts = [l for _, _, l in out]
        # keep masks must be low-aligned and full except at the two ends
        keeps_ok = all(k == (1 << self.S) - 1 or i in (len(self.beats_of(data)) - 1, len(out) - 1)
                       for i, (_, k, _) in enumerate(out))
        ok = (got == exp) and lasts == [0] * (len(out) - 1) + [1] and keeps_ok
        if not ok:
            self.mismatches += 1
            if self.mismatches <= 10:
                bad = next((i for i, (g, e) in enumerate(zip(got, exp)) if g != e), None)
                self.log.error(f"{label}: {len(got)} symbols in {len(out)} beats vs {len(exp)}; "
                               f"first mismatch at {bad}; lasts ok={lasts == [0] * (len(out) - 1) + [1]}; "
                               f"keeps ok={keeps_ok}")
                self.log.error(f"  got parity {got[len(data):]}")
                self.log.error(f"  exp parity {exp[len(data):]}")
        return ok

    def _random_block(self, length=None):
        length = self.K if length is None else length
        return [random.randrange(self.Q) for _ in range(length)]

    # -- scenarios ------------------------------------------------------------
    async def run_blocks(self, profile='backtoback'):
        self.set_profile(profile)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        self.log.info(f"blocks: {n_blocks} x RS({self.N},{self.K}) under '{profile}'")
        # corner blocks first: all zero, all ones, then random
        blocks = [[0] * self.K, [self.Q - 1] * self.K]
        blocks += [self._random_block() for _ in range(max(0, n_blocks - 2))]
        for i, data in enumerate(blocks):
            await self.send_block(data)
            out = await self.collect(self.expected_beats(self.K), timeout_cycles=20 * self.N + 200)
            self._score_block(f"block {i}", data, out)
        return self.mismatches == 0

    async def run_backpressure(self):
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            data = self._random_block()
            await self.send_block(data)
            out = await self.collect(self.expected_beats(self.K), timeout_cycles=40 * self.N + 400)
            self._score_block(f"profile {profile}", data, out)
        return self.mismatches == 0

    async def run_framing(self):
        self.set_profile('constrained')
        before = self.frame_err_count
        # short block: k-3 symbols (at least 1)
        short = self._random_block(max(1, self.K - 3))
        await self.send_block(short)
        out = await self.collect(self.expected_beats(len(short)), timeout_cycles=20 * self.N + 200)
        self._score_block("short block", short, out)
        # long block: k+2 symbols, capped at what the golden model can encode
        # (a full-length profile has no room, so its "long" case is k and
        # only the short block pulses)
        long_len = min(self.K + 2, self.Q - 1 - 2 * self.T)
        long = self._random_block(long_len)
        await self.send_block(long)
        out = await self.collect(self.expected_beats(long_len), timeout_cycles=20 * self.N + 200)
        self._score_block("long block", long, out)
        await self.wait_clocks(self.clk_name, 4)
        pulses = self.frame_err_count - before
        expected = 2 if long_len != self.K else 1
        self.checks += 1
        if pulses != expected:
            self.mismatches += 1
            self.log.error(f"frame_err pulses: {pulses}, expected {expected}")
        # a clean block afterwards must be clean and must not pulse
        before = self.frame_err_count
        data = self._random_block()
        await self.send_block(data)
        out = await self.collect(self.expected_beats(self.K), timeout_cycles=20 * self.N + 200)
        self._score_block("block after framing errors", data, out)
        self.checks += 1
        if self.frame_err_count != before:
            self.mismatches += 1
            self.log.error("frame_err pulsed on a clean block")
        return self.mismatches == 0

    async def run_throughput(self):
        """One block with no delays anywhere: n symbols out within n + margin
        cycles of the first input. The margin covers the input BFM's first
        handshake and the skid's fill."""
        self.set_profile('backtoback')
        data = self._random_block()
        start = None
        self.slave._recvQ.clear()
        await self.send_block(data, wait=False)   # queued, so beats present back to back
        n_beats = self.expected_beats(self.K)
        cycles = 0
        while len(self.slave._recvQ) < n_beats:
            await RisingEdge(self.clk)
            cycles += 1
            if start is None and int(self.dut.in_valid.value) and int(self.dut.in_ready.value):
                start = cycles
            if cycles > 20 * self.N + 200:
                break
        out = [(int(p.data), int(p.keep), int(p.last)) for p in self.slave._recvQ]
        self.slave._recvQ.clear()
        self._score_block("throughput block", data, out)
        elapsed = cycles - (start or 0)
        margin = 8
        bound = n_beats + margin
        self.checks += 1
        self.log.info(f"throughput: {self.N} symbols in {n_beats} beats in {elapsed} cycles from "
                      f"first accept (bound beats + {margin} = {bound})")
        if elapsed > bound:
            self.mismatches += 1
            self.log.error(f"throughput: {elapsed} cycles exceeds {bound}")
        return self.mismatches == 0

    async def run_no_dead_cycles(self):
        """The per-block cost must be the codeword's beats and nothing more.

        run_throughput above bounds ONE block's absolute time with a margin,
        which cannot see a per-block gap: a fixed margin absorbs it, and the
        latency it is really measuring is free anyway. This measures the SLOPE
        over 4 then 8 blocks, so every fixed cost -- the first handshake, the
        skid fill, the parity flush -- cancels, and what is left is purely the
        per-block increment. That is the number the bus sees.

        A codeword is K_BEATS + P_BEATS, because the encoder starts parity on
        a FRESH beat; so expected_beats() cycles per block IS line rate, and
        anything above it is a dead cycle at the block boundary.
        """
        self.set_profile('backtoback')
        nb = self.expected_beats(self.K)
        took = {}
        for blocks in (4, 8):
            self.slave._recvQ.clear()
            datas = [self._random_block() for _ in range(blocks)]
            for d in datas:
                await self.send_block(d, wait=False)
            cycles, start = 0, None
            while len(self.slave._recvQ) < blocks * nb:
                await RisingEdge(self.clk)
                cycles += 1
                if start is None and int(self.dut.in_valid.value) and int(self.dut.in_ready.value):
                    start = cycles
                if cycles > 40 * self.N * blocks + 400:
                    break
            out = [(int(p.data), int(p.keep), int(p.last)) for p in self.slave._recvQ]
            self.slave._recvQ.clear()
            for i, d in enumerate(datas):
                self._score_block(f"slope {blocks} blk {i}", d, out[i * nb:(i + 1) * nb])
            took[blocks] = cycles - (start or 0)

        slope = (took[8] - took[4]) / 4.0
        dead = slope - nb
        self.checks += 1
        self.log.info(f"no-dead-cycles: {took[4]} cycles for 4 blocks, {took[8]} for 8 "
                      f"-> slope {slope:.2f} cycles/block vs codeword {nb} beats "
                      f"({dead:+.2f} dead per block)")
        if dead > 0.25:
            self.mismatches += 1
            self.log.error(f"{dead:.2f} DEAD cycles per block: the slope is {slope:.2f} "
                           f"against a codeword of {nb} beats. Latency is free; a gap at "
                           f"the block boundary is not.")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'frame_err_pulses': self.frame_err_count}
