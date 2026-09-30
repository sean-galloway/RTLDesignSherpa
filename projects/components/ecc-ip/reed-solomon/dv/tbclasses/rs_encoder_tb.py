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
    async def send_block(self, data):
        """Queue one block; last on the final symbol. Does not wait for output."""
        for i, sym in enumerate(data):
            pkt = self.master.create_packet(data=sym, keep=(1 << self.S) - 1,
                                            last=1 if i == len(data) - 1 else 0)
            await self.master.send(pkt)

    async def collect(self, count, timeout_cycles):
        waited = 0
        while len(self.slave._recvQ) < count:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_cycles:
                self.log.error(f"timeout: {len(self.slave._recvQ)} of {count} symbols after "
                               f"{timeout_cycles} cycles")
                self.mismatches += 1
                break
        out = []
        while self.slave._recvQ:
            pkt = self.slave._recvQ.popleft()
            out.append((int(pkt.data), int(pkt.last)))
        return out

    def _score_block(self, label, data, out):
        exp = self.gold_encode(data)
        n_out = len(exp)
        self.checks += 1
        got = [d for d, _ in out]
        lasts = [l for _, l in out]
        ok = (got == exp) and lasts == [0] * (n_out - 1) + [1]
        if not ok:
            self.mismatches += 1
            if self.mismatches <= 10:
                bad = next((i for i, (g, e) in enumerate(zip(got, exp)) if g != e), None)
                self.log.error(f"{label}: len {len(got)} vs {n_out}; first data mismatch at "
                               f"{bad}; lasts ok={lasts == [0] * (n_out - 1) + [1]}")
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
            out = await self.collect(self.N, timeout_cycles=20 * self.N + 200)
            self._score_block(f"block {i}", data, out)
        return self.mismatches == 0

    async def run_backpressure(self):
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            data = self._random_block()
            await self.send_block(data)
            out = await self.collect(self.N, timeout_cycles=40 * self.N + 400)
            self._score_block(f"profile {profile}", data, out)
        return self.mismatches == 0

    async def run_framing(self):
        self.set_profile('constrained')
        before = self.frame_err_count
        # short block: k-3 symbols (at least 1)
        short = self._random_block(max(1, self.K - 3))
        await self.send_block(short)
        out = await self.collect(len(short) + 2 * self.T, timeout_cycles=20 * self.N + 200)
        self._score_block("short block", short, out)
        # long block: k+2 symbols, capped at what the golden model can encode
        # (a full-length profile has no room, so its "long" case is k and
        # only the short block pulses)
        long_len = min(self.K + 2, self.Q - 1 - 2 * self.T)
        long = self._random_block(long_len)
        await self.send_block(long)
        out = await self.collect(long_len + 2 * self.T, timeout_cycles=20 * self.N + 200)
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
        out = await self.collect(self.N, timeout_cycles=20 * self.N + 200)
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
        for i, sym in enumerate(data):
            pkt = self.master.create_packet(data=sym, keep=(1 << self.S) - 1,
                                            last=1 if i == len(data) - 1 else 0)
            # queue without waiting for completion, so beats present back to back
            await self.master._driver_send(pkt, sync=True)
        cycles = 0
        while len(self.slave._recvQ) < self.N:
            await RisingEdge(self.clk)
            cycles += 1
            if start is None and int(self.dut.in_valid.value) and int(self.dut.in_ready.value):
                start = cycles
            if cycles > 20 * self.N + 200:
                break
        out = [(int(p.data), int(p.last)) for p in self.slave._recvQ]
        self.slave._recvQ.clear()
        self._score_block("throughput block", data, out)
        elapsed = cycles - (start or 0)
        margin = 8
        self.checks += 1
        self.log.info(f"throughput: {self.N} symbols in {elapsed} cycles from first accept "
                      f"(bound n + {margin} = {self.N + margin})")
        if elapsed > self.N + margin:
            self.mismatches += 1
            self.log.error(f"throughput: {elapsed} cycles exceeds {self.N + margin}")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'frame_err_pulses': self.frame_err_count}
