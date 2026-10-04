"""
bch_encoder_core testbench

GAXIMaster drives the `in_` valid/ready port (data, keep, last), GAXISlave
drains the `out_` port, and every block is scored against bch_model.BCHModel:
BCHModel.encode(data) must equal the n bits the core emits, with out_last on
the final beat. frame_err is sampled every clock.

Scenarios:
  blocks        random data blocks of exactly k bits, back to back
  backpressure  the same under randomized valid/ready timing profiles
  framing       a short block and a long block: encoded as given, frame_err
                pulses once each, and the next good block is clean
  throughput    back-to-back both sides: one block must complete in n + margin
                cycles (the parity drain is the only stall)

Author: RTL Design Sherpa
Created: 2026-10-03
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge

import galois

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config

from projects.components.ecc_ip.bch.dv.tbclasses.bch_model import BCHModel


class BCHEncoderTB(TBBase):
    """Drives bch_encoder_core and scores it against BCHModel."""

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

        self.M = int(dut.FIELD_DIM.value)
        self.PRIM = int(dut.PRIM_POLY.value)
        self.T = int(dut.T_BITS.value)
        self.N = int(dut.N_BITS.value)
        self.B = int(dut.BITS_PER_BEAT.value)
        self.FIRST_ROOT = int(dut.FIRST_ROOT.value)
        self.K = int(dut.K_BITS.value)

        self.model = BCHModel(self.M, self.PRIM, self.T, self.N, self.FIRST_ROOT)
        self.deg_g = self.model.degree_g()

        self.checks = 0
        self.mismatches = 0
        self.frame_err_count = 0
        self._init_bfms()
        self.log.info(f"BCHEncoderTB BCH({self.N},{self.K}) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} b={self.FIRST_ROOT} B={self.B} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    # -- BFMs ----------------------------------------------------------------
    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.B, default=0))
        fc_in.add_field(FieldDefinition(name='keep', bits=self.B, default=(1 << self.B) - 1))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="BCH_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='data', bits=self.B, default=0))
        fc_out.add_field(FieldDefinition(name='keep', bits=self.B, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="BCH_OUT", prefix="out_", clock=self.clk,
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
        """Encode a full k-bit block; returns n bits."""
        return self.model.encode(data)

    def gold_encode_bits(self, data):
        """Encode an arbitrary-length bit vector; returns len(data)+deg(g) bits.

        Polynomial objects, not field arrays: the first cut built msg_poly and
        x_d as GF(2) arrays, where `*` is elementwise and dies on the shape
        broadcast instead of multiplying polynomials. Mirrors
        bch_model.encode, which constrains itself to exactly k data bits --
        this helper exists for the framing cases (short/long blocks).
        """
        g = self.model._int_to_gf2_poly(self.model.generator_int())
        msg_poly = galois.Poly(list(data), field=self.model.GF2)
        x_d = galois.Poly([self.model.GF2(1)] + [self.model.GF2(0)] * self.deg_g,
                          field=self.model.GF2)
        shifted = msg_poly * x_d
        parity = [int(c) for c in (shifted % g).coefficients(order='desc')]
        parity = [0] * (self.deg_g - len(parity)) + parity
        return list(data) + parity

    # -- driving / collecting -------------------------------------------------
    def beats_of(self, bits):
        """Split a bit list into (data, keep) beats of B bits, low lane first;
        only the last beat may be partial (low-aligned keep)."""
        beats = []
        for i in range(0, len(bits), self.B):
            chunk = bits[i:i + self.B]
            data = 0
            for u, b in enumerate(chunk):
                data |= b << u
            beats.append((data, (1 << len(chunk)) - 1))
        return beats

    def bits_of(self, beats):
        """(data, keep) beats back to bits; a partial beat may appear anywhere."""
        out = []
        for data, keep in beats:
            for u in range(self.B):
                if keep >> u & 1:
                    out.append((data >> u) & 1)
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

    def expected_beats(self, data_len):
        """Beats the encoder emits for a block with that many data bits."""
        return ((data_len + self.B - 1) // self.B +
                (self.deg_g + self.B - 1) // self.B)

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
        exp = self.gold_encode_bits(data)
        self.checks += 1
        got = self.bits_of([(d, k) for d, k, _ in out])
        lasts = [l for _, _, l in out]
        data_beats = len(self.beats_of(data))
        full_keep = (1 << self.B) - 1
        keeps_ok = all(k == full_keep or i in (data_beats - 1, len(out) - 1)
                       for i, (_, k, _) in enumerate(out))
        ok = (got == exp) and lasts == [0] * (len(out) - 1) + [1] and keeps_ok
        if not ok:
            self.mismatches += 1
            if self.mismatches <= 10:
                bad = next((i for i, (g, e) in enumerate(zip(got, exp)) if g != e), None)
                self.log.error(f"{label}: {len(got)} bits in {len(out)} beats vs {len(exp)}; "
                               f"first mismatch at {bad}; lasts ok={lasts == [0] * (len(out) - 1) + [1]}; "
                               f"keeps ok={keeps_ok}")
                self.log.error(f"  got parity {got[len(data):]}")
                self.log.error(f"  exp parity {exp[len(data):]}")
        return ok

    def _random_block(self, length=None):
        length = self.K if length is None else length
        return [random.randint(0, 1) for _ in range(length)]

    # -- scenarios ------------------------------------------------------------
    async def run_blocks(self, profile='backtoback'):
        self.set_profile(profile)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        self.log.info(f"blocks: {n_blocks} x BCH({self.N},{self.K}) under '{profile}'")
        blocks = [[0] * self.K, [1] * self.K]
        blocks += [self._random_block() for _ in range(max(0, n_blocks - 2))]
        for i, data in enumerate(blocks):
            await self.send_block(data)
            out = await self.collect(self.expected_beats(len(data)), timeout_cycles=20 * self.N + 200)
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
        # short block: at least 1 bit
        short_len = max(1, self.K - 3)
        short = self._random_block(short_len)
        await self.send_block(short)
        out = await self.collect(self.expected_beats(short_len), timeout_cycles=20 * self.N + 200)
        self._score_block("short block", short, out)
        # long block
        long_len = self.K + 2
        long = self._random_block(long_len)
        await self.send_block(long)
        out = await self.collect(self.expected_beats(long_len), timeout_cycles=20 * self.N + 200)
        self._score_block("long block", long, out)
        await self.wait_clocks(self.clk_name, 4)
        pulses = self.frame_err_count - before
        expected = 2
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
        """One block with no delays anywhere: n bits out within n + margin cycles."""
        self.set_profile('backtoback')
        data = self._random_block()
        start = None
        self.slave._recvQ.clear()
        await self.send_block(data, wait=False)
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
        self.log.info(f"throughput: {self.N} bits in {n_beats} beats in {elapsed} cycles from "
                      f"first accept (bound beats + {margin} = {bound})")
        if elapsed > bound:
            self.mismatches += 1
            self.log.error(f"throughput: {elapsed} cycles exceeds {bound}")
        return self.mismatches == 0

    async def run_no_dead_cycles(self):
        """Slope over 4 then 8 blocks must be the codeword beat count."""
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
                           f"against a codeword of {nb} beats.")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'frame_err_pulses': self.frame_err_count}
