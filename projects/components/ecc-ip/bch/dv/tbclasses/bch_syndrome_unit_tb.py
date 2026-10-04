"""
bch_syndrome_unit testbench

GAXIMaster feeds received codeword bits on in_valid/ready/in_data/in_keep/in_last;
GAXISlave receives the one-beat out_valid/ready result containing the t odd
syndromes and the all-zero flag. Every result is scored against
bch_model.BCHModel.syndromes(block).

Blocks with 0, 1, t, t+1 and many errors, with and without idle cycles between
beats, and two blocks back to back.

Author: RTL Design Sherpa
Created: 2026-10-03
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config

from projects.components.ecc_ip.bch.dv.tbclasses.bch_model import BCHModel


class BCHSyndromeTB(TBBase):
    """Drives bch_syndrome_unit and scores it against BCHModel."""

    BLOCKS = {'gate': 6, 'func': 48, 'full': 256}
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

        self.model = BCHModel(self.M, self.PRIM, self.T, self.N, self.FIRST_ROOT)
        self.K = self.model.k()

        self.checks = 0
        self.mismatches = 0
        self._init_bfms()
        self.log.info(f"BCHSyndromeTB BCH({self.N},{self.K}) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} b={self.FIRST_ROOT} B={self.B} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.B, default=0))
        fc_in.add_field(FieldDefinition(name='keep', bits=self.B, default=(1 << self.B) - 1))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="BCH_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='syndromes', bits=self.T * self.M, default=0))
        fc_out.add_field(FieldDefinition(name='no_error', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="BCH_OUT", prefix="out_", clock=self.clk,
                               field_config=fc_out, pkt_prefix="", multi_sig=True, log=self.log)

    def set_profile(self, name):
        cfg = quick_config(profiles=[name], fields=['valid_delay', 'ready_delay']).build()
        self.master.set_randomizer(cfg[name])
        self.slave.set_randomizer(cfg[name])

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
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

    def random_received(self, errors):
        """A codeword with `errors` random bit errors; returns (rx, positions)."""
        data = [random.randint(0, 1) for _ in range(self.K)]
        enc = self.model.encode(data)
        rx = list(enc)
        pos = []
        if errors:
            pos = random.sample(range(self.N), errors)
            for p in pos:
                rx[p] ^= 1
        return rx, pos

    def beats_of(self, bits):
        """(packed, keep) beats of B bits, low lane first; last may be partial."""
        beats = []
        for i in range(0, len(bits), self.B):
            chunk = bits[i:i + self.B]
            packed = 0
            for u, b in enumerate(chunk):
                packed |= b << u
            beats.append((packed, (1 << len(chunk)) - 1))
        return beats

    def unpack_syndromes(self, packed):
        return [(packed >> (j * self.M)) & ((1 << self.M) - 1) for j in range(self.T)]

    async def feed(self, rx, gaps=False):
        """Feed a block as beats and return (syndromes, no_error)."""
        beats = self.beats_of(rx)
        self.slave._recvQ.clear()
        for j, (packed, keep) in enumerate(beats):
            if gaps and random.random() < 0.3:
                pkt = self.master.create_packet(data=0, keep=0, last=0)
                await self.master.send(pkt)
            pkt = self.master.create_packet(data=packed, keep=keep,
                                            last=1 if j == len(beats) - 1 else 0)
            await self.master.send(pkt)

        waited = 0
        while len(self.slave._recvQ) < 1:
            await RisingEdge(self.clk)
            waited += 1
            if waited > 20 * self.N + 200:
                self.log.error("timeout waiting for syndrome output")
                self.mismatches += 1
                return [0] * self.T, 1
        out = self.slave._recvQ.popleft()
        synd = self.unpack_syndromes(int(out.syndromes))
        no_err = int(out.no_error)
        return synd, no_err

    async def run_blocks(self):
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                errors = random.choice([0, 0, 1, self.T, self.T + 1, min(self.N, 2 * self.T + 3)])
                rx, _ = self.random_received(errors)
                synd, no_err = await self.feed(rx, gaps=(i % 2 == 1))
                exp = self.model.syndromes(rx)
                self._score(f"block {i} ({errors} errors) syndromes", synd, exp)
                self._score(f"block {i} all_zero", no_err, 1 if not any(exp) else 0)
        return self.mismatches == 0

    async def run_back_to_back(self):
        """Two blocks with no idle cycle between them."""
        self.set_profile('backtoback')
        rx1, _ = self.random_received(1)
        rx2, _ = self.random_received(0)
        b1, b2 = self.beats_of(rx1), self.beats_of(rx2)
        self.slave._recvQ.clear()
        for j, (packed, keep) in enumerate(b1 + b2):
            pkt = self.master.create_packet(data=packed, keep=keep,
                                            last=1 if j in (len(b1) - 1, len(b1) + len(b2) - 1) else 0)
            await self.master.send(pkt)

        for label, rx in (("back-to-back block 1", rx1), ("back-to-back block 2", rx2)):
            waited = 0
            while len(self.slave._recvQ) < 1:
                await RisingEdge(self.clk)
                waited += 1
                if waited > 20 * self.N + 200:
                    self.log.error(f"timeout waiting for {label}")
                    self.mismatches += 1
                    return False
            out = self.slave._recvQ.popleft()
            synd = self.unpack_syndromes(int(out.syndromes))
            no_err = int(out.no_error)
            exp = self.model.syndromes(rx)
            self._score(label, synd, exp)
            self._score(f"{label} all_zero", no_err, 1 if not any(exp) else 0)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
