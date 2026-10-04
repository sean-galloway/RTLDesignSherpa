"""
bch_key_equation_solver testbench

Drives the solver with packed odd syndromes on in_valid/ready and scores the
one-beat out_valid/ready result (Lambda_0..Lambda_t, degree, more-than-t flag)
against bch_model.BCHModel.

Blocks with 0, 1, t, t+1 and many errors, with idle gaps, back-to-back, and
downstream stalls.

Author: RTL Design Sherpa
Created: 2026-10-03
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

from projects.components.ecc_ip.bch.dv.tbclasses.bch_model import BCHModel


class BCHKeyEquationSolverTB(TBBase):
    """Drives bch_key_equation_solver and scores it against BCHModel."""

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
        self.FIRST_ROOT = int(dut.FIRST_ROOT.value)

        self.model = BCHModel(self.M, self.PRIM, self.T, self.N, self.FIRST_ROOT)
        self.K = self.model.k()

        self.checks = 0
        self.mismatches = 0
        self._init_bfms()
        self.log.info(f"BCHKeyEquationSolverTB BCH({self.N},{self.K}) t={self.T} "
                      f"m={self.M} prim=0x{self.PRIM:X} b={self.FIRST_ROOT} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='syndromes', bits=self.T * self.M, default=0))
        self.master = GAXIMaster(dut=self.dut, title="KES_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        deg_width = (self.T + 1).bit_length()
        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='lambda', bits=(self.T + 1) * self.M, default=0))
        fc_out.add_field(FieldDefinition(name='lambda_degree', bits=deg_width, default=0))
        fc_out.add_field(FieldDefinition(name='more_than_t', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="KES_OUT", prefix="out_", clock=self.clk,
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

    def pack_syndromes(self, synd_list):
        packed = 0
        for j, s in enumerate(synd_list):
            packed |= s << (j * self.M)
        return packed

    def unpack_lambda(self, packed):
        mask = (1 << self.M) - 1
        return [(packed >> (i * self.M)) & mask for i in range(self.T + 1)]

    def normalize_lambda(self, lam):
        """Scale a locator so Lambda_0 == 1; riBM and textbook BM differ by scale."""
        if lam[0] == 0:
            return lam
        inv = self.model._to_int(self.model._el(lam[0]) ** -1)
        return [self.model.gf_mul(c, inv) for c in lam]

    def expected(self, block):
        """Return (lambda[0..t], degree_clamped, more_than_t) from the golden model."""
        S = self.model._full_syndrome_sequence(block)
        lam = self.model._berlekamp_massey(S)
        deg = max((i for i, c in enumerate(lam) if c), default=-1)
        lam_low = (lam + [0] * (self.T + 1))[:self.T + 1]
        deg_clamped = min(deg, self.T) if deg >= 0 else 0
        more = deg > self.T
        return lam_low, deg_clamped, more

    async def feed_and_score(self, rx, label=""):
        synd = self.model.syndromes(rx)
        exp_lam, exp_deg, exp_more = self.expected(rx)

        pkt = self.master.create_packet(syndromes=self.pack_syndromes(synd))
        await self.master.send(pkt)

        waited = 0
        while len(self.slave._recvQ) < 1:
            await RisingEdge(self.clk)
            waited += 1
            if waited > 20 * self.T + 200:
                self.log.error(f"timeout waiting for KES output {label}")
                self.mismatches += 1
                return

        out = self.slave._recvQ.popleft()
        got_lam = self.normalize_lambda(self.unpack_lambda(int(getattr(out, 'lambda'))))
        got_deg = int(out.lambda_degree)
        got_more = int(out.more_than_t)

        self._score(f"{label} lambda", got_lam, exp_lam)
        self._score(f"{label} degree", got_deg, exp_deg)
        self._score(f"{label} more_than_t", got_more, exp_more)

    async def run_blocks(self):
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                errors = random.choice([0, 0, 1, self.T, self.T + 1, min(self.N, 2 * self.T + 3)])
                rx, _ = self.random_received(errors)
                await self.feed_and_score(rx, label=f"block {i} ({errors} errors)")
        return self.mismatches == 0

    async def run_back_to_back(self):
        """Two blocks with the second input accepted as soon as the first output clears."""
        self.set_profile('backtoback')
        rx1, _ = self.random_received(1)
        rx2, _ = self.random_received(0)

        synd1 = self.model.syndromes(rx1)
        synd2 = self.model.syndromes(rx2)
        exp1 = self.expected(rx1)
        exp2 = self.expected(rx2)

        self.slave._recvQ.clear()
        await self.master.send(self.master.create_packet(syndromes=self.pack_syndromes(synd1)))

        # Consume the first result so in_ready can rise for the next block.
        waited = 0
        while len(self.slave._recvQ) < 1:
            await RisingEdge(self.clk)
            waited += 1
            if waited > 20 * self.T + 200:
                self.log.error("timeout waiting for back-to-back block 1")
                self.mismatches += 1
                return False
        out1 = self.slave._recvQ.popleft()
        got_lam = self.normalize_lambda(self.unpack_lambda(int(getattr(out1, 'lambda'))))
        self._score("back-to-back block 1 lambda", got_lam, exp1[0])
        self._score("back-to-back block 1 degree", int(out1.lambda_degree), exp1[1])
        self._score("back-to-back block 1 more_than_t", int(out1.more_than_t), exp1[2])

        await self.master.send(self.master.create_packet(syndromes=self.pack_syndromes(synd2)))

        waited = 0
        while len(self.slave._recvQ) < 1:
            await RisingEdge(self.clk)
            waited += 1
            if waited > 20 * self.T + 200:
                self.log.error("timeout waiting for back-to-back block 2")
                self.mismatches += 1
                return False
        out2 = self.slave._recvQ.popleft()
        got_lam = self.normalize_lambda(self.unpack_lambda(int(getattr(out2, 'lambda'))))
        self._score("back-to-back block 2 lambda", got_lam, exp2[0])
        self._score("back-to-back block 2 degree", int(out2.lambda_degree), exp2[1])
        self._score("back-to-back block 2 more_than_t", int(out2.more_than_t), exp2[2])
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
