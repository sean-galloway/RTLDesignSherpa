"""
bch_chien_search testbench

GAXIMaster feeds one-beat locator coefficients on in_valid/ready/in_lambda/
in_lambda_degree; GAXISlave receives the multi-beat out_valid/ready result
containing root flags, the running root count, and out_last. Every walk is
scored against bch_model.BCHModel._chien_positions(lam_asc).

Blocks with 0..t+1 injected errors (locator from Berlekamp-Massey), plus
random degree-<=t polynomials, with idle gaps, back-to-back walks, and
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


class BCHChienSearchTB(TBBase):
    """Drives bch_chien_search and scores it against BCHModel."""

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
        self.FIRST_ROOT = self.convert_to_int(os.environ.get('FIRST_ROOT', '1'))

        self.model = BCHModel(self.M, self.PRIM, self.T, self.N, b=self.FIRST_ROOT)
        self.K = self.model.k()
        self.RC_W = (self.T + 1).bit_length()
        self.LAM_W = (self.T + 1) * self.M

        self.checks = 0
        self.mismatches = 0
        self._init_bfms()
        self.log.info(f"BCHChienSearchTB BCH({self.N},{self.K}) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} b={self.FIRST_ROOT} B={self.B} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='lambda', bits=self.LAM_W, default=0))
        fc_in.add_field(FieldDefinition(name='lambda_degree', bits=self.RC_W, default=0))
        self.master = GAXIMaster(dut=self.dut, title="BCH_CHIEN_IN", prefix="in_",
                                 clock=self.clk, field_config=fc_in, pkt_prefix="",
                                 multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='flip_en', bits=self.B, default=0))
        fc_out.add_field(FieldDefinition(name='root_count', bits=self.RC_W, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="BCH_CHIEN_OUT", prefix="out_",
                               clock=self.clk, field_config=fc_out, pkt_prefix="",
                               multi_sig=True, log=self.log)

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

    def pack_lambda(self, lam_asc):
        """Pack locator coefficients ascending into in_lambda vector."""
        packed = 0
        for i, c in enumerate(lam_asc):
            packed |= (c & ((1 << self.M) - 1)) << (i * self.M)
        return packed

    def random_locator(self):
        """A random degree-<=t locator polynomial (not from an error pattern)."""
        degree = random.randint(0, self.T)
        lam = [random.randint(0, (1 << self.M) - 1) for _ in range(degree + 1)]
        if degree == 0:
            lam[0] = 1
        else:
            lam[degree] = random.randint(1, (1 << self.M) - 1)
        lam += [0] * (self.T + 1 - len(lam))
        return lam

    async def feed_lambda(self, lam_asc):
        """Drive one locator polynomial and collect the resulting walk."""
        packed = self.pack_lambda(lam_asc)
        degree = max((i for i, c in enumerate(lam_asc) if c), default=0)
        self.slave._recvQ.clear()
        pkt = self.master.create_packet(**{'lambda': packed, 'lambda_degree': degree})
        await self.master.send(pkt)

        positions = []
        final_root_count = None
        beat_idx = 0
        while True:
            waited = 0
            while len(self.slave._recvQ) < 1:
                await RisingEdge(self.clk)
                waited += 1
                if waited > 20 * self.N + 200:
                    self.log.error("timeout waiting for chien output beat")
                    self.mismatches += 1
                    return positions, None
            out = self.slave._recvQ.popleft()
            flip_en = int(out.flip_en)
            root_count = int(out.root_count)
            last = int(out.last)
            base_pos = beat_idx * self.B
            for u in range(self.B):
                if base_pos + u < self.N and (flip_en >> u) & 1:
                    positions.append(base_pos + u)
            self._score(f"beat {beat_idx} root_count", root_count, len(positions))
            final_root_count = root_count
            if last:
                break
            beat_idx += 1

        return positions, final_root_count

    async def run_blocks(self):
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                if random.random() < 0.7:
                    errors = random.choice([0, 0, 1, self.T, self.T + 1,
                                            min(self.N, 2 * self.T + 3)])
                    rx, _ = self.random_received(errors)
                    S = self.model._full_syndrome_sequence(rx)
                    lam_asc = self.model._berlekamp_massey(S)
                else:
                    lam_asc = self.random_locator()

                exp_positions = sorted(self.model._chien_positions(lam_asc))
                got_positions, final_count = await self.feed_lambda(lam_asc)

                self._score(f"block {i} positions", got_positions, exp_positions)
                self._score(f"block {i} final_root_count", final_count, len(exp_positions))
        return self.mismatches == 0

    async def run_back_to_back(self):
        """Two walks with no idle cycle between them."""
        self.set_profile('backtoback')
        for label, gen in (("back-to-back block 1", lambda: self.random_received(1)),
                           ("back-to-back block 2", lambda: self.random_received(0))):
            rx, _ = gen()
            S = self.model._full_syndrome_sequence(rx)
            lam_asc = self.model._berlekamp_massey(S)
            exp_positions = sorted(self.model._chien_positions(lam_asc))
            got_positions, final_count = await self.feed_lambda(lam_asc)
            self._score(f"{label} positions", got_positions, exp_positions)
            self._score(f"{label} final_root_count", final_count, len(exp_positions))
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
