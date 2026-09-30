"""
Decoder sub-block testbenches

Direct-drive TBs for the decoder's Level 1/2 blocks, each scored against
rs_model.RSModel -- the hardware-algorithm reference validated against reedsolo
(rs_model.validate). One class per block:

  SyndromeTB      syndrome_unit: step n symbols with i_first on the first,
                  compare the 2t syndromes and the all-zero flag

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from projects.components.ecc_ip.reed_solomon.dv.tbclasses.rs_model import RSModel


class _DecoderBlockTB(TBBase):
    BLOCKS = {'gate': 8, 'func': 64, 'full': 512}

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
        # blocks without their own FIRST_ROOT (the solver) get it from the environment
        self.B = int(dut.FIRST_ROOT.value) if hasattr(dut, 'FIRST_ROOT') \
            else int(os.environ.get('FIRST_ROOT', '0'))
        self.N = int(os.environ.get('N_SYMBOLS', str((1 << self.M) - 1)))
        self.S = int(dut.SYMBOLS_PER_BEAT.value) if hasattr(dut, 'SYMBOLS_PER_BEAT') else 1
        self.Q = 1 << self.M
        self.model = RSModel(self.M, self.PRIM, self.T, self.N, self.B)
        self.checks = 0
        self.mismatches = 0

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
        """A codeword with `errors` random symbol errors; returns (rx, positions)."""
        data = [random.randrange(self.Q) for _ in range(self.model.k)]
        rx = self.model.encode(data)
        pos = random.sample(range(self.N), errors)
        for p in pos:
            rx[p] ^= random.randrange(1, self.Q)
        return rx, pos

    def beats_of(self, symbols):
        """(packed, count) beats of S symbols, low lane first; the last may be partial."""
        beats = []
        for i in range(0, len(symbols), self.S):
            chunk = symbols[i:i + self.S]
            packed = 0
            for u, sym in enumerate(chunk):
                packed |= sym << (u * self.M)
            beats.append((packed, len(chunk)))
        return beats

    def lanes_of(self, packed, count=None):
        count = self.S if count is None else count
        return [(packed >> (u * self.M)) & (self.Q - 1) for u in range(count)]

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}


class SyndromeTB(_DecoderBlockTB):
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        self.dut.i_step.value = 0
        self.dut.i_first.value = 0
        self.dut.i_data.value = 0
        self.dut.i_count.value = 0
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 3)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 1)

    async def feed(self, rx, gaps=False):
        """Feed a block as beats of S symbols (partial last beat) with i_first
        on the first; returns the registered syndromes and all-zero flag, and
        checks the _next outputs on the last beat matched them."""
        beats = self.beats_of(rx)
        next_synd, next_zero = None, None
        for j, (packed, count) in enumerate(beats):
            if gaps and random.random() < 0.3:
                self.dut.i_step.value = 0
                await RisingEdge(self.clk)
            self.dut.i_data.value = packed
            self.dut.i_count.value = count
            self.dut.i_first.value = 1 if j == 0 else 0
            self.dut.i_step.value = 1
            if j == len(beats) - 1:
                await Timer(1, units='ns')
                next_synd = self.lanes_of(int(self.dut.ow_synd_next.value), 2 * self.T)
                next_zero = int(self.dut.ow_all_zero_next.value)
            await RisingEdge(self.clk)
        self.dut.i_step.value = 0
        self.dut.i_first.value = 0
        await Timer(1, units='ns')
        synd = self.lanes_of(int(self.dut.ow_synd.value), 2 * self.T)
        self._score("next-value outputs on the last beat", (next_synd, next_zero),
                    (synd, int(self.dut.ow_all_zero.value)))
        return synd, int(self.dut.ow_all_zero.value)

    async def run_blocks(self):
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for i in range(n_blocks):
            errors = random.choice([0, 0, 1, self.T, self.T + 1, min(self.N, 2 * self.T + 3)])
            rx, _ = self.random_received(errors)
            synd, zero = await self.feed(rx, gaps=(i % 2 == 1))
            exp = self.model.syndromes(rx)
            self._score(f"block {i} ({errors} errors) syndromes", synd, exp)
            self._score(f"block {i} all_zero", zero, 1 if not any(exp) else 0)
        # back-to-back blocks with no idle cycle between: i_first alone must restart
        rx1, _ = self.random_received(1)
        rx2, _ = self.random_received(0)
        b1, b2 = self.beats_of(rx1), self.beats_of(rx2)
        for j, (packed, count) in enumerate(b1 + b2):
            self.dut.i_data.value = packed
            self.dut.i_count.value = count
            self.dut.i_first.value = 1 if j in (0, len(b1)) else 0
            self.dut.i_step.value = 1
            if j == len(b1) - 1:
                await Timer(1, units='ns')
                got = self.lanes_of(int(self.dut.ow_synd_next.value), 2 * self.T)
                self._score("back-to-back block 1", got, self.model.syndromes(rx1))
            await RisingEdge(self.clk)
        self.dut.i_step.value = 0
        self.dut.i_first.value = 0
        await Timer(1, units='ns')
        self._score("back-to-back block 2 all_zero", int(self.dut.ow_all_zero.value), 1)
        return self.mismatches == 0


class KESTB(_DecoderBlockTB):
    """key_equation_solver_ribm: start with 2t syndromes, expect o_done exactly
    2t cycles later with Lambda (2t+1 coefficients), Omega (t), the degree and
    the degree-error flag all bit-exact against RSModel.ribm."""

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        self.dut.i_start.value = 0
        self.dut.i_synd.value = 0
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 3)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 1)

    def _pack(self, vals):
        p = 0
        for i, v in enumerate(vals):
            p |= v << (i * self.M)
        return p

    def _unpack(self, packed, count):
        return [(packed >> (i * self.M)) & (self.Q - 1) for i in range(count)]

    async def solve(self, S):
        self.dut.i_synd.value = self._pack(S)
        self.dut.i_start.value = 1
        await RisingEdge(self.clk)
        self.dut.i_start.value = 0
        cycles = 0
        while True:
            await RisingEdge(self.clk)
            cycles += 1
            await Timer(1, units='ns')
            if int(self.dut.o_done.value):
                break
            if cycles > 4 * self.T + 8:
                self.log.error("o_done never came")
                return None
        lam = self._unpack(int(self.dut.o_lambda.value), 2 * self.T + 1)
        om = self._unpack(int(self.dut.o_omega.value), self.T)
        return cycles, lam, om, int(self.dut.o_deg.value), int(self.dut.o_deg_err.value), \
            int(self.dut.o_busy.value)

    async def run_blocks(self):
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for i in range(n_blocks):
            errors = random.choice([1, 1, 2, self.T - 1, self.T, self.T, self.T + 1,
                                    min(self.N, 2 * self.T + 3)])
            errors = max(1, min(errors, self.N))
            rx, _ = self.random_received(errors)
            S = self.model.syndromes(rx)
            res = await self.solve(S)
            if res is None:
                self.mismatches += 1
                continue
            cycles, lam, om, deg, deg_err, busy = res
            exp_lam, exp_om = self.model.ribm(S)
            exp_deg = max(0, self.model.degree(exp_lam))
            self._score(f"block {i} ({errors} errs) lambda", lam, exp_lam)
            self._score(f"block {i} omega", om, exp_om)
            self._score(f"block {i} deg", deg, exp_deg)
            self._score(f"block {i} deg_err", deg_err, 1 if exp_deg > self.T else 0)
            self._score(f"block {i} cycles to done", cycles, 2 * self.T)  # 2t iterations, done registered on the last
            self._score(f"block {i} busy cleared", busy, 0)
        # all-zero syndromes: Lambda = 1 (degree 0), the caller bypasses anyway
        res = await self.solve([0] * (2 * self.T))
        if res is not None:
            _, lam, om, deg, deg_err, _ = res
            exp_lam, exp_om = self.model.ribm([0] * (2 * self.T))
            self._score("zero syndromes lambda", lam, exp_lam)
            self._score("zero syndromes deg", deg, 0)
        return self.mismatches == 0


class ChienTB(_DecoderBlockTB):
    """chien_search: load Lambda (t+1 low coefficients from RSModel.ribm), step
    through the n positions, compare o_root with RSModel.chien and o_odd_sum
    with X^-1 * Lambda'(X^-1) computed on the model's field."""

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        self.dut.i_load.value = 0
        self.dut.i_step.value = 0
        self.dut.i_lambda.value = 0
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 3)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 1)

    def _pack(self, vals):
        p = 0
        for i, v in enumerate(vals):
            p |= v << (i * self.M)
        return p

    def odd_sum_expected(self, lam, j):
        """X^-1 * Lambda'(X^-1) = sum over odd i of Lambda_i * X^-i, X = alpha^(n-1-j)."""
        l = self.N - 1 - j
        acc = 0
        for i in range(1, len(lam), 2):
            acc ^= self.model.mul(lam[i], self.model.alpha_pow(-i * l))
        return acc

    async def walk(self, lam):
        """Step through the block a beat at a time; lane u of a beat is
        position j+u. Positions past n (in the last beat) are ignored."""
        self.dut.i_lambda.value = self._pack(lam)
        self.dut.i_load.value = 1
        await RisingEdge(self.clk)
        self.dut.i_load.value = 0
        roots, odd = [], []
        for j in range(0, self.N, self.S):
            await Timer(1, units='ns')
            root_lanes = int(self.dut.o_root.value)
            odd_lanes = self.lanes_of(int(self.dut.o_odd_sum.value))
            for u in range(self.S):
                if j + u >= self.N:
                    break
                if root_lanes >> u & 1:
                    roots.append(j + u)
                odd.append(odd_lanes[u])
            self.dut.i_step.value = 1
            await RisingEdge(self.clk)
        self.dut.i_step.value = 0
        return roots, odd

    async def run_blocks(self):
        for i in range(self.BLOCKS[self.TEST_LEVEL]):
            errors = random.choice([1, 1, 2, self.T - 1, self.T, self.T])
            errors = max(1, min(errors, self.T))
            rx, pos = self.random_received(errors)
            lam_ext, _ = self.model.ribm(self.model.syndromes(rx))
            lam = lam_ext[:self.T + 1]
            roots, odd = await self.walk(lam)
            self._score(f"block {i} ({errors} errs) roots", roots, sorted(pos))
            self._score(f"block {i} model roots agree", self.model.chien(lam), sorted(pos))
            exp_odd = [self.odd_sum_expected(lam, j) for j in range(self.N)]
            self._score(f"block {i} odd sums", odd, exp_odd)
        return self.mismatches == 0


class ForneyTB(_DecoderBlockTB):
    """forney_evaluator: load Omega, step through the positions feeding the
    model's odd sum, and compare o_err_val at each root with the injected
    error value (and with RSModel.forney)."""

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        self.dut.i_load.value = 0
        self.dut.i_step.value = 0
        self.dut.i_omega.value = 0
        self.dut.i_odd_sum.value = 0
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 3)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 1)

    def _pack(self, vals):
        p = 0
        for i, v in enumerate(vals):
            p |= v << (i * self.M)
        return p

    def odd_sum(self, lam, j):
        l = self.N - 1 - j
        acc = 0
        for i in range(1, len(lam), 2):
            acc ^= self.model.mul(lam[i], self.model.alpha_pow(-i * l))
        return acc

    async def run_blocks(self):
        for i in range(self.BLOCKS[self.TEST_LEVEL]):
            errors = random.choice([1, 1, 2, self.T - 1, self.T, self.T])
            errors = max(1, min(errors, self.T))
            data = [random.randrange(self.Q) for _ in range(self.model.k)]
            enc = self.model.encode(data)
            pos = random.sample(range(self.N), errors)
            vals = [random.randrange(1, self.Q) for _ in pos]
            rx = list(enc)
            for p, v in zip(pos, vals):
                rx[p] ^= v
            lam_ext, om = self.model.ribm(self.model.syndromes(rx))
            lam = lam_ext[:self.T + 1]
            self.dut.i_omega.value = self._pack(om)
            self.dut.i_load.value = 1
            await RisingEdge(self.clk)
            self.dut.i_load.value = 0
            got = {}
            den_zero_at_root = 0
            for j in range(0, self.N, self.S):
                packed = 0
                for u in range(self.S):
                    if j + u < self.N:
                        packed |= self.odd_sum(lam, j + u) << (u * self.M)
                self.dut.i_odd_sum.value = packed
                await Timer(1, units='ns')
                lane_vals = self.lanes_of(int(self.dut.o_err_val.value))   # not `vals`: that is the injected list
                dz = int(self.dut.o_den_zero.value)
                for u in range(self.S):
                    if j + u in pos:
                        got[j + u] = lane_vals[u]
                        den_zero_at_root += (dz >> u) & 1
                self.dut.i_step.value = 1
                await RisingEdge(self.clk)
            self.dut.i_step.value = 0
            exp = dict(zip(pos, vals))
            self._score(f"block {i} ({errors} errs) error values", got, exp)
            self._score(f"block {i} model forney agrees",
                        {j: self.model.forney(lam, om, j) for j in pos}, exp)
            self._score(f"block {i} den_zero at roots", den_zero_at_root, 0)
        return self.mismatches == 0


class KESEuclidTB(KESTB):
    """key_equation_solver_euclid: same drive as KESTB, scored against
    RSModel.euclid (bit-exact Lambda and textbook Omega); o_done within
    2t + 1 cycles (data-dependent, plus the finishing check)."""

    async def run_blocks(self):
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for i in range(n_blocks):
            errors = random.choice([1, 1, 2, self.T - 1, self.T, self.T, self.T + 1,
                                    min(self.N, 2 * self.T + 3)])
            errors = max(1, min(errors, self.N))
            rx, _ = self.random_received(errors)
            S = self.model.syndromes(rx)
            res = await self.solve(S)
            if res is None:
                self.mismatches += 1
                continue
            cycles, lam, om, deg, deg_err, busy = res
            exp_lam, exp_om, exp_cycles = self.model.euclid(S)
            exp_deg = max(0, self.model.degree(exp_lam))
            self._score(f"block {i} ({errors} errs) lambda", lam, exp_lam)
            self._score(f"block {i} omega", om, exp_om)
            self._score(f"block {i} deg", deg, exp_deg)
            self._score(f"block {i} deg_err", deg_err, 1 if exp_deg > self.T else 0)
            self._score(f"block {i} cycles to done", cycles, exp_cycles + 1)
            # measured on the model over 3000 blocks per profile: at most 2t
            # iterations for t >= 8, 2t + 1 at t <= 2 when a leading syndrome is
            # zero (a normalise step); plus one cycle for the finishing check
            self.checks += 1
            if cycles > 2 * self.T + 2:
                self.mismatches += 1
                self.log.error(f"block {i}: {cycles} cycles exceeds 2t + 2")
            self._score(f"block {i} busy cleared", busy, 0)
        return self.mismatches == 0

