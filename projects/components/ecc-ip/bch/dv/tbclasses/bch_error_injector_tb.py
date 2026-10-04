"""
bch_error_injector testbench

GAXIMaster feeds coded bits on in_valid/ready/in_data/in_keep/in_last;
GAXISlave receives the same interface on out_.  A seeded Python model mirrors
the RTL's per-bit xorshift generators and selection-sampling decisions so every
output beat can be compared bit-exactly.  Additional property checks cover
COUNT distinctness/uniformity, BURST contiguity, RATE mean, keep gating, and
statistics counters.

Author: RTL Design Sherpa
Created: 2026-10-03
"""

import os
import random
import math

import cocotb
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class BCHErrorInjectorModel:
    """Bit-exact mirror of the RTL error injector's logical behavior."""

    def __init__(self, n, b, seed=12345):
        self.N = n
        self.B = b
        self._seed = seed
        self.reset(seed)

    def reset(self, seed):
        self.rnd = [((0x9E37_79B9 * (u + 1)) & 0xFFFFFFFF) for u in range(self.B)]
        self.pos = 0
        self.first = True
        self.e_left = 0
        self.burst_start = 0
        self.seed_load(seed)

    def seed_load(self, seed):
        for u in range(self.B):
            self.rnd[u] = ((seed ^ ((0x9E37_79B9 * (u + 1)) & 0xFFFFFFFF)) | 1) & 0xFFFFFFFF

    @staticmethod
    def xorshift32(x):
        x = (x ^ ((x << 13) & 0xFFFFFFFF)) & 0xFFFFFFFF
        x = (x ^ (x >> 17)) & 0xFFFFFFFF
        x = (x ^ ((x << 5) & 0xFFFFFFFF)) & 0xFFFFFFFF
        return x

    def _advance(self):
        r16 = []
        for u in range(self.B):
            self.rnd[u] = self.xorshift32(self.rnd[u])
            r16.append(self.rnd[u] & 0xFFFF)
        return r16

    def process_beat(self, data, keep, last, mode, count, rate):
        r16 = self._advance()
        e_left = count if self.first else self.e_left
        hits = 0
        k_before = 0
        out_data = data
        positions = []

        if mode == 1:  # COUNT
            for u in range(self.B):
                if not (keep >> u) & 1:
                    continue
                pos_u = self.pos + u
                inrange = pos_u < self.N
                rem = self.N - pos_u
                lhs_hi = ((r16[u] * rem) >> 16) if inrange else 0
                threshold = e_left - k_before
                hit = inrange and threshold > 0 and lhs_hi < threshold
                if hit:
                    out_data ^= (1 << u)
                    hits += 1
                    k_before += 1
                    positions.append(pos_u)
            self.e_left = e_left - hits

        elif mode == 2:  # BURST
            if self.first:
                span = self.N - count + 1
                self.burst_start = (r16[0] * span) >> 16
            for u in range(self.B):
                if not (keep >> u) & 1:
                    continue
                pos_u = self.pos + u
                hit = self.burst_start <= pos_u < self.burst_start + count
                if hit:
                    out_data ^= (1 << u)
                    hits += 1
                    positions.append(pos_u)

        elif mode == 3:  # RATE
            for u in range(self.B):
                if not (keep >> u) & 1:
                    continue
                hit = r16[u] < rate
                if hit:
                    out_data ^= (1 << u)
                    hits += 1

        if last:
            self.pos = 0
            self.first = True
        else:
            self.pos += self.B
            self.first = False

        return out_data, keep, last, hits, positions


class BCHErrorInjectorTB(TBBase):
    """Drives bch_error_injector and scores it against BCHErrorInjectorModel."""

    BLOCKS = {'gate': 8, 'func': 32, 'full': 128}
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

        self.model = BCHErrorInjectorModel(self.N, self.B, seed=self.SEED)
        self.checks = 0
        self.mismatches = 0
        self._init_bfms()
        self.log.info(f"BCHErrorInjectorTB BCH({self.N},*) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} B={self.B} level={self.TEST_LEVEL} seed={self.SEED}")

    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.B, default=0))
        fc_in.add_field(FieldDefinition(name='keep', bits=self.B, default=(1 << self.B) - 1))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="INJ_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='data', bits=self.B, default=0))
        fc_out.add_field(FieldDefinition(name='keep', bits=self.B, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="INJ_OUT", prefix="out_", clock=self.clk,
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

    def beats_of(self, bits, keep_override=None):
        """Split a bit list into (data, keep) beats of B bits, low lane first."""
        beats = []
        for i in range(0, len(bits), self.B):
            chunk = bits[i:i + self.B]
            data = 0
            for u, b in enumerate(chunk):
                data |= b << u
            if keep_override is not None:
                keep = keep_override[i // self.B]
            else:
                keep = (1 << len(chunk)) - 1
            beats.append((data, keep))
        return beats

    async def apply_config(self, mode, count, rate, seed_load=False, clear=False, mark=0, seed=None):
        if seed is not None:
            self.dut.cfg_seed.value = seed
        self.dut.cfg_mode.value = mode
        self.dut.cfg_count.value = count
        self.dut.cfg_rate.value = rate
        self.dut.cfg_seed_load.value = 1 if seed_load else 0
        self.dut.cfg_clear.value = 1 if clear else 0
        self.dut.cfg_mark.value = mark
        await self.wait_clocks(self.clk_name, 1)
        if seed_load and seed is not None:
            self.model.seed_load(seed)
        self.dut.cfg_seed_load.value = 0
        self.dut.cfg_clear.value = 0

    async def send_block(self, bits, keep_override=None):
        """Send a block, return list of predicted beats and total hits."""
        beats = self.beats_of(bits, keep_override)
        predicted = []
        total_hits = 0
        for data, keep in beats:
            mode = int(self.dut.cfg_mode.value)
            count = int(self.dut.cfg_count.value)
            rate = int(self.dut.cfg_rate.value)
            last = 1 if len(predicted) == len(beats) - 1 else 0
            exp_data, exp_keep, exp_last, hits, _ = self.model.process_beat(
                data, keep, last, mode, count, rate)
            predicted.append((exp_data, exp_keep, exp_last))
            total_hits += hits
            pkt = self.master.create_packet(data=data, keep=keep, last=last)
            await self.master.send(pkt)
        return predicted, total_hits

    async def collect_beats(self, n_beats, timeout_cycles=None):
        timeout_cycles = timeout_cycles or 20 * self.N + 200
        waited = 0
        while len(self.slave._recvQ) < n_beats:
            await RisingEdge(self.clk)
            waited += 1
            if waited > timeout_cycles:
                self.log.error(f"timeout waiting for {n_beats} beats")
                self.mismatches += 1
                break
        out = []
        while len(out) < n_beats and self.slave._recvQ:
            pkt = self.slave._recvQ.popleft()
            out.append((int(pkt.data), int(pkt.keep), int(pkt.last)))
        return out

    async def run_none_mode(self):
        """Mode 0 must pass through unchanged."""
        await self.apply_config(mode=0, count=0, rate=0, seed_load=True, seed=self.SEED)
        bits = [random.randint(0, 1) for _ in range(self.N)]
        predicted, _ = await self.send_block(bits)
        out = await self.collect_beats(len(predicted))
        for i, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"NONE beat {i}", got, exp)
        return self.mismatches == 0

    async def run_count_mode(self):
        """Mode 1: exact count, distinct positions, and bit-exact output."""
        await self.apply_config(mode=1, count=0, rate=0, seed_load=True, seed=self.SEED)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        error_counts = [0, 1, self.T, min(self.N, self.T + 2)]
        if self.N > self.T + 3:
            error_counts.append(self.T + 3)
        all_positions = []
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                count = random.choice(error_counts)
                await self.apply_config(mode=1, count=count, rate=0)
                bits = [random.randint(0, 1) for _ in range(self.N)]
                predicted, total_hits = await self.send_block(bits)
                out = await self.collect_beats(len(predicted))
                for j, (got, exp) in enumerate(zip(out, predicted)):
                    self._score(f"COUNT block {i} beat {j}", got, exp)
                self._score(f"COUNT block {i} total hits", total_hits, min(count, self.N))
                # collect positions for uniformity sanity
                pos = 0
                for data, keep, last in predicted:
                    for u in range(self.B):
                        if (keep >> u) & 1:
                            if (data >> u) & 1 != bits[pos]:
                                all_positions.append(pos)
                            pos += 1
                        if pos >= self.N:
                            break
        # uniformity sanity over aggregate hits (weighted by bin width)
        if all_positions and self.N > 1:
            n_bins = min(8, self.N)
            bins = [0] * n_bins
            bin_edges = [self.N * i // n_bins for i in range(n_bins + 1)]
            for p in all_positions:
                for b in range(n_bins):
                    if bin_edges[b] <= p < bin_edges[b + 1]:
                        bins[b] += 1
                        break
            total = len(all_positions)
            if total > n_bins * 5:
                chi = 0.0
                for b in range(n_bins):
                    width = bin_edges[b + 1] - bin_edges[b]
                    expected = total * width / self.N
                    if expected > 0:
                        chi += ((bins[b] - expected) ** 2) / expected
                crit = 2 * n_bins  # loose sanity threshold
                self.checks += 1
                if chi > crit:
                    self.mismatches += 1
                    self.log.error(f"COUNT position uniformity failed: chi={chi:.2f}")
        return self.mismatches == 0

    async def run_burst_mode(self):
        """Mode 2: hits form one contiguous run."""
        await self.apply_config(mode=2, count=0, rate=0, seed_load=True, seed=self.SEED)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                count = random.choice([1, self.T, min(self.N, 2 * self.T)])
                await self.apply_config(mode=2, count=count, rate=0)
                bits = [random.randint(0, 1) for _ in range(self.N)]
                predicted, total_hits = await self.send_block(bits)
                out = await self.collect_beats(len(predicted))
                for j, (got, exp) in enumerate(zip(out, predicted)):
                    self._score(f"BURST block {i} beat {j}", got, exp)
                # contiguity check on predicted positions
                positions = []
                pos = 0
                for data, keep, last in predicted:
                    for u in range(self.B):
                        if (keep >> u) & 1:
                            if (data >> u) & 1 != bits[pos]:
                                positions.append(pos)
                            pos += 1
                        if pos >= self.N:
                            break
                if positions:
                    span = max(positions) - min(positions) + 1
                    self._score(f"BURST block {i} contiguous", span, len(positions))
                    self._score(f"BURST block {i} count", len(positions), min(count, self.N))
        return self.mismatches == 0

    async def run_rate_mode(self):
        """Mode 3: per-bit flip probability rate/65536, mean within tolerance."""
        await self.apply_config(mode=3, count=0, rate=0, seed_load=True, seed=self.SEED)
        # Send enough bits to measure rate; at least 10k valid bits.
        target_bits = max(10000, 16 * self.N)
        rate = 1000  # ~1.5 %
        await self.apply_config(mode=3, count=0, rate=rate)
        bits = [random.randint(0, 1) for _ in range(target_bits)]
        predicted, total_hits = await self.send_block(bits)
        out = await self.collect_beats(len(predicted))
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"RATE beat {j}", got, exp)
        valid_bits = sum(bin(keep).count('1') for _, keep, _ in predicted)
        if valid_bits:
            measured = total_hits / valid_bits
            expected = rate / 65536.0
            # 20 % relative tolerance, min 0.005 absolute
            tol = max(expected * 0.20, 0.005)
            self.checks += 1
            if abs(measured - expected) > tol:
                self.mismatches += 1
                self.log.error(f"RATE mean off: measured {measured:.5f}, expected {expected:.5f}")
        return self.mismatches == 0

    async def run_keep_awareness(self):
        """No flips in lanes where keep is zero."""
        await self.apply_config(mode=3, count=0, rate=5000, seed_load=True, seed=self.SEED)
        bits = [random.randint(0, 1) for _ in range(self.N)]
        n_beats = (self.N + self.B - 1) // self.B
        # zero one lane per beat deterministically
        keeps = []
        for i in range(n_beats):
            keeps.append(((1 << self.B) - 1) & ~(1 << (i % self.B)))
        predicted, _ = await self.send_block(bits, keep_override=keeps)
        out = await self.collect_beats(len(predicted))
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"KEEP beat {j}", got, exp)
        return self.mismatches == 0

    async def run_backpressure(self):
        """Full backpressure: hold out_ready low and verify no drops."""
        await self.apply_config(mode=1, count=2, rate=0, seed_load=True, seed=self.SEED)
        self.set_profile('slow')
        bits = [random.randint(0, 1) for _ in range(self.N)]
        predicted, _ = await self.send_block(bits)
        out = await self.collect_beats(len(predicted), timeout_cycles=100 * self.N + 500)
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"BACKPRESSURE beat {j}", got, exp)
        return self.mismatches == 0

    async def run_stats(self):
        """Check statistics counters over a known run."""
        await self.apply_config(mode=1, count=0, rate=0, seed_load=True, clear=True, seed=self.SEED)
        n_blocks = 4
        total_hits_sum = 0
        blocks_hit = 0
        over_t = 0
        last_hits = 0
        for i in range(n_blocks):
            count = [0, 1, self.T, self.T + 2][i % 4]
            count = min(count, self.N)
            await self.apply_config(mode=1, count=count, rate=0)
            bits = [random.randint(0, 1) for _ in range(self.N)]
            predicted, total_hits = await self.send_block(bits)
            out = await self.collect_beats(len(predicted))
            for got, exp in zip(out, predicted):
                self._score("stats beat", got, exp)
            total_hits_sum += total_hits
            if total_hits:
                blocks_hit += 1
            if total_hits > self.T:
                over_t += 1
            last_hits = total_hits

        await self.wait_clocks(self.clk_name, 4)
        self.checks += 4
        if int(self.dut.o_inj_bits.value) != total_hits_sum:
            self.mismatches += 1
            self.log.error(f"stats o_inj_bits: got {int(self.dut.o_inj_bits.value)} exp {total_hits_sum}")
        if int(self.dut.o_inj_blocks.value) != blocks_hit:
            self.mismatches += 1
            self.log.error(f"stats o_inj_blocks: got {int(self.dut.o_inj_blocks.value)} exp {blocks_hit}")
        if int(self.dut.o_inj_over_t.value) != over_t:
            self.mismatches += 1
            self.log.error(f"stats o_inj_over_t: got {int(self.dut.o_inj_over_t.value)} exp {over_t}")
        if int(self.dut.o_last_block_errors.value) != last_hits:
            self.mismatches += 1
            self.log.error(f"stats o_last_block_errors: got {int(self.dut.o_last_block_errors.value)} exp {last_hits}")

        # clear check
        await self.apply_config(mode=0, count=0, rate=0, clear=True)
        await self.wait_clocks(self.clk_name, 2)
        self.checks += 3
        if int(self.dut.o_inj_bits.value) != 0:
            self.mismatches += 1
        if int(self.dut.o_inj_blocks.value) != 0:
            self.mismatches += 1
        if int(self.dut.o_inj_over_t.value) != 0:
            self.mismatches += 1
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
