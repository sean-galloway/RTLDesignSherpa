"""
error_injector testbench

GAXIMaster feeds coded symbols on in_valid/ready/in_data/in_keep/in_last;
GAXISlave receives the same interface plus out_erasure on out_.  A seeded
Python model mirrors the RTL's per-lane xorshift generators and selection-
sampling decisions so every output beat can be compared symbol-exactly.
Additional property checks cover COUNT distinctness/uniformity, BURST
contiguity, RATE mean, keep gating, CLUSTERS geometry, LOCALIZED window
placement, BADBLOCK severity toggling, DEBUG deterministic walking, erasure
marking, backpressure, and statistics counters.

Author: RTL Design Sherpa
Created: 2026-10-04
"""

import os
import random
import math

from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config


class ErrorInjectorModel:
    """Bit-exact mirror of the RTL error injector's logical behavior."""

    MAXB = 8

    def __init__(self, m, s, n, t, seed=12345):
        self.M = m
        self.S = s
        self.N = n
        self.T = t
        self._seed = seed
        self.beat_count = 0
        self.reset(seed)

    def reset(self, seed):
        self.rnd = [((0x9E37_79B9 * (u + 1)) & 0xFFFFFFFF) for u in range(self.S)]
        self.rnd_a = ((0x9E37_79B9 * 3) & 0xFFFFFFFF)
        self.rnd_b = ((0x9E37_79B9 * 7) & 0xFFFFFFFF)
        self.pos = 0
        self.first = True
        self.e_left = 0
        self.burst_start = 0
        self.tab_start = [0] * self.MAXB
        self.tab_len = [0] * self.MAXB
        self.n_burst = 0
        self.loc_start = 0
        self.loc_wid = 0
        self.bad = False
        self.rate_eff = 0
        self.dbg_base = 0
        self.seed_load(seed)

    def seed_load(self, seed):
        for u in range(self.S):
            self.rnd[u] = ((seed ^ ((0x9E37_79B9 * (u + 1)) & 0xFFFFFFFF)) | 1) & 0xFFFFFFFF
        self.rnd_a = ((seed ^ ((0x9E37_79B9 * 3) & 0xFFFFFFFF)) | 1) & 0xFFFFFFFF
        self.rnd_b = ((seed ^ ((0x9E37_79B9 * 7) & 0xFFFFFFFF)) | 1) & 0xFFFFFFFF

    @staticmethod
    def xorshift32(x):
        x = (x ^ ((x << 13) & 0xFFFFFFFF)) & 0xFFFFFFFF
        x = (x ^ (x >> 17)) & 0xFFFFFFFF
        x = (x ^ ((x << 5) & 0xFFFFFFFF)) & 0xFFFFFFFF
        return x

    def _advance(self):
        r16 = []
        for u in range(self.S):
            self.rnd[u] = self.xorshift32(self.rnd[u])
            r16.append(self.rnd[u] & 0xFFFF)
        self.rnd_a = self.xorshift32(self.rnd_a)
        self.rnd_b = self.xorshift32(self.rnd_b)
        return r16

    def _draw_clusters(self, cnt_min, cnt_max, len_min, len_max):
        # Mirror the RTL's combinational cluster-table draw on the first beat.
        xa = [0] * (self.MAXB + 1)
        xb = [0] * self.MAXB
        xa[0] = self.rnd_a
        for i in range(1, self.MAXB + 1):
            xa[i] = self.xorshift32(xa[i - 1])
        xb[0] = self.rnd_b
        for i in range(1, self.MAXB):
            xb[i] = self.xorshift32(xb[i - 1])

        if cnt_max > cnt_min:
            n = cnt_min + (((xa[0] & 0xFFFF) * (cnt_max - cnt_min + 1)) >> 16)
        else:
            n = cnt_min
        if n > self.MAXB:
            n = self.MAXB
        self.n_burst = n

        for i in range(self.MAXB):
            if len_max > len_min:
                l = len_min + (((xa[i + 1] & 0xFFFF) * (len_max - len_min + 1)) >> 16)
            else:
                l = len_min
            if l > self.N:
                l = self.N
            s = ((xb[i] & 0xFFFF) * (self.N - l + 1)) >> 16
            self.tab_len[i] = l if i < n else 0
            self.tab_start[i] = s if i < n else 0

    def _draw_block_state(self, mode, rate, count, len_min, len_max):
        # Stream outputs after the per-beat advance, mirroring the RTL's
        # combinational cluster-table chain on the block's first beat.
        xa0 = self.rnd_a
        xa1 = self.xorshift32(xa0)
        xb0 = self.rnd_b
        if mode == 5:  # LOCALIZED
            if len_max > len_min:
                wid = len_min + (((xa1 & 0xFFFF) * (len_max - len_min + 1)) >> 16)
            else:
                wid = len_min
            if wid > self.N:
                wid = self.N
            start = ((xb0 & 0xFFFF) * (self.N - wid + 1)) >> 16
            self.loc_wid = wid
            self.loc_start = start
        elif mode == 6:  # BADBLOCK
            self.bad = (xa0 & 0xFFFF) < len_min
            self.rate_eff = len_max if self.bad else rate
        elif mode == 7:  # DEBUG
            step = rate % self.N
            self.dbg_base = (self.dbg_base + step) % self.N

    def process_beat(self, data, keep, last, mode, count=0, rate=0,
                     cnt_min=0, cnt_max=0, len_min=0, len_max=0, mark=0):
        self.beat_count += 1
        r16 = self._advance()

        if self.first:
            if mode == 4:
                self._draw_clusters(cnt_min, cnt_max, len_min, len_max)
            elif mode in (5, 6, 7):
                self._draw_block_state(mode, rate, count, len_min, len_max)

        e_left = count if self.first else self.e_left
        hits = 0
        k_before = 0
        out_data = data
        positions = []
        hit_mask = 0

        if mode == 1:  # COUNT
            for u in range(self.S):
                if not (keep >> u) & 1:
                    continue
                pos_u = self.pos + u
                inrange = pos_u < self.N
                rem = self.N - pos_u
                lhs_hi = ((r16[u] * rem) >> 16) if inrange else 0
                threshold = e_left - k_before
                hit = inrange and threshold > 0 and lhs_hi < threshold
                if hit:
                    out_data ^= ((self._val(u, r16[u]) & ((1 << self.M) - 1)) << (u * self.M))
                    hits += 1
                    k_before += 1
                    positions.append(pos_u)
                    hit_mask |= (1 << u)
            self.e_left = e_left - hits

        elif mode == 2:  # BURST
            if self.first:
                span = self.N - count + 1
                self.burst_start = (r16[0] * span) >> 16
            for u in range(self.S):
                if not (keep >> u) & 1:
                    continue
                pos_u = self.pos + u
                hit = self.burst_start <= pos_u < self.burst_start + count
                if hit:
                    out_data ^= ((self._val(u, r16[u]) & ((1 << self.M) - 1)) << (u * self.M))
                    hits += 1
                    positions.append(pos_u)
                    hit_mask |= (1 << u)

        elif mode == 3:  # RATE
            for u in range(self.S):
                if not (keep >> u) & 1:
                    continue
                hit = r16[u] < rate
                if hit:
                    out_data ^= ((self._val(u, r16[u]) & ((1 << self.M) - 1)) << (u * self.M))
                    hits += 1
                    positions.append(self.pos + u)
                    hit_mask |= (1 << u)

        elif mode == 4:  # CLUSTERS
            for u in range(self.S):
                if not (keep >> u) & 1:
                    continue
                pos_u = self.pos + u
                hit = False
                for i in range(self.n_burst):
                    if pos_u >= self.tab_start[i] and pos_u < self.tab_start[i] + self.tab_len[i]:
                        hit = True
                        break
                if hit:
                    out_data ^= ((self._val(u, r16[u]) & ((1 << self.M) - 1)) << (u * self.M))
                    hits += 1
                    positions.append(pos_u)
                    hit_mask |= (1 << u)

        elif mode == 5:  # LOCALIZED
            end = self.loc_start + self.loc_wid
            for u in range(self.S):
                if not (keep >> u) & 1:
                    continue
                pos_u = self.pos + u
                hit = (self.loc_start <= pos_u < end) and (r16[u] < rate)
                if hit:
                    out_data ^= ((self._val(u, r16[u]) & ((1 << self.M) - 1)) << (u * self.M))
                    hits += 1
                    positions.append(pos_u)
                    hit_mask |= (1 << u)

        elif mode == 6:  # BADBLOCK
            for u in range(self.S):
                if not (keep >> u) & 1:
                    continue
                hit = r16[u] < self.rate_eff
                if hit:
                    out_data ^= ((self._val(u, r16[u]) & ((1 << self.M) - 1)) << (u * self.M))
                    hits += 1
                    positions.append(self.pos + u)
                    hit_mask |= (1 << u)

        elif mode == 7:  # DEBUG
            for u in range(self.S):
                if not (keep >> u) & 1:
                    continue
                pos_u = self.pos + u
                dpos = (pos_u - self.dbg_base) if pos_u >= self.dbg_base else (pos_u + self.N - self.dbg_base)
                hit = dpos < count
                if hit:
                    out_data ^= ((self._val(u, r16[u]) & ((1 << self.M) - 1)) << (u * self.M))
                    hits += 1
                    positions.append(pos_u)
                    hit_mask |= (1 << u)

        if last:
            self.pos = 0
            self.first = True
        else:
            self.pos += self.S
            self.first = False

        erasure = hit_mask if mark else 0
        return out_data, keep, last, hits, positions, erasure

    def _val(self, u, r16):
        # The RTL's lane value uses bits [16 +: M] of the 32-bit state.
        # r16 is bits [15:0]; reconstruct the 32-bit state after advance is not
        # directly stored, but the value bits are the next M bits above r16.
        # Since we only have r16 here, we mirror the deterministic property:
        # val = 1 if those M bits are zero else those M bits.  For bit-exact
        # reproduction the model must derive the same M-bit slice the RTL used.
        # We store the full 32-bit state in self.rnd[u]; bits [16 +: M] are
        # available there.
        v = (self.rnd[u] >> 16) & ((1 << self.M) - 1)
        return 1 if v == 0 else v


class ErrorInjectorTB(TBBase):
    """Drives error_injector and scores it against ErrorInjectorModel."""

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

        self.M = int(dut.SYMBOL_WIDTH.value)
        self.S = int(dut.SYMBOLS_PER_BEAT.value)
        self.N = int(dut.N_SYMBOLS.value)
        self.T = int(dut.T_SYMBOLS.value)
        self.DATA_WIDTH = self.M * self.S

        self.model = ErrorInjectorModel(self.M, self.S, self.N, self.T, seed=self.SEED)
        self.checks = 0
        self.mismatches = 0
        self._init_bfms()
        self.log.info(f"ErrorInjectorTB M={self.M} S={self.S} N={self.N} T={self.T} "
                      f"DATA_WIDTH={self.DATA_WIDTH} level={self.TEST_LEVEL} seed={self.SEED}")

    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.DATA_WIDTH, default=0))
        fc_in.add_field(FieldDefinition(name='keep', bits=self.S, default=(1 << self.S) - 1))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        self.master = GAXIMaster(dut=self.dut, title="INJ_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)

        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='data', bits=self.DATA_WIDTH, default=0))
        fc_out.add_field(FieldDefinition(name='keep', bits=self.S, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        fc_out.add_field(FieldDefinition(name='erasure', bits=self.S, default=0))
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

    def symbols_of(self, symbols, keep_override=None):
        """Split a symbol list into (data, keep) beats of S symbols."""
        beats = []
        for i in range(0, len(symbols), self.S):
            chunk = symbols[i:i + self.S]
            data = 0
            for u, sym in enumerate(chunk):
                data |= (sym & ((1 << self.M) - 1)) << (u * self.M)
            if keep_override is not None:
                keep = keep_override[i // self.S]
            else:
                keep = (1 << len(chunk)) - 1
            beats.append((data, keep))
        return beats

    def random_symbols(self, n):
        """Return n random symbols appropriate for the symbol width."""
        mask = (1 << self.M) - 1
        return [random.randint(0, mask) for _ in range(n)]

    async def apply_config(self, mode=0, count=0, rate=0, seed_load=False, clear=False,
                         mark=0, seed=None, cnt_min=0, cnt_max=0, len_min=0, len_max=0):
        if seed is not None:
            self.dut.cfg_seed.value = seed
        self.dut.cfg_mode.value = mode
        self.dut.cfg_count.value = count
        self.dut.cfg_rate.value = rate
        self.dut.cfg_seed_load.value = 1 if seed_load else 0
        self.dut.cfg_clear.value = 1 if clear else 0
        self.dut.cfg_mark_erasure.value = mark
        self.dut.cfg_cnt_min.value = cnt_min
        self.dut.cfg_cnt_max.value = cnt_max
        self.dut.cfg_len_min.value = len_min
        self.dut.cfg_len_max.value = len_max
        await self.wait_clocks(self.clk_name, 1)
        if seed_load and seed is not None:
            self.model.seed_load(seed)
        self.dut.cfg_seed_load.value = 0
        self.dut.cfg_clear.value = 0

    async def send_block(self, symbols, keep_override=None, mark=0, **model_kwargs):
        """Send a block, return list of predicted beats and total hits."""
        beats = self.symbols_of(symbols, keep_override)
        predicted = []
        total_hits = 0
        for data, keep in beats:
            last = 1 if len(predicted) == len(beats) - 1 else 0
            exp_data, exp_keep, exp_last, hits, _, erasure = self.model.process_beat(
                data, keep, last, mark=mark, **model_kwargs)
            predicted.append((exp_data, exp_keep, exp_last, erasure))
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
            out.append((int(pkt.data), int(pkt.keep), int(pkt.last), int(getattr(pkt, 'erasure', 0))))
        return out

    async def run_none_mode(self):
        """Mode 0 must pass through unchanged."""
        await self.apply_config(mode=0, seed_load=True, seed=self.SEED)
        symbols = self.random_symbols(self.N)
        predicted, _ = await self.send_block(symbols, mode=0)
        out = await self.collect_beats(len(predicted))
        for i, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"NONE beat {i}", got, exp)
        return self.mismatches == 0

    async def run_count_mode(self):
        """Mode 1: exact count, distinct positions, and symbol-exact output."""
        await self.apply_config(mode=1, count=0, seed_load=True, seed=self.SEED)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        error_counts = [0, 1, self.T, min(self.N, self.T + 2)]
        if self.N > self.T + 3:
            error_counts.append(self.T + 3)
        all_positions = []
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                count = random.choice(error_counts)
                await self.apply_config(mode=1, count=count)
                symbols = self.random_symbols(self.N)
                predicted, total_hits = await self.send_block(symbols, mode=1, count=count)
                out = await self.collect_beats(len(predicted))
                for j, (got, exp) in enumerate(zip(out, predicted)):
                    self._score(f"COUNT block {i} beat {j}", got, exp)
                self._score(f"COUNT block {i} total hits", total_hits, min(count, self.N))
                # collect positions for uniformity sanity
                pos = 0
                for data, keep, last, _ in predicted:
                    for u in range(self.S):
                        if (keep >> u) & 1:
                            if ((data >> (u * self.M)) & ((1 << self.M) - 1)) != symbols[pos]:
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
        await self.apply_config(mode=2, count=0, seed_load=True, seed=self.SEED)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                count = random.choice([1, self.T, min(self.N, 2 * self.T)])
                await self.apply_config(mode=2, count=count)
                symbols = self.random_symbols(self.N)
                predicted, total_hits = await self.send_block(symbols, mode=2, count=count)
                out = await self.collect_beats(len(predicted))
                for j, (got, exp) in enumerate(zip(out, predicted)):
                    self._score(f"BURST block {i} beat {j}", got, exp)
                # contiguity check on predicted positions
                positions = []
                pos = 0
                for data, keep, last, _ in predicted:
                    for u in range(self.S):
                        if (keep >> u) & 1:
                            if ((data >> (u * self.M)) & ((1 << self.M) - 1)) != symbols[pos]:
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
        """Mode 3: per-symbol flip probability rate/65536, mean within tolerance."""
        await self.apply_config(mode=3, count=0, seed_load=True, seed=self.SEED)
        # Send enough symbols to measure rate; at least 10k valid symbols.
        target_symbols = max(10000, 16 * self.N)
        rate = 1000  # ~1.5 %
        await self.apply_config(mode=3, rate=rate)
        symbols = self.random_symbols(target_symbols)
        predicted, total_hits = await self.send_block(symbols, mode=3, rate=rate)
        out = await self.collect_beats(len(predicted))
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"RATE beat {j}", got, exp)
        valid_symbols = sum(bin(keep).count('1') for _, keep, _, _ in predicted)
        if valid_symbols:
            measured = total_hits / valid_symbols
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
        await self.apply_config(mode=3, rate=5000, seed_load=True, seed=self.SEED)
        symbols = self.random_symbols(self.N)
        n_beats = (self.N + self.S - 1) // self.S
        # zero one lane per beat deterministically
        keeps = []
        for i in range(n_beats):
            keeps.append(((1 << self.S) - 1) & ~(1 << (i % self.S)))
        predicted, _ = await self.send_block(symbols, keep_override=keeps, mode=3, rate=5000)
        out = await self.collect_beats(len(predicted))
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"KEEP beat {j}", got, exp)
        return self.mismatches == 0

    async def run_clusters_mode(self):
        """Mode 4: random burst clusters, geometry and hit distribution checks."""
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        # Choose cluster parameters that keep clusters small relative to N.
        cnt_min, cnt_max = 1, min(4, self.N)
        len_min, len_max = 1, min(8, self.N)
        await self.apply_config(mode=4, seed_load=True, seed=self.SEED,
                                cnt_min=cnt_min, cnt_max=cnt_max,
                                len_min=len_min, len_max=len_max)
        await self.wait_clocks(self.clk_name, 2)
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                symbols = self.random_symbols(self.N)
                predicted, total_hits = await self.send_block(
                    symbols, mode=4, mark=0, cnt_min=cnt_min, cnt_max=cnt_max,
                    len_min=len_min, len_max=len_max)
                out = await self.collect_beats(len(predicted))
                for j, (got, exp) in enumerate(zip(out, predicted)):
                    self._score(f"CLUSTERS block {i} beat {j}", got, exp)

                # Per-block hit bounds (allow overlap shrinkage on lower bound)
                lower = cnt_min * len_min
                upper = cnt_max * len_max
                self.checks += 1
                if total_hits > upper:
                    self.mismatches += 1
                    self.log.error(f"CLUSTERS block {i} hits {total_hits} > upper {upper}")
                if total_hits < lower:
                    # overlap can shrink the lower bound; only flag severe shortage
                    if total_hits == 0 and lower > 0:
                        self.mismatches += 1
                        self.log.error(f"CLUSTERS block {i} no hits but lower bound {lower}")
                    else:
                        self.checks -= 1  # don't count the soft lower-bound check

        # Cluster geometry is already verified per beat by the bit-exact model.
        return self.mismatches == 0

    async def run_localized_mode(self):
        """Mode 5: all hits inside the drawn window, bit-exact beats."""
        await self.apply_config(mode=5, seed_load=True, seed=self.SEED)
        n_blocks = self.BLOCKS[self.TEST_LEVEL]
        combos = [(1, 8, 65535), (4, 32, 10000), (1, min(self.N, 64), 2000)]
        mask = (1 << self.M) - 1
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for i in range(n_blocks):
                len_min, len_max, rate = random.choice(combos)
                if len_max > self.N:
                    len_max = self.N
                if len_min > len_max:
                    len_min = len_max
                await self.apply_config(mode=5, rate=rate, len_min=len_min, len_max=len_max)
                symbols = self.random_symbols(self.N)
                predicted, total_hits = await self.send_block(
                    symbols, mode=5, rate=rate, len_min=len_min, len_max=len_max)
                out = await self.collect_beats(len(predicted))
                for j, (got, exp) in enumerate(zip(out, predicted)):
                    self._score(f"LOCALIZED block {i} beat {j}", got, exp)

                win_start = self.model.loc_start
                win_end = win_start + self.model.loc_wid

                pos = 0
                inside_hits = 0
                for data, keep, last, _ in predicted:
                    for u in range(self.S):
                        if (keep >> u) & 1:
                            hit = ((data >> (u * self.M)) & mask) != symbols[pos]
                            if hit:
                                if not (win_start <= pos < win_end):
                                    self.mismatches += 1
                                    if self.mismatches <= 10:
                                        self.log.error(
                                            f"LOCALIZED block {i} hit at {pos} outside "
                                            f"[{win_start},{win_end})")
                                inside_hits += 1
                            pos += 1
                        if pos >= self.N:
                            break
                if rate == 65535 and self.model.loc_wid > 0 and inside_hits == 0:
                    self.mismatches += 1
                    self.log.error(f"LOCALIZED block {i} density 65535 produced no hits")
        return self.mismatches == 0

    async def run_badblock_mode(self):
        """Mode 6: probability sweep with binomial band on bad-block fraction."""
        await self.apply_config(mode=6, seed_load=True, seed=self.SEED)
        n_blocks = 64
        rate_hi = 65535
        rate_lo = 0
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for p in (0, 32768, 65535):
                await self.apply_config(mode=6, rate=rate_lo, len_min=p, len_max=rate_hi)
                bad_blocks = 0
                total_hits = 0
                for i in range(n_blocks):
                    symbols = self.random_symbols(self.N)
                    predicted, hits = await self.send_block(
                        symbols, mode=6, rate=rate_lo, len_min=p, len_max=rate_hi)
                    out = await self.collect_beats(len(predicted))
                    for j, (got, exp) in enumerate(zip(out, predicted)):
                        self._score(f"BADBLOCK p={p} block {i} beat {j}", got, exp)
                    if self.model.bad:
                        bad_blocks += 1
                    total_hits += hits

                expected_bad = n_blocks * (p / 65536.0)
                if p == 0:
                    if bad_blocks != 0 or total_hits != 0:
                        self.mismatches += 1
                        self.log.error(
                            f"BADBLOCK p=0: {bad_blocks} bad blocks, {total_hits} hits")
                elif p == 65535:
                    if bad_blocks == 0:
                        self.mismatches += 1
                        self.log.error(
                            f"BADBLOCK p=65535: no bad blocks ({total_hits} hits)")
                else:
                    sigma = math.sqrt(n_blocks * (p / 65536.0) * (1.0 - p / 65536.0))
                    if abs(bad_blocks - expected_bad) > 5 * sigma:
                        self.mismatches += 1
                        self.log.error(
                            f"BADBLOCK p={p}: {bad_blocks} bad blocks, expected "
                            f"{expected_bad:.1f} +/- {5 * sigma:.1f}")
        return self.mismatches == 0

    async def run_debug_mode(self):
        """Mode 7: deterministic walking errors, bit-exact and coverage."""
        await self.apply_config(mode=7, seed_load=True, seed=self.SEED)
        counts = [1, 3]
        steps = [1, 7]
        if self.N >= 3:
            steps.append(self.N // 3)
        mask = (1 << self.M) - 1
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for count in counts:
                for step in steps:
                    if step == 0 or step >= self.N:
                        continue
                    gcd = math.gcd(step, self.N)
                    n_blocks = max(self.BLOCKS[self.TEST_LEVEL],
                                   min((2 * self.N) // gcd, 512))
                    await self.apply_config(mode=7, count=count, rate=step)
                    expected = set()
                    base = self.model.dbg_base
                    for b in range(n_blocks):
                        base = (base + step) % self.N
                        for j in range(min(count, self.N)):
                            expected.add((base + j) % self.N)
                    predicted_set = set()
                    total_hits = 0
                    for b in range(n_blocks):
                        symbols = self.random_symbols(self.N)
                        predicted, hits = await self.send_block(
                            symbols, mode=7, count=count, rate=step)
                        out = await self.collect_beats(len(predicted))
                        for j, (got, exp) in enumerate(zip(out, predicted)):
                            self._score(f"DEBUG count={count} step={step} block {b} beat {j}",
                                        got, exp)
                        total_hits += hits
                        pos = 0
                        for data, keep, last, _ in predicted:
                            for u in range(self.S):
                                if (keep >> u) & 1:
                                    if ((data >> (u * self.M)) & mask) != symbols[pos]:
                                        predicted_set.add(pos)
                                    pos += 1
                                if pos >= self.N:
                                    break
                    self._score(
                        f"DEBUG count={count} step={step} set match",
                        predicted_set, expected)
                    want_hits = n_blocks * min(count, self.N)
                    self._score(
                        f"DEBUG count={count} step={step} total hits",
                        total_hits, want_hits)
        return self.mismatches == 0

    async def run_mark_phase(self):
        """Erasure sideband equals the hit mask when cfg_mark_erasure is set."""
        # DEBUG first so its deterministic walk is not disturbed by a RATE run.
        step = 1 if self.N <= 8 else max(1, self.N // 16)
        await self.apply_config(mode=7, count=1, rate=step, mark=1,
                                seed_load=True, seed=self.SEED)
        symbols = self.random_symbols(self.N)
        predicted, _ = await self.send_block(symbols, mode=7, count=1, rate=step, mark=1)
        out = await self.collect_beats(len(predicted))
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"MARK(DEBUG) beat {j}", got, exp)

        await self.apply_config(mode=3, rate=3000, mark=1, seed=self.SEED)
        symbols = self.random_symbols(self.N)
        predicted, _ = await self.send_block(symbols, mode=3, rate=3000, mark=1)
        out = await self.collect_beats(len(predicted))
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"MARK beat {j}", got, exp)
        return self.mismatches == 0

    async def run_backpressure(self):
        """Full backpressure: hold out_ready low and verify no drops."""
        await self.apply_config(mode=1, count=2, seed_load=True, seed=self.SEED)
        self.set_profile('slow')
        symbols = self.random_symbols(self.N)
        predicted, _ = await self.send_block(symbols, mode=1, count=2)
        out = await self.collect_beats(len(predicted), timeout_cycles=100 * self.N + 500)
        for j, (got, exp) in enumerate(zip(out, predicted)):
            self._score(f"BACKPRESSURE beat {j}", got, exp)
        return self.mismatches == 0

    async def run_stats(self):
        """Check statistics counters over a known run."""
        await self.apply_config(mode=1, count=0, seed_load=True, clear=True, seed=self.SEED)
        n_blocks = 4
        total_hits_sum = 0
        blocks_hit = 0
        over_t = 0
        last_hits = 0
        for i in range(n_blocks):
            count = [0, 1, self.T, self.T + 2][i % 4]
            count = min(count, self.N)
            await self.apply_config(mode=1, count=count)
            symbols = self.random_symbols(self.N)
            predicted, total_hits = await self.send_block(symbols, mode=1, count=count)
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
        if int(self.dut.o_inj_symbols.value) != total_hits_sum:
            self.mismatches += 1
            self.log.error(f"stats o_inj_symbols: got {int(self.dut.o_inj_symbols.value)} exp {total_hits_sum}")
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
        await self.apply_config(mode=0, count=0, clear=True)
        await self.wait_clocks(self.clk_name, 2)
        self.checks += 3
        if int(self.dut.o_inj_symbols.value) != 0:
            self.mismatches += 1
        if int(self.dut.o_inj_blocks.value) != 0:
            self.mismatches += 1
        if int(self.dut.o_inj_over_t.value) != 0:
            self.mismatches += 1
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
