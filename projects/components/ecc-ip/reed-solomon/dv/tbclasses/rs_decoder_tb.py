"""
rs_decoder_core testbench

GAXIMaster drives `in_` (data, keep, last) with received blocks, GAXISlave
drains `out_` (data, keep, last, status_*), and every block is scored against
RSModel.decode -- itself validated against reedsolo -- for the k data symbols,
out_last on the k-th, and the verdict carried with it.

Scenarios:
  blocks        clean blocks and 1 .. t random errors, back to back
  uncorrectable t+1 and more errors: the verdict must match the model
                (uncorrectable, or the identical miscorrection when the code
                itself cannot tell), and the data must be as received when
                uncorrectable
  framing       short and long blocks pass through with frame_err, then a good
                block decodes cleanly
  backpressure  the block mix under randomized valid/ready profiles
  throughput    several blocks back to back: about n cycles per block once
                the pipeline is full, after a 2n + 2t latency to the first
                symbol (a block is released only with its verdict)

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import os
import random

from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import quick_config

from projects.components.ecc_ip.reed_solomon.dv.tbclasses.rs_model import RSModel


class RSDecoderTB(TBBase):
    BLOCKS = {'gate': 6, 'func': 32, 'full': 128}
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
        self.SC_W = int(dut.STATUS_CNT_WIDTH.value)
        # ERASURE_SUPPORT is a bit parameter, readable: the erasure scenarios
        # score against the model's erasure path when it is on, and against
        # the errors-only path (the dedicated off-state test) when it is not.
        self.ERASURE = bool(int(dut.ERASURE_SUPPORT.value))
        self.Q = 1 << self.M
        self.model = RSModel(self.M, self.PRIM, self.T, self.N, self.B)
        # the DUT's KES_ALGO is a string parameter cocotb cannot read back; the runner
        # passes the same choice in the environment so the model uses the same solver
        self.KES = os.environ.get('KES_ALGO', 'RIBM').lower()
        self.checks = 0
        self.mismatches = 0
        self._init_bfms()
        self.log.info(f"RSDecoderTB RS({self.N},{self.K}) t={self.T} m={self.M} "
                      f"prim=0x{self.PRIM:X} b={self.B} level={self.TEST_LEVEL} seed={self.SEED}")

    def _init_bfms(self):
        fc_in = FieldConfig()
        fc_in.add_field(FieldDefinition(name='data', bits=self.M * self.S, default=0))
        fc_in.add_field(FieldDefinition(name='keep', bits=self.S, default=(1 << self.S) - 1))
        fc_in.add_field(FieldDefinition(name='last', bits=1, default=0))
        # dead when ERASURE_SUPPORT = 0; driven in both states (that is the test)
        fc_in.add_field(FieldDefinition(name='erasure', bits=self.S, default=0))
        self.master = GAXIMaster(dut=self.dut, title="RS_IN", prefix="in_", clock=self.clk,
                                 field_config=fc_in, pkt_prefix="", multi_sig=True, log=self.log)
        fc_out = FieldConfig()
        fc_out.add_field(FieldDefinition(name='data', bits=self.M * self.S, default=0))
        fc_out.add_field(FieldDefinition(name='keep', bits=self.S, default=0))
        fc_out.add_field(FieldDefinition(name='last', bits=1, default=0))
        fc_out.add_field(FieldDefinition(name='status_ok', bits=1, default=0))
        fc_out.add_field(FieldDefinition(name='status_corrected', bits=self.SC_W, default=0))
        fc_out.add_field(FieldDefinition(name='status_uncorrectable', bits=1, default=0))
        fc_out.add_field(FieldDefinition(name='status_frame_err', bits=1, default=0))
        self.slave = GAXISlave(dut=self.dut, title="RS_OUT", prefix="out_", clock=self.clk,
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

    # -- stimulus --------------------------------------------------------------
    def make_received(self, errors, length=None, erasures=0, corrupt_erasures=True):
        """(symbols, flags): a codeword of the profile with `errors` symbol
        errors and `erasures` flagged positions, flags[p] = 1 at each. A
        flagged position is UNTRUSTED -- corrupted by default, left clean on
        request (a conservative flag is legal). `length` other than n builds a
        mis-framed block (a truncated or padded codeword)."""
        data = [random.randrange(self.Q) for _ in range(self.K)]
        rx = self.model.encode(data)
        flags = [0] * self.N
        pos = random.sample(range(self.N), errors + erasures)
        for p in pos[:errors]:
            rx[p] ^= random.randrange(1, self.Q)
        for p in pos[errors:]:
            flags[p] = 1
            if corrupt_erasures:
                rx[p] ^= random.randrange(1, self.Q)
        if length is not None and length != self.N:
            rx = rx[:length] if length < self.N else rx + [random.randrange(self.Q)
                                                           for _ in range(length - self.N)]
            flags = flags[:length] if length < self.N else flags + [0] * (length - self.N)
        return rx, flags

    def beats_of(self, symbols, flags=None):
        """(data, keep, erasure) beats of S, low lane first; only the last may
        be partial."""
        beats = []
        for i in range(0, len(symbols), self.S):
            chunk = symbols[i:i + self.S]
            data = 0
            erase = 0
            for u, sym in enumerate(chunk):
                data |= sym << (u * self.M)
                if flags and flags[i + u]:
                    erase |= 1 << u
            beats.append((data, (1 << len(chunk)) - 1, erase))
        return beats

    def n_beats(self, n_symbols):
        return (n_symbols + self.S - 1) // self.S

    async def send_block(self, rx, flags=None, wait=True):
        beats = self.beats_of(rx, flags)
        for i, (d, k, er) in enumerate(beats):
            pkt = self.master.create_packet(data=d, keep=k, erasure=er,
                                            last=1 if i == len(beats) - 1 else 0)
            if wait:
                await self.master.send(pkt)
            else:
                await self.master._driver_send(pkt, sync=True)

    async def collect(self, count, timeout_cycles):
        """Wait for `count` output BEATS; return one dict per beat."""
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
            p = self.slave._recvQ.popleft()
            out.append(dict(data=int(p.data), keep=int(p.keep), last=int(p.last), ok=int(p.status_ok),
                            corrected=int(p.status_corrected),
                            uncorrectable=int(p.status_uncorrectable),
                            frame_err=int(p.status_frame_err)))
        return out

    def symbols_of(self, out):
        syms = []
        for o in out:
            for u in range(self.S):
                if o['keep'] >> u & 1:
                    syms.append((o['data'] >> (u * self.M)) & (self.Q - 1))
        return syms

    # -- scoring ---------------------------------------------------------------
    def expected(self, rx, flags=None):
        """(data symbols, status dict) the core must produce for this block.
        The flags reach the model only on an ERASURE_SUPPORT build; in the off
        state the same flagged block must decode ERRORS-ONLY, and that
        comparison is the parameter's dedicated off-state test."""
        if len(rx) != self.N:
            n_data = len(rx) - 2 * self.T if len(rx) > 2 * self.T else len(rx)
            return rx[:n_data], dict(ok=0, corrected=0, uncorrectable=0, frame_err=1)
        er = [i for i, f in enumerate(flags) if f] if (flags and self.ERASURE) else None
        data, status, cnt = self.model.decode(rx, kes=self.KES, erasures=er)
        return data, dict(ok=1 if status == 'ok' else 0,
                          corrected=cnt if status == 'corrected' else 0,
                          uncorrectable=1 if status == 'uncorrectable' else 0,
                          frame_err=0)

    def score_block(self, label, rx, out, flags=None):
        exp_data, exp_status = self.expected(rx, flags)
        self.checks += 1
        got_data = self.symbols_of(out)
        lasts = [o['last'] for o in out]
        # keeps: full except the final beat, which is low-aligned
        keeps_ok = all(o['keep'] == (1 << self.S) - 1 for o in out[:-1]) and \
            (not out or out[-1]['keep'] == (1 << (len(exp_data) - (len(out) - 1) * self.S)) - 1)
        ok = got_data == exp_data and lasts == [0] * (len(out) - 1) + [1] and keeps_ok
        if ok:
            # the verdict is held on every beat of the block
            sts = [dict(ok=o['ok'], corrected=o['corrected'], uncorrectable=o['uncorrectable'],
                        frame_err=o['frame_err']) for o in out]
            ok = all(st == exp_status for st in sts)
            if not ok and self.mismatches < 10:
                self.log.error(f"{label}: status {sts[-1]} (constant={len(set(map(str, sts))) == 1}) "
                               f"expected {exp_status}")
        elif self.mismatches < 10:
            bad = next((i for i, (g, e) in enumerate(zip(got_data, exp_data)) if g != e), None)
            self.log.error(f"{label}: {len(got_data)} symbols in {len(out)} beats vs {len(exp_data)}; "
                           f"first data mismatch at {bad}; lasts ok={lasts == [0] * (len(out) - 1) + [1]}; "
                           f"keeps ok={keeps_ok}")
        if not ok:
            self.mismatches += 1
        return ok

    async def run_one(self, label, rx, flags=None):
        await self.send_block(rx, flags)
        exp_data, _ = self.expected(rx, flags)
        out = await self.collect(self.n_beats(len(exp_data)), timeout_cycles=40 * self.N + 400)
        return self.score_block(label, rx, out, flags)

    # -- scenarios ------------------------------------------------------------
    async def run_blocks(self):
        self.set_profile('backtoback')
        n = self.BLOCKS[self.TEST_LEVEL]
        mix = [0, 1, self.T] + [random.randint(0, self.T) for _ in range(max(0, n - 3))]
        for i, e in enumerate(mix):
            await self.run_one(f"block {i} ({e} errors)", *self.make_received(e))
        return self.mismatches == 0

    async def run_uncorrectable(self):
        self.set_profile('constrained')
        n = max(3, self.BLOCKS[self.TEST_LEVEL] // 2)
        for i in range(n):
            e = random.choice([self.T + 1, self.T + 1, self.T + 2, min(self.N, 2 * self.T + 3)])
            e = min(e, self.N)
            await self.run_one(f"uncorrectable {i} ({e} errors)", *self.make_received(e))
        return self.mismatches == 0

    async def run_framing(self):
        self.set_profile('constrained')
        await self.run_one("short block", *self.make_received(0, length=max(1, self.N - 3)))
        if self.N < self.Q - 1:
            await self.run_one("long block", *self.make_received(0, length=self.N + 2))
        await self.run_one("one-symbol block", *self.make_received(0, length=1))
        await self.run_one("clean block after framing", *self.make_received(1))
        return self.mismatches == 0

    async def run_backpressure(self):
        for profile in self.PROFILES[self.TEST_LEVEL]:
            self.set_profile(profile)
            for e in (0, self.T, self.T + 1):
                await self.run_one(f"profile {profile} ({e} errors)", *self.make_received(e))
        return self.mismatches == 0

    # -- erasure scenarios (TASK-002) ------------------------------------------
    def erasure_cells(self):
        """(errors, erasures, corrupt) cells at and past the 2e + f = 2t bound:
        f-only decodes (including the t_zero path and flags on clean symbols),
        the boundary itself, the first past-bound mixes, and f = 2t+1 (f_over,
        uncorrectable by inspection)."""
        t2 = 2 * self.T
        cells = [(0, 1, True), (0, self.T, True), (0, t2, True),
                 (0, min(self.T, 2), False)]
        step = max(1, (self.T + 1) // 3)
        cells += [(e, t2 - 2 * e, True) for e in range(0, self.T + 1, step)]
        past = [(1, t2, True), (2, t2 - 2, True), (0, t2 + 1, True)]
        cells += past[:1] if self.TEST_LEVEL == 'gate' else past
        return [(e, f, c) for e, f, c in cells if f <= t2 + 1 and e + f <= self.N]

    async def run_erasures(self):
        """TASK-002: the erasure path. On an ERASURE_SUPPORT build the flagged
        positions decode by the model's erasure method (scored in expected());
        OFF the build the very same stimulus must decode ERRORS-ONLY -- the
        flags are dead -- which is the parameter's dedicated off-state test."""
        self.set_profile('constrained')
        self.log.info(f"run_erasures: {'ERASURE_SUPPORT on' if self.ERASURE else 'OFF-STATE: flags must be dead'}")
        for i, (e, f, corrupt) in enumerate(self.erasure_cells()):
            await self.run_one(f"erasure {i} ({e} errors, {f} flags, corrupt={corrupt})",
                               *self.make_received(e, erasures=f, corrupt_erasures=corrupt))
        return self.mismatches == 0

    async def run_no_dead_cycles(self):
        """The per-block cost must be n/S beats and nothing more.

        Measured as a SLOPE: run B blocks, then 2B, and difference them. That
        cancels every fixed cost -- receive latency, the solve, the correction
        walk, the verdict cycle -- so what is left is purely the per-block
        increment. No latency model to be wrong about, which is what made the
        old upper-bound check unable to see the stall it was written around.

        A codeword is n/S beats, so n/S cycles per block IS the bus. Anything
        above it is a dead cycle at the block boundary, and dead cycles are
        the failure -- latency is not.

        TASK-002: the ERASURE build's stage B runs TRANS + solve + COMB
        serially (the validated algorithm shape), occupying f + 2t + deg_e +
        5 cycles per block; when that exceeds the codeword's beats the intake
        is solve-stage-bound, not bus-bound, and the codeword rate is not
        achievable. These blocks drive t errors with no flags (deg_e = t,
        f = 0), so the erasure rate is max(n/S, 3t + 5) -- exact on every
        matrix profile. The errors-only build keeps the strict n/S contract.
        """
        self.set_profile('backtoback')
        nb = self.n_beats(self.N)
        kb = self.n_beats(self.K)
        rate = max(nb, 3 * self.T + 5) if self.ERASURE else nb
        took = {}
        for blocks in (4, 8):
            self.slave._recvQ.clear()
            rxs = [self.make_received(self.T) for _ in range(blocks)]
            for rx, fl in rxs:
                await self.send_block(rx, fl, wait=False)
            cycles, start = 0, None
            while len(self.slave._recvQ) < blocks * kb:
                await RisingEdge(self.clk)
                cycles += 1
                if start is None and int(self.dut.in_valid.value) and int(self.dut.in_ready.value):
                    start = cycles
                if cycles > 40 * self.N * blocks + 400:
                    break
            out = await self.collect(blocks * kb, timeout_cycles=10)
            for i, (rx, fl) in enumerate(rxs):
                self.score_block(f"slope {blocks} blk {i}", rx, out[i * kb:(i + 1) * kb], fl)
            took[blocks] = cycles - (start or 0)

        slope = (took[8] - took[4]) / 4.0
        dead = slope - rate
        self.checks += 1
        self.log.info(f"no-dead-cycles: {took[4]} cycles for 4 blocks, {took[8]} for 8 "
                      f"-> slope {slope:.2f} cycles/block vs rate {rate} "
                      f"({dead:+.2f} dead per block)")
        if dead > 0.25:
            self.mismatches += 1
            self.log.error(f"{dead:.2f} DEAD cycles per block: the slope is {slope:.2f} "
                           f"against a per-block rate of {rate}. Latency is free; a gap at "
                           f"the block boundary is not.")
        return self.mismatches == 0

    async def run_throughput(self):
        """Blocks back to back with no delays anywhere: total time for B blocks
        must be within B*n + latency, where latency is n + 2t + margin."""
        self.set_profile('backtoback')
        blocks = 4
        rxs = [self.make_received(self.T) for _ in range(blocks)]
        for rx, fl in rxs:
            await self.send_block(rx, fl, wait=False)
        cycles = 0
        start = None
        kb = self.n_beats(self.K)
        nb = self.n_beats(self.N)
        while len(self.slave._recvQ) < blocks * kb:
            await RisingEdge(self.clk)
            cycles += 1
            if start is None and int(self.dut.in_valid.value) and int(self.dut.in_ready.value):
                start = cycles
            if cycles > 40 * self.N * blocks + 400:
                break
        out = await self.collect(blocks * kb, timeout_cycles=10)
        for i, (rx, fl) in enumerate(rxs):
            self.score_block(f"throughput block {i}", rx, out[i * kb:(i + 1) * kb], fl)
        elapsed = cycles - (start or 0)
        # An UPPER bound with a per-block allowance of the rate + 1 and a
        # 16-cycle margin. It cannot catch dead cycles coming back, because
        # it was written to permit the one the design used to have -- so
        # run_no_dead_cycles below measures the SLOPE instead, which needs no
        # latency estimate at all. This bound stays as a coarse smoke check.
        # TASK-002: the erasure build's per-block rate is max(n/S, 3t + 5)
        # (stage B is solve-stage-bound below that; see run_no_dead_cycles).
        per_block = max(nb + 1, 3 * self.T + 6) if self.ERASURE else nb + 1
        bound = blocks * per_block + 2 * nb + 2 * self.T + 16
        self.checks += 1
        self.log.info(f"throughput: {blocks} blocks of {nb} beats in {elapsed} cycles from first accept "
                      f"(bound {bound}; steady state {(elapsed - 2 * nb - 2 * self.T) / blocks:.1f} "
                      f"cycles/block vs rate + 1 = {per_block})")
        if elapsed > bound:
            self.mismatches += 1
            self.log.error(f"throughput: {elapsed} cycles exceeds {bound}")
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
