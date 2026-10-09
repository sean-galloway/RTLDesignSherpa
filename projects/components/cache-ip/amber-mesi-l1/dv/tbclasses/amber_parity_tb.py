"""
amber parity testbench (cache_sim trace-replay parity, Task 10)

Replays a committed cache_sim trace (word addresses, dv/traces/) through
amber_core and pins hit/miss/miss-class counts EXACTLY against the cache_sim
JS golden model -- PRD success criterion 1:

  per run: hits / misses / compulsory / capacity / conflict, amber vs
  cache_sim, exact equality.  Any drift is a bug in RTL or harness, never
  tolerated.

What this TB does beyond counting (all scored through self._score, any
mismatch fails the cell):
  * streaming replay: the whole trace is queued through the house GAXI
    master's send_burst, so requests are presented back-to-back at accept
    rate (no lockstep per-access round trip)
  * per-access DUT outcome: every accepted request resolves through exactly
    one pass -- a miss passes MISS_VICTIM (flag sampled at state entry), a
    hit never does; the response (in request order, the pipeline is
    blocking/in-order) folds the flag into the recorded outcome
  * per-access model parity: a faithful Python port of model.js
    Cache.access (NOT the amber rank/ring view -- the JS list view) is
    stepped in lockstep; its hit/miss per access must equal the DUT
    outcome.  For LRU/FIFO this is the native-parity argument made
    per-access; for RANDOM the port carries the recorded LFSR extension, so
    the victim WAY of every miss is pinned against the observed
    repl_victim_way as well (deterministic per-set draw count)
  * miss classification: shadow fully-associative model (sets=1,
    ways=SETS*WAYS) with the identical algorithm to model.js simulate():
    first-ever block -> compulsory, else FA miss -> capacity, else conflict
  * read-data check: the grid replays reads only (cache_sim models a
    read-only footprint; writes would replay as same-footprint
    write-allocate accesses), so cache content always equals the memory
    model and every response beat is checked against it
  * totals cross-check: the five counters are compared against the JS
    golden totals the pytest wrapper computed (PARITY_EXPECT env, JSON);
    the result JSON is written to PARITY_OUT for the wrapper's
    defense-in-depth re-comparison

mon_time is a core input; this TB sources it with the same free-running
counter the Task 9 TB uses (rig-level sourcing is Task 11).

Inherits the GAXI stimulus path, memory responders, MonBus plumbing and
scoring idioms from AmberCoreTB; the oracle/coherence model machinery and
directed scenarios are unused here (parity cells run no snoops -- the
cache_sim golden has no coherence).

Author: RTL Design Sherpa
Created: 2026-10-09
"""

import json
import os
import random

import cocotb
from cocotb.triggers import FallingEdge, Timer

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_core_tb import (
    AmberCoreTB,
    ST_MISS_VICTIM,
    ST_ERROR,
)
from projects.components.cache_ip.amber_mesi_l1.dv.golden.cache_sim_harness import (
    COUNT_KEYS,
    LfsrRng,
    POLICY_BY_REPL,
    check_totals,
    parse_address_text,
)


class ModelJsCache:
    """Faithful Python port of model.js Cache + Cache.prototype.access.

    Way numbering is the JS model's (first-null preference for LRU/FIFO),
    NOT amber's rank/ring permutation: for LRU/FIFO the DUT's abstract
    recency order matches this model's up to a consistent way renaming, so
    per-access hit/miss parity holds exactly.  For RANDOM, policy is the
    recorded LFSR extension (draw on EVERY miss, no empty-way preference),
    which is way-for-way the amber_repl LFSR, so per-access victim-way
    parity holds exactly too.
    """

    def __init__(self, sets, ways, block_words, policy):
        assert policy in ('LRU', 'FIFO', 'RANDOM')
        self.sets = sets
        self.ways = ways
        self.policy = policy
        self.block_shift = (block_words - 1).bit_length()
        self.set_bits = (sets - 1).bit_length()
        self.tags = [[None] * ways for _ in range(sets)]
        self.lru = [[] for _ in range(sets)]
        self.fifo = [[] for _ in range(sets)]
        # per-set LFSR for the recorded RANDOM extension; every set starts
        # at REPL_SEED exactly like amber_repl
        self.lfsr = [LfsrRng() for _ in range(sets)] if policy == 'RANDOM' \
            else None

    @staticmethod
    def _move_to_back(lst, val):
        try:
            lst.remove(val)
        except ValueError:
            pass
        lst.append(val)

    def access(self, word):
        """One access; returns (hit, set_index, way) exactly like model.js."""
        block = word >> self.block_shift
        if self.sets == 1:
            set_idx = 0
            tag = block
        else:
            set_idx = block & (self.sets - 1)
            tag = block >> self.set_bits
        stags = self.tags[set_idx]

        way = -1
        for w in range(self.ways):
            if stags[w] is not None and stags[w] == tag:
                way = w
                break
        if way != -1:
            if self.policy == 'LRU':
                self._move_to_back(self.lru[set_idx], way)
            return True, set_idx, way

        if self.policy == 'RANDOM':
            # recorded extension: no empty-way preference; every miss draws
            way = self.lfsr[set_idx].next_int(self.ways)
        else:
            for w in range(self.ways):
                if stags[w] is None:
                    way = w
                    break
            if way == -1:
                if self.policy == 'LRU':
                    way = self.lru[set_idx].pop(0)
                else:  # FIFO
                    way = self.fifo[set_idx].pop(0)
        stags[way] = tag
        if self.policy == 'LRU':
            self._move_to_back(self.lru[set_idx], way)
        elif self.policy == 'FIFO':
            self.fifo[set_idx].append(way)
        return False, set_idx, way


class AmberParityTB(AmberCoreTB):
    """Trace-replay parity TB; see module docstring."""

    SEND_CHUNK = 8192

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        random.seed(self.SEED)

        self.POLICY = POLICY_BY_REPL.get(self.REPL_POLICY)
        if self.POLICY in (None, 'TREE_PLRU'):
            raise ValueError(f'parity grid does not cover REPL_POLICY='
                             f'{self.REPL_POLICY} ({self.POLICY})')

        trace_path = os.environ['PARITY_TRACE']
        with open(trace_path, 'r', encoding='utf-8') as fh:
            self.words = parse_address_text(fh.read())
        if not self.words:
            raise ValueError(f'{trace_path}: empty trace')
        self.N = len(self.words)
        self.ext_policy = self.POLICY == 'RANDOM'

        block_words = self.LINE_BYTES // 4
        self.block_shift = (block_words - 1).bit_length()
        # per-access DUT reference (model.js view) + FA shadow (model.js
        # simulate(): sets=1, ways=SETS*WAYS, same policy)
        self.main_model = ModelJsCache(self.SETS, self.WAYS, block_words,
                                       self.POLICY)
        self.fa_model = ModelJsCache(1, self.SETS * self.WAYS, block_words,
                                     self.POLICY)
        self.global_blocks = set()
        self.totals = {k: 0 for k in COUNT_KEYS}

        # expectation + report plumbing (filled by the pytest wrapper)
        self.expected = json.loads(os.environ['PARITY_EXPECT'])
        self.out_path = os.environ.get('PARITY_OUT', '')
        n_exp = self.expected.get('num_accesses')
        if n_exp is not None and n_exp != self.N:
            raise ValueError(f'trace parse mismatch: TB {self.N} accesses '
                             f'vs golden {n_exp}')

        # replay bookkeeping
        self.n_accepts = 0
        self.processed = 0
        self.data_checks = 0
        self.victim_checks = 0
        self._pass_miss = False
        self.outcomes = []          # per response, snapshot at the handshake
        self._victims_observed = []

        self.log.info(f'AmberParityTB policy={self.POLICY} trace={os.path.basename(trace_path)} '
                      f'N={self.N} seed={self.SEED}')

    # ------------------------------------------------------------------
    # monitor: leaner than the Task 9 integration monitor -- no snoops, no
    # coherence taps; records pass flags, victim ways, accepts, mon_time
    # ------------------------------------------------------------------
    async def _monitor(self):
        d = self.dut
        prev_state = -1
        while True:
            await FallingEdge(d.clk)
            await Timer(100, units='ps')
            self.cyc += 1
            d.mon_time.value = self.cyc

            st = int(d.ctrl_state.value)
            if st != prev_state:
                if st == ST_MISS_VICTIM:
                    # first MISS_VICTIM cycle of a pass: repl_req is high,
                    # repl_victim_way presents the current LFSR/rank value,
                    # and the LFSR advances at the end of this cycle
                    self._pass_miss = True
                    self._victims_observed.append(
                        int(d.u_repl.repl_victim_way.value))
                prev_state = st

            if int(d.cpu_req_wr_valid.value) \
                    and int(d.cpu_req_wr_ready.value):
                self.n_accepts += 1

    # ------------------------------------------------------------------
    # response observation: the pass flag is consumed AT the response
    # handshake (inside the slave callback -- synchronous, so the monitor
    # cannot interleave).  Responses are in request order (blocking
    # pipeline), so outcomes[k] belongs to words[k].
    # ------------------------------------------------------------------
    def _on_rsp(self, packet):
        data = int(getattr(packet, 'fields', {}).get('data', 0))
        self.rsp_log.append((self.cyc, data))
        self.outcomes.append(self._pass_miss)
        self._pass_miss = False

    # ------------------------------------------------------------------
    # per-response scoring (responses are in request order)
    # ------------------------------------------------------------------
    def _score_response(self, idx, data):
        word = self.words[idx]
        miss = self.outcomes[idx]

        mhit, _mset, mway = self.main_model.access(word)
        self.checks += 1
        if mhit == miss:
            self.mismatches += 1
            if self.mismatches <= 30:
                self.log.error(
                    f'CHECK FAIL: access {idx} (word {word:#x}): DUT '
                    f'{"miss" if miss else "hit"} vs model '
                    f'{"miss" if not mhit else "hit"}')

        if miss:
            if self.ext_policy:
                obs = self._victims_observed.pop(0)
                self.checks += 1
                self.victim_checks += 1
                if obs != mway:
                    self.mismatches += 1
                    if self.mismatches <= 30:
                        self.log.error(
                            f'CHECK FAIL: access {idx} victim way: '
                            f'DUT {obs} vs LFSR model {mway}')
            block = word >> self.block_shift
            fahit, _, _ = self.fa_model.access(word)
            self.totals['misses'] += 1
            if block not in self.global_blocks:
                self.totals['compulsory'] += 1
            elif not fahit:
                self.totals['capacity'] += 1
            else:
                self.totals['conflict'] += 1
        else:
            self.totals['hits'] += 1
            self.fa_model.access(word)
        self.global_blocks.add(word >> self.block_shift)

        # read data vs the memory model: the grid replays reads only, so
        # cache content never diverges from memory
        byte_addr = (word << 2) & ((1 << self.ADDR_WIDTH) - 1)
        line = self._line_of(byte_addr)
        beat = (byte_addr >> (self.STRB_W.bit_length() - 1)) \
            & (self.FILL_BEATS - 1)
        exp = self._beat_of_line(self._mem_line(line), beat)
        self.checks += 1
        self.data_checks += 1
        if data != exp:
            self.mismatches += 1
            if self.mismatches <= 30:
                self.log.error(f'CHECK FAIL: access {idx} rsp data: '
                               f'got {data:#x} expected {exp:#x}')

    def _drain_responses(self):
        while len(self.rsp_log) > self.processed:
            _cyc, data = self.rsp_log[self.processed]
            self._score_response(self.processed, data)
            self.processed += 1

    # ------------------------------------------------------------------
    # replay
    # ------------------------------------------------------------------
    async def _prefill_trace_span(self):
        """Deterministic memory content for every line the trace touches
        (super() pre-fills SPAN lines; long traces span more)."""
        max_line = self._line_of(max(w << 2 for w in self.words)) + 1
        for line in range(self.SPAN, max_line):
            self.memory_model.write(self._base_of(line),
                                    bytearray(self._default_line(line)))

    async def run(self):
        await self._prefill_trace_span()
        full_be = (1 << self.STRB_W) - 1

        # stream the trace: chunked send_burst keeps the request pipeline
        # full; responses are drained between chunks and at the end
        for i in range(0, self.N, self.SEND_CHUNK):
            pkts = [self.master.create_packet(
                data=self._pack_req((w << 2), 0, full_be, 0))
                for w in self.words[i:i + self.SEND_CHUNK]]
            await self.master.send_burst(pkts)
            self._drain_responses()
            self.log.info(f'replay {self.processed}/{self.N} '
                          f'(cycle {self.cyc})')

        # final drain: every accepted request must get exactly one response
        for _ in range(self.N * 60 + 200000):
            self._drain_responses()
            if self.processed >= self.N:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError(
                f'response timeout: {self.processed}/{self.N} responses '
                f'after {self.N * 60 + 200000} cycles')

        # -- end-of-run cross-checks -------------------------------------
        self._score('accepts == accesses', self.n_accepts, self.N)
        self._score('responses == accesses', self.processed, self.N)
        self._score('outcomes == accesses', len(self.outcomes), self.N)
        self._score('no dangling miss pass', self._pass_miss, False)
        if self.ext_policy:
            self._score('all observed victims consumed',
                        len(self._victims_observed), 0)
        self._check_totals_vs_golden()

        await self.wait_clocks('clk', 10)
        self._score('quiescent: no monbus valid at end',
                    int(self.dut.mon_valid.value), 0)
        self._score('quiescent: ctrl not in ERROR',
                    int(self.dut.ctrl_state.value) == ST_ERROR, False)

        report = self.get_test_report()
        if self.out_path:
            with open(self.out_path, 'w', encoding='utf-8') as fh:
                json.dump(report, fh, indent=2)
        self.log.info(f'Parity report: {report}')
        return self.mismatches == 0

    def _check_totals_vs_golden(self):
        exp = {k: self.expected['totals'][k] for k in COUNT_KEYS}
        for k in COUNT_KEYS:
            self._score(f'parity totals {k}: amber vs cache_sim',
                        self.totals[k], exp[k])
        diffs = check_totals(self.totals, exp, label='golden-recompare: ')
        for d in diffs:
            self.log.error(d)

    def get_test_report(self):
        return {
            'policy': self.POLICY,
            'sets': self.SETS,
            'ways': self.WAYS,
            'line_bytes': self.LINE_BYTES,
            'n_accesses': self.N,
            'totals': dict(self.totals),
            'golden_totals': {k: self.expected['totals'][k] for k in COUNT_KEYS},
            'checks': self.checks,
            'mismatches': self.mismatches,
            'data_checks': self.data_checks,
            'victim_checks': self.victim_checks,
            'n_accepts': self.n_accepts,
        }
