"""
jet cache_sim trace-replay parity testbench (Task 12)

Replays a committed cache_sim trace (word addresses, amber's
dv/traces/) through jet_top and pins hit/miss/miss-class counts EXACTLY
against the cache_sim JS golden model (bin/apps/cache_sim/js/model.js,
via dv/golden/cache_sim_harness.py) -- the amber parity grid's criterion
re-run on jet (MAS ch06/02: the policy axis is cache_sim-parity).

What this TB does beyond the amber parity TB it is modelled on:

  * the DUT is jet_top (non-blocking MSHR cache), driven through the
    JetCoreTB event-stream scoreboard, so every response / fill beat /
    drain / victim way is ALSO lockstep-scored (the parity cell is a
    full core run, not a counter pass);
  * the replay is merge-free BY CONSTRUCTION: the trace is chunked into
    bursts with no repeated line inside a burst, with a full quiesce
    (every fill committed and retired) between bursts.  A merge is a hit
    that does not move LRU state, while model.js's hit WOULD reorder --
    with merges impossible, jet's update-at-alloc is cache_sim's
    access-time install, and per-access hit/miss parity is exact for
    every policy (the claim-suppressed stale-tag hit resolves to a miss
    in both models at the same access: the evicting alloc is the same
    point in the access order);
  * per-access model parity: the faithful Python port of model.js
    Cache.access (ModelJsCache, amber_parity_tb) steps in lockstep with
    the accept log; for RANDOM the recorded-LFSR extension semantics
    apply (one draw per miss == one draw per alloc -- jet's repl_req
    fires only at the alloc, so a claim-aware stall never re-draws);
    the victim WAY of every alloc is pinned against the per-set LFSR by
    the inherited scoreboard;
  * miss classification: shadow fully-associative model (sets=1,
    ways=SETS*WAYS), the identical algorithm to model.js simulate();
  * totals cross-check against the JS golden totals the pytest wrapper
    computed (PARITY_EXPECT env, JSON); the report JSON is written to
    PARITY_OUT for the wrapper's defense-in-depth re-comparison.

Parity cells run no snoops (the cache_sim golden has no coherence --
same constraint as amber's parity grid).

Author: RTL Design Sherpa
Created: 2026-10-29
"""

import json
import os
import random

import cocotb

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_parity_tb import (
    ModelJsCache,
)
from projects.components.cache_ip.amber_mesi_l1.dv.golden.cache_sim_harness import (
    COUNT_KEYS,
    POLICY_BY_REPL,
    check_totals,
    parse_address_text,
)
from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_core_tb import (
    JetCoreTB,
)


class JetParityTB(JetCoreTB):
    """Trace-replay parity TB for jet_top; see the module docstring."""

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

        block_words = self.LINE_BYTES // 4
        self.block_shift = (block_words - 1).bit_length()
        max_line = max(w >> self.block_shift for w in self.words)
        if max_line >= self.PRELOAD_LINES:
            raise ValueError(f'trace span (line {max_line:#x}) exceeds '
                             f'the preloaded memory '
                             f'({self.PRELOAD_LINES} lines)')
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

        self.log.info(f'JetParityTB policy={self.POLICY} '
                      f'trace={os.path.basename(trace_path)} '
                      f'N={self.N} seed={self.SEED}')

    # ------------------------------------------------------------------
    # per-access scoring (accept order == access order)
    # ------------------------------------------------------------------
    def _score_access(self, k):
        word = self.words[k]
        miss = self.accept_log[k] == 'alloc'

        mhit, _mset, _mway = self.main_model.access(word)
        self._score(f'access {k} (word {word:#x}): hit/miss parity',
                    miss, not mhit)

        block = word >> self.block_shift
        if miss:
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
        self.global_blocks.add(block)

    def _check_totals_vs_golden(self):
        exp = {k: self.expected['totals'][k] for k in COUNT_KEYS}
        for k in COUNT_KEYS:
            self._score(f'parity totals {k}: jet vs cache_sim',
                        self.totals[k], exp[k])
        diffs = check_totals(self.totals, exp, label='golden-recompare: ')
        for d in diffs:
            self.log.error(d)

    # ------------------------------------------------------------------
    # replay
    # ------------------------------------------------------------------
    async def run(self):
        # wait out the D-3 init walk (no probe: the trace owns every
        # access, so an init-walk probe read would corrupt the totals)
        await self._s_init_walk_recover()
        full_be = (1 << self.STRB_W) - 1
        N = self.N
        i = 0
        n_bursts = 0
        while i < N:
            # merge-free burst: no repeated LINE inside a burst, and a
            # full quiesce between bursts, so no access ever meets an
            # in-flight fill of its own line (see the module docstring)
            seen = set()
            j = i
            while j < N:
                ln = self.words[j] >> self.block_shift
                if ln in seen:
                    break
                seen.add(ln)
                j += 1
            ns = []
            for k in range(i, j):
                n = await self._send((self.words[k] << 2)
                                     & ((1 << self.ADDR_WIDTH) - 1),
                                     0, be=full_be, wdata=0,
                                     label=f'p{k}')
                ns.append(n)
            for n in ns:
                await self._await_rsp(n, 'parity')
            # quiesce: every fill committed AND retired, so the next
            # burst sees only installed tags (and the response sequencer
            # has drained -- the deposits land with the commit)
            for _ in range(self.RSP_TIMEOUT_CYCLES):
                if not self.entries and not self.unlaunched:
                    break
                await self._negedge_settled()
            else:
                raise RuntimeError('parity: fills never quiesced')
            for k in range(i, j):
                self._score_access(k)
            n_bursts += 1
            i = j
            if n_bursts % 200 == 0:
                self.log.info(f'replay {i}/{N} ({n_bursts} bursts, '
                              f'cycle {self.cyc})')

        # -- end-of-run cross-checks ------------------------------------
        self._score('accepts == accesses', len(self.accept_log), N)
        self._score('no merges in the replay', self.merge_count, 0)
        self._check_totals_vs_golden()

        await self._quiesce()

        report = self.get_test_report()
        report['policy'] = self.POLICY
        report['n_accesses'] = self.N
        report['totals'] = dict(self.totals)
        report['golden_totals'] = {k: self.expected['totals'][k]
                                   for k in COUNT_KEYS}
        if self.out_path:
            with open(self.out_path, 'w', encoding='utf-8') as fh:
                json.dump(report, fh, indent=2, default=str)
        self.log.info(f'Parity report: {report}')
        return self.mismatches == 0
