"""Replacement-policy parity models for the jet DV grid (Task 12)

The jet grid sweeps REPL_POLICY across {LRU, FIFO, RANDOM}; the
event-stream scoreboards pin the victim way at EVERY MSHR alloc against
the policy model (update-at-alloc: jet claims the victim way and updates
the policy in the alloc cycle; hits touch the policy only under LRU --
l1_repl's FIFO/RANDOM branches ignore repl_hit by construction, and the
TB models mirror that).

  LRU    -- amber's rank model (hit + alloc update), the model.js list
            semantics up to a consistent way renaming (the amber parity
            argument, amber_parity_tb.py).
  FIFO   -- amber's ring model (alloc update only).
  RANDOM -- per-set 32-bit Fibonacci LFSR (taps 32,22,2,1; REPL_SEED),
            the cache_sim recorded-LFSR extension's semantics
            (dv/golden/cache_sim_lfsr_extension.js): the victim is the
            truncated state SAMPLED at the alloc and the draw advances AT
            the alloc (jet's repl_req == w_accept_alloc -- one draw per
            alloc; a claim-stall retry does NOT redraw, since the LFSR
            only shifts on repl_req).

Author: RTL Design Sherpa
Created: 2026-10-29
"""

from projects.components.cache_ip.common_ip.dv.tbclasses.l1_core_tb import (
    LruModel,
    FifoModel,
)
from projects.components.cache_ip.common_ip.dv.golden.cache_sim_harness import (
    LfsrRng,
    REPL_SEED,
)

# amber_repl_t encodings (l1_pkg)
REPL_LRU, REPL_TREE_PLRU, REPL_FIFO, REPL_RANDOM = 0, 1, 2, 3
REPL_NAMES = {REPL_LRU: 'lru', REPL_TREE_PLRU: 'tplru',
              REPL_FIFO: 'fifo', REPL_RANDOM: 'rand'}


class RandReplModel:
    """Per-set LFSR parity model for l1_repl RANDOM.  victim() peeks the
    truncated state (no advance); update() is the alloc's draw."""

    def __init__(self, sets, ways, seed=REPL_SEED):
        self.sets, self.ways = sets, ways
        self.lfsr = [LfsrRng(seed) for _ in range(sets)]

    def victim(self, s):
        return self.lfsr[s].state & (self.ways - 1)

    def update(self, s, way):
        self.lfsr[s].next_int(self.ways)


def make_repl_model(policy, sets, ways):
    """The victim-way parity model for a REPL_POLICY encoding."""
    if policy == REPL_LRU:
        return LruModel(sets, ways)
    if policy == REPL_FIFO:
        return FifoModel(sets, ways)
    if policy == REPL_RANDOM:
        return RandReplModel(sets, ways)
    raise ValueError(f'no jet parity model for REPL_POLICY={policy} '
                     '(tree-PLRU is covered by the RTL self-check)')
