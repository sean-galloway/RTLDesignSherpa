"""
amber_repl testbench

Replacement-policy engine: true LRU (default), FIFO, RANDOM (LFSR), and
tree-PLRU. Direct pin-level stimulus -- the DUT has no bus interface, so no
BFM applies (the amba_random_configs / quick_config delay profiles are for
gaxi/AMBA-facing blocks; this TB randomizes traffic directly).

Golden models live here, one small Python class per policy, mirroring the
MAS ch02_blocks/04 contract:
  LRU      rank array, 0 = most recent; victim has rank WAYS-1
  FIFO     per-set ring of way indices; victim = head, install writes the
           victim slot and advances (install way == victim way, the
           amber_control guarantee -- MAS invariant)
  RANDOM   32-bit Fibonacci LFSR, taps (32,22,2,1), sample-then-advance on
           every repl_req
  TREE_PLRU binary tree of WAYS-1 bits per set, heap-indexed nodes, bits
           point away from the accessed way

Every cycle drives at most one of repl_hit / repl_update (mutually
exclusive per MAS). Install operations use the victim way just sampled --
that is what amber_control does on a fill.

Author: RTL Design Sherpa
Created: 2026-10-06
"""

import os
import random

from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


class LruModel:
    """Rank array: 0 = MRU, WAYS-1 = victim. Updates on hits and installs."""

    UPDATES_ON_HIT = True

    def __init__(self, sets, ways):
        self.sets, self.ways = sets, ways
        self.rank = [[w for w in range(ways)] for _ in range(sets)]

    def victim(self, s):
        for w in range(self.ways):
            if self.rank[s][w] == self.ways - 1:
                return w
        raise RuntimeError("LRU model: no victim")

    def update(self, s, way):
        old = self.rank[s][way]
        for w in range(self.ways):
            if w == way:
                self.rank[s][w] = 0
            elif self.rank[s][w] < old:
                self.rank[s][w] += 1


class FifoModel:
    """Ring of way indices; install writes the victim slot, head advances.
    Hits do not reorder a FIFO (MAS ch02_blocks/04) -- model ignores them."""

    UPDATES_ON_HIT = False

    def __init__(self, sets, ways):
        self.sets, self.ways = sets, ways
        self.q = [[w for w in range(ways)] for _ in range(sets)]
        self.head = [0] * sets

    def victim(self, s):
        return self.q[s][self.head[s]]

    def update(self, s, way):
        self.q[s][self.head[s]] = way
        self.head[s] = (self.head[s] + 1) % self.ways


class RandomModel:
    """32-bit Fibonacci LFSR, taps (32,22,2,1); victim = lfsr[WAY_WIDTH-1:0].
    State moves on repl_request only (advanced explicitly by the TB)."""

    UPDATES_ON_HIT = False

    def __init__(self, sets, ways, seed):
        self.sets, self.ways = sets, ways
        self.mask = ways - 1
        self.lfsr = [seed & 0xFFFFFFFF] * sets

    def victim(self, s):
        return self.lfsr[s] & self.mask

    def advance(self, s):
        l = self.lfsr[s]
        fb = ((l >> 31) ^ (l >> 21) ^ (l >> 1) ^ l) & 1
        self.lfsr[s] = ((l << 1) | fb) & 0xFFFFFFFF

    def update(self, s, way):
        pass  # policy state moves on repl_request only


class TreePlruModel:
    """Binary tree, WAYS-1 bits per set, heap-indexed; bits point away.
    Updates on hits and installs."""

    UPDATES_ON_HIT = True

    def __init__(self, sets, ways):
        import math
        self.sets, self.ways = sets, ways
        self.levels = int(math.log2(ways))
        self.tree = [[0] * (ways - 1) for _ in range(sets)]

    def victim(self, s):
        node = 0
        way = 0
        for _ in range(self.levels):
            b = self.tree[s][node]
            way = (way << 1) | b
            node = 2 * node + 1 + b
        return way

    def update(self, s, way):
        node = 0
        for lvl in range(self.levels):
            bit = (way >> (self.levels - 1 - lvl)) & 1
            self.tree[s][node] = 1 - bit
            node = 2 * node + 1 + bit


class AmberReplTB(TBBase):
    """Drives amber_repl and scores the victim way against a policy model."""

    OP_COUNTS = {'gate': 200, 'func': 2000, 'full': 20000}
    MODELS = {'lru': LruModel, 'fifo': FifoModel,
              'random': RandomModel, 'tree_plru': TreePlruModel}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.OP_COUNTS:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        random.seed(self.SEED)
        self.SETS = self.convert_to_int(os.environ.get('SETS', '128'))
        self.WAYS = self.convert_to_int(os.environ.get('WAYS', '4'))
        self.POLICY = os.environ.get('POLICY', 'lru')
        repl_seed = self.convert_to_int(os.environ.get('REPL_SEED', str(0x0000ACE1)))
        model_cls = self.MODELS[self.POLICY]
        self.model = (RandomModel(self.SETS, self.WAYS, repl_seed)
                      if self.POLICY == 'random'
                      else model_cls(self.SETS, self.WAYS))
        self.checks = 0
        self.mismatches = 0
        self.log.info(f"AmberReplTB sets={self.SETS} ways={self.WAYS} "
                      f"policy={self.POLICY} level={self.TEST_LEVEL} seed={self.SEED}")

    # -- the three mandatory methods -----------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self.dut.repl_req.value = 0
        self.dut.repl_hit.value = 0
        self.dut.repl_update.value = 0
        self.dut.repl_set.value = 0
        self.dut.repl_hit_way.value = 0
        await self.assert_reset()
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        await self.wait_clocks('clk', 1)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # -- scoring --------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {got} expected {exp}")

    # -- one policy access: request victim, then hit-or-install update --------
    async def _op(self, set_idx, do_hit, op_idx):
        # Drive the request and the (mutually exclusive) update event.
        self.dut.repl_set.value = set_idx
        self.dut.repl_req.value = 1
        self.dut.repl_hit.value = 1 if do_hit else 0
        self.dut.repl_update.value = 0 if do_hit else 1
        await Timer(1, units='ns')
        victim = int(self.dut.repl_victim_way.value)
        exp = self.model.victim(set_idx)
        self._score(f"op{op_idx} victim(set={set_idx})", victim, exp)
        if self.POLICY == 'random':
            self.model.advance(set_idx)
        if do_hit:
            way = random.randrange(self.WAYS)
        else:
            way = victim   # fills install into the victim way (MAS invariant)
        self.dut.repl_hit_way.value = way
        await RisingEdge(self.dut.clk)
        self.dut.repl_req.value = 0
        self.dut.repl_hit.value = 0
        self.dut.repl_update.value = 0
        if self.model.UPDATES_ON_HIT or not do_hit:
            self.model.update(set_idx, way)
        self.log.debug(f"op{op_idx}: set={set_idx} "
                       f"{'hit' if do_hit else 'install'} way={way}")

    async def _idle(self):
        self.dut.repl_req.value = 0
        self.dut.repl_hit.value = 0
        self.dut.repl_update.value = 0
        await RisingEdge(self.dut.clk)

    # -- tests ------------------------------------------------------------------
    async def run(self) -> bool:
        # Post-reset: the initial victim of every set must match the reset
        # state (LRU -> way WAYS-1, FIFO -> way 0, RANDOM -> seed truncated,
        # TREE_PLRU -> way 0).
        for set_idx in random.sample(range(self.SETS), min(self.SETS, 8)):
            self.dut.repl_set.value = set_idx
            self.dut.repl_req.value = 1
            await Timer(1, units='ns')
            self._score(f"reset victim(set={set_idx})",
                        int(self.dut.repl_victim_way.value),
                        self.model.victim(set_idx))
            if self.POLICY == 'random':
                self.model.advance(set_idx)
            await RisingEdge(self.dut.clk)
            self.dut.repl_req.value = 0

        n_ops = self.OP_COUNTS[self.TEST_LEVEL]
        self.log.info(f"amber_repl: {n_ops} policy ops at {self.TEST_LEVEL}")
        for i in range(n_ops):
            if random.random() < 0.2:
                await self._idle()
            else:
                await self._op(random.randrange(self.SETS),
                               do_hit=(random.random() < 0.5), op_idx=i)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
