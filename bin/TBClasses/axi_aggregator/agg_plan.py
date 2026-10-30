# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: agg_plan
# Purpose: Stimulus plan for the AXI4 write/read aggregators: transaction
#          records, directed streams and the random op generator
#
# Author: sean galloway
# Created: 2026-10-28

"""Stimulus plan for ``axi4_wr_aggregator`` / ``axi4_rd_aggregator``.

A ``Txn`` is one upstream AXI4 command (plus its write data). The generators
here only decide WHAT is sent and in what order; the expected downstream
stream is derived by the checker from the commands the upstream monitor
actually saw, never from this plan's intent. The one thing the plan does
declare is ``expect_agg`` for the directed streams, where the pairing outcome
is a property of the stream itself.
"""

from dataclasses import dataclass, field
from typing import List, Optional

INCR, FIXED, WRAP = 1, 0, 2
# Qualifier value sets: small so that pairs usually share them
# AxCACHE[1] (modifiable) must be set for a command to pair; 0 and 1 never pair
CACHES = (2, 3, 15, 2, 3, 15, 0, 1)
PROTS = (0, 1, 2)
QOSS = (0, 5)
REGIONS = (0, 1)
USERS = (0, 1)
QUAL_FIELDS = ('cache', 'prot', 'qos', 'region', 'user')


@dataclass
class Txn:
    """One upstream command."""
    addr: int
    id: int = 0
    length: int = 0            # AxLEN (beats - 1)
    size: int = 0              # AxSIZE, filled in by the allocator when -1
    burst: int = INCR
    lock: int = 0
    cache: int = 2
    prot: int = 0
    qos: int = 0
    region: int = 0
    user: int = 0
    data: List[int] = field(default_factory=list)   # writes: one word per beat
    strb: Optional[int] = None                       # writes: explicit WSTRB (None = BFM default)
    oor: bool = False          # writes: addressed beyond the slave memory (SLVERR expected)
    label: str = ''
    # filled in by the run
    result: object = None
    error: str = ''

    def quals(self):
        return {k: getattr(self, k) for k in QUAL_FIELDS}


class Planner:
    """Address allocator + stream builders for one data width."""

    def __init__(self, data_width, mem_bytes, rng):
        self.dw = data_width
        self.B = data_width // 8
        self.full = self.B.bit_length() - 1
        self.mem_bytes = mem_bytes
        self.rng = rng
        self.next_addr = 0
        self.next_oor = mem_bytes

    # ---- allocation ------------------------------------------------------
    def slot(self, align_beats=2, beats=2):
        """A fresh region of `beats` beats aligned to `align_beats` beats."""
        al = align_beats * self.B
        self.next_addr = (self.next_addr + al - 1) // al * al
        a = self.next_addr
        self.next_addr += max(beats, align_beats) * self.B
        if self.next_addr > self.mem_bytes:
            raise RuntimeError("planner ran out of memory: raise MEM_BYTES")
        return a

    def oor_slot(self):
        a = (self.next_oor + 2 * self.B - 1) // (2 * self.B) * (2 * self.B)
        self.next_oor = a + 2 * self.B
        return a

    def word(self):
        return self.rng.getrandbits(self.dw)

    def rand_quals(self):
        r = self.rng
        return dict(cache=r.choice(CACHES), prot=r.choice(PROTS), qos=r.choice(QOSS),
                    region=r.choice(REGIONS), user=r.choice(USERS))

    # ---- single transactions ---------------------------------------------
    def single(self, addr, id=0, quals=None, strb=None, wr=True, label='', **kw):
        t = Txn(addr=addr, id=id, size=self.full, label=label, strb=strb, **(quals or {}), **kw)
        if wr:
            t.data = [self.word()]
        return t

    def burst(self, id=0, beats=2, quals=None, wr=True, label='burst'):
        a = self.slot(align_beats=4, beats=4)
        t = Txn(addr=a, id=id, length=beats - 1, size=self.full, label=label, **(quals or {}))
        if wr:
            t.data = [self.word() for _ in range(beats)]
        return t

    def pair(self, id=0, quals=None, wr=True, strbs=(None, None), oor=False, label='pair'):
        a = self.oor_slot() if oor else self.slot()
        q = quals if quals is not None else self.rand_quals()
        lo = self.single(a, id, q, strbs[0], wr, label + '.lo', oor=oor)
        hi = self.single(a + self.B, id, q, strbs[1], wr, label + '.hi', oor=oor)
        return [lo, hi]

    def rand_strb(self):
        return self.rng.randrange(1, 1 << self.B)

    # ---- directed streams ------------------------------------------------
    def directed(self, wr):
        """[(name, [Txn...], expect_agg)] with expect_agg for HOLD > 0.

        The caller runs them with the upstream driven back-to-back, so a hi that
        follows its lo is on the bus within the hold window."""
        P = self
        B = self.B
        d = []

        # lo0 hi0 lo1 hi2 -> exactly one aggregation (lo0+hi0)
        a0, a1, a2 = P.slot(), P.slot(), P.slot()
        d.append(('lo0 hi0 lo1 hi2', [
            P.single(a0, 1, wr=wr, label='lo0'), P.single(a0 + B, 1, wr=wr, label='hi0'),
            P.single(a1, 1, wr=wr, label='lo1'), P.single(a2 + B, 1, wr=wr, label='hi2')], 1))
        # lo0 lo1 hi0 hi1 -> nothing adjacent pairs
        a0, a1 = P.slot(), P.slot()
        d.append(('lo0 lo1 hi0 hi1', [
            P.single(a0, 1, wr=wr, label='lo0'), P.single(a1, 1, wr=wr, label='lo1'),
            P.single(a0 + B, 1, wr=wr, label='hi0'), P.single(a1 + B, 1, wr=wr, label='hi1')], 0))
        # hi0 lo0
        a0 = P.slot()
        d.append(('hi0 lo0', [P.single(a0 + B, 1, wr=wr, label='hi0'),
                              P.single(a0, 1, wr=wr, label='lo0')], 0))
        # four in a row: two aggregations
        a0, a1 = P.slot(), P.slot()
        d.append(('lo0 hi0 lo1 hi1', [
            P.single(a0, 2, wr=wr, label='lo0'), P.single(a0 + B, 2, wr=wr, label='hi0'),
            P.single(a1, 2, wr=wr, label='lo1'), P.single(a1 + B, 2, wr=wr, label='hi1')], 2))
        # different ids
        a0 = P.slot()
        d.append(('id mismatch', [P.single(a0, 1, wr=wr, label='lo'),
                                  P.single(a0 + B, 2, wr=wr, label='hi')], 0))
        # each qualifier differing
        alt = dict(cache=7, prot=3, qos=9, region=2, user=1)
        for q in QUAL_FIELDS:
            a0 = P.slot()
            base = dict(cache=2, prot=0, qos=0, region=0, user=0)
            other = dict(base)
            other[q] = alt[q]
            d.append((f'{q} mismatch', [P.single(a0, 1, base, wr=wr, label='lo'),
                                        P.single(a0 + B, 1, other, wr=wr, label='hi')], 0))
        # non-modifiable (AxCACHE[1] = 0) commands never pair, even identical ones
        for cv, lab in ((0, 'cache=0 pair'), (1, 'cache=1 (bufferable only) pair')):
            a0 = P.slot()
            d.append((lab, [P.single(a0, 1, dict(cache=cv), wr=wr, label='lo'),
                            P.single(a0 + B, 1, dict(cache=cv), wr=wr, label='hi')], 0))
        a0 = P.slot()
        d.append(('modifiable lo, cache=0 hi', [P.single(a0, 1, dict(cache=2), wr=wr, label='lo'),
                                                P.single(a0 + B, 1, dict(cache=0), wr=wr, label='hi')], 0))
        a0 = P.slot()
        d.append(('cache=0 lo, modifiable hi', [P.single(a0, 1, dict(cache=0), wr=wr, label='lo'),
                                                P.single(a0 + B, 1, dict(cache=2), wr=wr, label='hi')], 0))
        # same non-zero qualifiers DO pair
        a0 = P.slot()
        d.append(('matching qualifiers', P.pair(1, alt, wr=wr), 1))
        # a burst never pairs, and never lets its neighbours pair across it
        d.append(('burst alone', [P.burst(1, 4, wr=wr)], 0))
        a0 = P.slot(beats=4)
        b = Txn(addr=a0 + B, id=1, length=1, size=self.full, label='burst at hi addr',
                data=[P.word(), P.word()] if wr else [])
        d.append(('lo burst', [P.single(a0, 1, wr=wr, label='lo'), b], 0))
        a0 = P.slot()
        d.append(('lo burst hi', [P.single(a0, 1, wr=wr, label='lo'), P.burst(1, 2, wr=wr),
                                  P.single(a0 + B, 1, wr=wr, label='hi')], 0))
        # not full width, not INCR, locked: never a lo, never a hi
        if self.full > 0:
            a0 = P.slot()
            narrow = lambda a, lab: Txn(addr=a, id=1, size=self.full - 1, label=lab,
                                        data=[P.word() & ((1 << (B * 4)) - 1)] if wr else [])
            d.append(('narrow pair', [narrow(a0, 'lo'), narrow(a0 + B // 2, 'hi')], 0))
        a0 = P.slot()
        fx = lambda a, lab: Txn(addr=a, id=1, size=self.full, burst=FIXED, label=lab,
                                data=[P.word()] if wr else [])
        d.append(('fixed pair', [fx(a0, 'lo'), fx(a0 + B, 'hi')], 0))
        a0 = P.slot()
        lk = lambda a, lab: Txn(addr=a, id=1, size=self.full, lock=1, label=lab,
                                data=[P.word()] if wr else [])
        d.append(('locked pair', [lk(a0, 'lo'), lk(a0 + B, 'hi')], 0))
        # misaligned: lo/hi addresses that straddle two 2-beat windows
        a0 = P.slot(beats=4)
        d.append(('misaligned pair', [P.single(a0 + B, 1, wr=wr, label='x'),
                                      P.single(a0 + 2 * B, 1, wr=wr, label='y')], 0))
        if wr:
            d.append(('oor pair', P.pair(1, {}, wr=True, oor=True, label='oor'), 1))
        return d

    def lone_cases(self, wr):
        """Single lone lo, run alone on an idle bus: hold-expiry latency."""
        return [('lone lo', [self.single(self.slot(), 3, wr=wr, label='lone')], 0),
                ('lone lo 2', [self.single(self.slot(), 0, dict(cache=3, prot=1), wr=wr, label='lone')], 0)]

    # ---- random ops ------------------------------------------------------
    def random_op(self, wr, ids, allow_oor=True):
        r = self.rng
        k = r.random()
        id_ = r.choice(ids)
        B = self.B
        strbs = (self.rand_strb() if (wr and r.random() < 0.3) else None,
                 self.rand_strb() if (wr and r.random() < 0.3) else None)
        if k < 0.34:
            return self.pair(id_, None, wr, strbs)
        if k < 0.42:
            return [self.single(self.slot(), id_, self.rand_quals(), wr=wr, label='lone lo')]
        if k < 0.48:
            a = self.slot()
            return [self.single(a + B, id_, self.rand_quals(), wr=wr, label='lone hi')]
        if k < 0.58:
            return [self.burst(id_, r.randint(2, 4), self.rand_quals(), wr)]
        if k < 0.65:
            a = self.slot()
            q = self.rand_quals()
            return [self.single(a + B, id_, q, wr=wr, label='hi'), self.single(a, id_, q, wr=wr, label='lo')]
        if k < 0.74:
            a0, a1 = self.slot(), self.slot()
            q = self.rand_quals()
            return [self.single(a0, id_, q, wr=wr, label='lo0'), self.single(a1, id_, q, wr=wr, label='lo1'),
                    self.single(a0 + B, id_, q, wr=wr, label='hi0'), self.single(a1 + B, id_, q, wr=wr, label='hi1')]
        if k < 0.84:
            lo, hi = self.pair(id_, None, wr, strbs)
            if r.random() < 0.5:
                hi.id = (hi.id + 1 + r.randrange(len(ids) - 1 or 1)) % (max(ids) + 1)
                if hi.id == lo.id:
                    hi.id = (lo.id + 1) % (max(ids) + 1)
            else:
                q = r.choice(QUAL_FIELDS)
                setattr(hi, q, getattr(hi, q) ^ 1)
            return [lo, hi]
        if k < 0.88 and self.full > 0:
            a = self.slot()
            nr = lambda addr: Txn(addr=addr, id=id_, size=self.full - 1, label='narrow',
                                  data=[self.word() & ((1 << (B * 4)) - 1)] if wr else [])
            return [nr(a), nr(a + B // 2)]
        if k < 0.92:
            a = self.slot()
            lk = lambda addr: Txn(addr=addr, id=id_, size=self.full, lock=1, label='lock',
                                  data=[self.word()] if wr else [])
            return [lk(a), lk(a + B)]
        if k < 0.95 and wr and allow_oor:
            return self.pair(id_, None, True, oor=True, label='oor')
        return self.pair(id_, None, wr, strbs)

    def random_groups(self, wr, n_txns, ids, group_max=6):
        """Groups of concurrently launched transactions (launch order = list order)."""
        groups, cur, made = [], [], 0
        while made < n_txns:
            op = self.random_op(wr, ids)
            if cur and len(cur) + len(op) > group_max:
                groups.append(cur)
                cur = []
            cur += op
            made += len(op)
        if cur:
            groups.append(cur)
        return groups
