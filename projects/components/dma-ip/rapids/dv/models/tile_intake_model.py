# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: tile_intake_model
# Purpose: Cycle model of RAPIDS's tile intake when delta interleaves and
#          reorders packets: the pencilled-in tagged, indexed intake
#          (rapids TASK-033), against today's arrival-order landing
#
# Documentation: projects/components/dma-ip/rapids/docs/rapids_mas/ch03_macro_blocks/14_tile_header.md
# Subsystem: rapids
# Author: sean galloway
# Created: 2026-10-19
"""RAPIDS tile intake under an interleaving, reordering fabric.

The mechanism under test (RAPIDS MAS, Tile Packet Header, Interleaved and
Out-of-Order Intake):

* Every flit carries a tag {sender, pos, head} beside its data. sender is the
  6-bit destination index of the source (nodes 0-21, cells 32-47, cores
  48-51); pos is the flit's place in the space the sender holds for that
  class; head marks a header flit.
* Class 0, cell data: pos is the cell's count of flits sent, header included,
  modulo TILE_LAND_FLITS. The landing space is a ring written at pos; the
  drain takes the packet at the read pointer once its header and every flit
  up to its last are present, and returns its flits as it drains.
* Class 1, descriptors (cores): a header plus one descriptor beat; pos is the
  core's packet count modulo TILE_DESC_PER_CORE, so each packet owns one
  intake entry. Entries leave in pos order.
* Class 2, MonBus (cells, cores, nodes): one header-only flit, the 64-bit
  MonBus word in header bits [97:34] (the length field and target[31:0]);
  pos is the sender's count modulo TILE_MON_PER_SENDER, and entries leave
  in pos order.

The fabric keeps the flits of one packet in order and nothing else: packets
get random latencies (so a later one overtakes), and the RAPIDS link carries
one flit per cycle chosen from any packet with a flit ready (so packets
interleave). Credit returns ride their own port with their own jitter.

Knobs for the controls and the mutations: ``landing='arrival'`` is today's
landing (one stream, packets framed in arrival order); ``drain='any'``
drains any complete packet rather than the one at the read pointer;
``pos_excl_header`` counts only payload flits into pos. ``send_rule`` is the
cell's rule: 'strap' (strap only), 'waitall' (strap whole before the next
packet) or 'oneflit' (one flit of the last packet back, the retired rule).
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

CLS_DATA, CLS_DESC, CLS_MON = 0, 1, 2

CELLS = list(range(32, 48))
CORES = list(range(48, 52))
NODES = list(range(0, 22))


@dataclass
class Flit:
    sender: int
    cls: int
    pos: int
    head: bool
    last: bool
    data: Tuple


@dataclass
class Packet:
    flits: List[Flit]
    ready_at: int
    sent_at: int


@dataclass
class Cfg:
    land: int = 16
    desc_per_core: int = 2
    mon_per_sender: int = 2
    cells: int = 16
    cores: int = 4
    nodes: int = 22
    data_flits: int = 600            # payload flits per cell
    descs: int = 12                  # per core
    mons: int = 8                    # per sender
    lat: Tuple[int, int] = (8, 40)   # fabric latency range, cycles
    crd_lat: Tuple[int, int] = (4, 20)
    drain_per_cycle: int = 1         # sink write path, flits per cycle
    send_rule: str = 'strap'
    landing: str = 'indexed'         # or 'arrival'
    drain: str = 'inorder'           # or 'any'
    pos_excl_header: bool = False
    max_cycles: int = 400_000
    seed: int = 1


class Sender:
    """One cell, core or node: straps per class, pos counters, the send rule."""

    def __init__(self, idx: int, cfg: Cfg, rng: random.Random):
        self.idx, self.cfg, self.rng = idx, cfg, rng
        self.free = {CLS_DATA: cfg.land, CLS_DESC: cfg.desc_per_core, CLS_MON: cfg.mon_per_sender}
        self.pos = {CLS_DATA: 0, CLS_DESC: 0, CLS_MON: 0}
        self.seq = {CLS_DATA: 0, CLS_DESC: 0, CLS_MON: 0}
        self.data_left = cfg.data_flits if idx in CELLS else 0
        self.desc_left = cfg.descs if idx in CORES else 0
        self.mon_left = cfg.mons
        self.sent_flits = 0
        self.next_beats = 0          # the waiting packet's size, drawn once
        self.returned = 0
        self.before_last = 0
        self.any_sent = False
        self.sent_log: Dict[int, List] = {CLS_DATA: [], CLS_DESC: [], CLS_MON: []}

    def done(self) -> bool:
        return not (self.data_left or self.desc_left or self.mon_left)

    def whole(self) -> bool:
        c = self.cfg
        return (self.free[CLS_DATA] == c.land and self.free[CLS_DESC] == c.desc_per_core
                and self.free[CLS_MON] == c.mon_per_sender)

    def _data_ok(self, flits: int) -> bool:
        if self.free[CLS_DATA] < flits:
            return False
        rule = self.cfg.send_rule
        if rule == 'waitall':
            return self.free[CLS_DATA] == self.cfg.land
        if rule == 'oneflit':
            return not self.any_sent or self.returned > self.before_last
        return True

    def try_send(self, now: int) -> Optional[Packet]:
        """At most one packet per cycle; MonBus first, then descriptors, then data."""
        c, rng = self.cfg, self.rng
        if self.mon_left and self.free[CLS_MON] and rng.random() < 0.05:
            word = (self.idx << 56) | self.seq[CLS_MON]
            f = Flit(self.idx, CLS_MON, self.pos[CLS_MON], True, True, ('mon', word))
            self._charge(CLS_MON, 1)
            self.sent_log[CLS_MON].append(word)
            self.mon_left -= 1
            return self._pkt([f], now)
        if self.desc_left and self.free[CLS_DESC] and rng.random() < 0.2:
            desc = (self.idx, self.seq[CLS_DESC])
            p = self.pos[CLS_DESC]
            fl = [Flit(self.idx, CLS_DESC, p, True, False, ('hdr', 1)),
                  Flit(self.idx, CLS_DESC, p, False, True, ('desc', desc))]
            self._charge(CLS_DESC, 1)
            self.sent_log[CLS_DESC].append(desc)
            self.desc_left -= 1
            return self._pkt(fl, now)
        if self.data_left:
            if not self.next_beats:
                self.next_beats = min(self.data_left, rng.randint(1, c.land - 1))
            beats = self.next_beats
            if not self._data_ok(beats + 1):
                return None
            self.next_beats = 0
            fl = []
            base = self.pos[CLS_DATA]
            for i in range(beats + 1):
                off = i if not c.pos_excl_header else max(i - 1, 0)
                pos = (base + off) % c.land
                if i == 0:
                    fl.append(Flit(self.idx, CLS_DATA, pos, True, False, ('hdr', beats)))
                else:
                    v = self.seq[CLS_DATA]
                    self.seq[CLS_DATA] += 1
                    self.sent_log[CLS_DATA].append(v)
                    fl.append(Flit(self.idx, CLS_DATA, pos, False, i == beats, ('beat', v)))
            adv = beats + 1 if not c.pos_excl_header else beats
            self.pos[CLS_DATA] = (base + adv) % c.land
            self.free[CLS_DATA] -= beats + 1
            self.before_last = self.sent_flits
            self.any_sent = True
            self.sent_flits += beats + 1
            self.data_left -= beats
            return self._pkt(fl, now)
        return None

    def _charge(self, cls: int, n: int):
        self.free[cls] -= n
        self.pos[cls] = (self.pos[cls] + 1) % (self.cfg.desc_per_core if cls == CLS_DESC
                                               else self.cfg.mon_per_sender)
        self.seq[cls] += 1

    def _pkt(self, flits: List[Flit], now: int) -> Packet:
        return Packet(flits, now + self.rng.randint(*self.cfg.lat), now)

    def credit(self, cls: int, n: int, errors: List[str]):
        self.free[cls] += n
        if cls == CLS_DATA:
            self.returned += n
        cap = {CLS_DATA: self.cfg.land, CLS_DESC: self.cfg.desc_per_core,
               CLS_MON: self.cfg.mon_per_sender}[cls]
        if self.free[cls] > cap:
            errors.append(f"sender {self.idx} class {cls}: over-return to {self.free[cls]}")


class Rapids:
    """The intake: indexed rings (or today's arrival-order landing)."""

    def __init__(self, cfg: Cfg):
        self.cfg = cfg
        self.ring: Dict[int, List[Optional[Flit]]] = {s: [None] * cfg.land for s in CELLS}
        self.rd: Dict[int, int] = {s: 0 for s in CELLS}
        self.desc_ent = {s: [None] * cfg.desc_per_core for s in CORES}
        self.desc_rd = {s: 0 for s in CORES}
        self.mon_ent = {s: [None] * cfg.mon_per_sender for s in CORES + CELLS + NODES}
        self.mon_rd = {s: 0 for s in self.mon_ent}
        self.arrival_q: Dict[int, List[Flit]] = {s: [] for s in CELLS}   # landing='arrival'
        self.got: Dict[int, Dict[int, List]] = {CLS_DATA: {}, CLS_DESC: {}, CLS_MON: {}}
        self.errors: List[str] = []
        self.returns: List[Tuple[int, int, int]] = []    # (sender, cls, n) this cycle
        self.early_returns: List[Tuple[int, int, int]] = []

    # ---- arrival -----------------------------------------------------------
    def land(self, f: Flit):
        if f.cls == CLS_DATA:
            if self.cfg.landing == 'arrival':
                # today's RTL: the header is stripped and its flit returned on arrival
                self.arrival_q[f.sender].append(f)
                if f.head:
                    self.early_returns.append((f.sender, CLS_DATA, 1))
                return
            slot = self.ring[f.sender]
            if slot[f.pos] is not None:
                self.errors.append(f"cell {f.sender}: ring slot {f.pos} overwritten")
            slot[f.pos] = f
        elif f.cls == CLS_DESC:
            ent = self.desc_ent[f.sender]
            cur = ent[f.pos] or {}
            key = 'hdr' if f.head else 'body'
            if key in cur:
                self.errors.append(f"core {f.sender}: entry {f.pos} {key} overwritten")
            cur[key] = f
            ent[f.pos] = cur
        else:
            ent = self.mon_ent[f.sender]
            if ent[f.pos] is not None:
                self.errors.append(f"sender {f.sender}: MonBus entry {f.pos} overwritten")
            ent[f.pos] = f

    # ---- drain -------------------------------------------------------------
    def _ring_packet_at(self, s: int, start: int) -> Optional[List[int]]:
        """Slot indices of the complete packet whose header is at start, or None."""
        ring, L = self.ring[s], self.cfg.land
        h = ring[start]
        if h is None or not h.head:
            return None
        n = h.data[1]
        idx = [(start + i) % L for i in range(n + 1)]
        if all(ring[i] is not None for i in idx):
            return idx
        return None

    def drain(self, rng: random.Random):
        self.returns, self.early_returns = self.early_returns, []
        budget = self.cfg.drain_per_cycle
        for s in rng.sample(CELLS, len(CELLS)):
            if budget <= 0:
                break
            if self.cfg.landing == 'arrival':
                q = self.arrival_q[s]
                if q and any(f.last for f in q):
                    k = next(i for i, f in enumerate(q) if f.last) + 1
                    pkt, self.arrival_q[s] = q[:k], q[k:]
                    self._deliver(s, pkt)
                    budget -= len(pkt)
                continue
            if self.cfg.drain == 'any':
                starts = [i for i in range(self.cfg.land) if self._ring_packet_at(s, i)]
                idx = self._ring_packet_at(s, starts[0]) if starts else None
            else:
                idx = self._ring_packet_at(s, self.rd[s])
            if idx:
                pkt = [self.ring[s][i] for i in idx]
                for i in idx:
                    self.ring[s][i] = None
                self.rd[s] = (idx[-1] + 1) % self.cfg.land
                self._deliver(s, pkt)
                budget -= len(pkt)
        for s, ent in self.desc_ent.items():
            e = ent[self.desc_rd[s]]
            if e and 'hdr' in e and 'body' in e and rng.random() < 0.3:
                self.got[CLS_DESC].setdefault(s, []).append(e['body'].data[1])
                ent[self.desc_rd[s]] = None
                self.desc_rd[s] = (self.desc_rd[s] + 1) % self.cfg.desc_per_core
                self.returns.append((s, CLS_DESC, 1))
        for s, ent in self.mon_ent.items():
            e = ent[self.mon_rd[s]]
            if e and rng.random() < 0.5:
                self.got[CLS_MON].setdefault(s, []).append(e.data[1])
                ent[self.mon_rd[s]] = None
                self.mon_rd[s] = (self.mon_rd[s] + 1) % self.cfg.mon_per_sender
                self.returns.append((s, CLS_MON, 1))

    def _deliver(self, s: int, pkt: List[Flit]):
        """A packet into its cell's sink channel (one channel per cell)."""
        if not pkt[0].head or not pkt[-1].last:
            self.errors.append(f"cell {s}: misframed packet delivered")
        self.got[CLS_DATA].setdefault(s, []).extend(f.data[1] for f in pkt if not f.head)
        early = 1 if self.cfg.landing == 'arrival' else 0
        self.returns.append((s, CLS_DATA, len(pkt) - early))

    def empty(self) -> bool:
        return (all(x is None for r in self.ring.values() for x in r)
                and all(not q for q in self.arrival_q.values())
                and all(x is None for e in self.desc_ent.values() for x in e)
                and all(x is None for e in self.mon_ent.values() for x in e))


def run(cfg: Cfg) -> Dict:
    """Run the model to completion; return errors and throughput."""
    rng = random.Random(cfg.seed)
    senders = {s: Sender(s, cfg, rng) for s in CELLS[:cfg.cells] + CORES[:cfg.cores] + NODES[:cfg.nodes]}
    rapids = Rapids(cfg)
    in_flight: List[Packet] = []
    credits: List[Tuple[int, int, int, int]] = []   # (due, sender, cls, n)
    first_data = last_data = None
    data_flits = 0
    now = 0
    while now < cfg.max_cycles:
        now += 1
        for s in senders.values():
            p = s.try_send(now)
            if p:
                in_flight.append(p)
        # RAPIDS's link: one flit per cycle from any packet with a flit ready
        ready = [p for p in in_flight if p.ready_at <= now]
        if ready:
            p = rng.choice(ready)
            f = p.flits.pop(0)
            rapids.land(f)
            if f.cls == CLS_DATA and not f.head:
                data_flits += 1
                first_data = first_data or now
                last_data = now
            if not p.flits:
                in_flight.remove(p)
        rapids.drain(rng)
        for s, cls, n in rapids.returns:
            credits.append((now + rng.randint(*cfg.crd_lat), s, cls, n))
        due = [c for c in credits if c[0] <= now]
        for c in due:
            credits.remove(c)
            senders[c[1]].credit(c[2], c[3], rapids.errors)
        if (all(s.done() for s in senders.values()) and not in_flight and not credits
                and rapids.empty()):
            break
    errors = list(rapids.errors)
    if now >= cfg.max_cycles:
        errors.append(f"did not finish in {cfg.max_cycles} cycles")
    for idx, s in senders.items():
        for cls, name in ((CLS_DATA, 'data'), (CLS_DESC, 'desc'), (CLS_MON, 'MonBus')):
            want, got = s.sent_log[cls], rapids.got[cls].get(idx, [])
            if want != got:
                bad = next((i for i, (a, b) in enumerate(zip(want, got)) if a != b), min(len(want), len(got)))
                errors.append(f"sender {idx} {name}: {len(got)}/{len(want)} delivered, first difference at {bad}")
        if not s.whole():
            errors.append(f"sender {idx}: straps not whole at the end {s.free}")
    span = (last_data - first_data + 1) if first_data else 1
    return {'errors': errors, 'cycles': now, 'data_flits': data_flits,
            'link_util': data_flits / span}   # payload flits per cycle on the link
