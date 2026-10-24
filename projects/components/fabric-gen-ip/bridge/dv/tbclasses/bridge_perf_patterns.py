# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Traffic patterns against offered load (bridge TASK-014).

Uniform random traffic is the most benign pattern a fabric can see (Dally &
Towles ch. 3): every slave takes an equal share and no allocation conflict
lasts. The two that expose arbitration and buffering are
  permutation  every master streams at a DIFFERENT slave at once -- the
               fabric must carry N flows in parallel, so a shared stage or a
               serialising arbiter shows as a ceiling under N beats per cycle;
  hot-spot     every master streams at the SAME slave -- one port's peak is
               the ceiling, and the queue in front of it is where latency
               grows and fairness is decided.
The standard evaluation (Duato ch. 9) is accepted traffic and latency
against APPLIED load, up to and past saturation, not a single-point floor.

The driver is open loop, as test_bridge_2x2_rw_load: every `gap` cycles each
master starts one burst at the slave the pattern names, whether or not the
last one finished. Offered load per master is beats/gap in that master's
beats; it is converted to SLAVE beats (a 64-bit master's beat is two of a
32-bit slave's) so the figures compare at the port that limits. Accepted is
the slave port's R handshakes per cycle over the phase window. Latency is
call to last beat at the requester, so it includes queueing in the
requester once the port's outstanding limit is reached -- that is what a
real master sees. Every read is checked against the slave model.
"""
from __future__ import annotations

import statistics
from dataclasses import dataclass
from typing import Callable, Dict, List, Sequence, Tuple

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from bridge_perf_probe import Sampler

BEATS = 4                       # beats per read, as the load test

PATTERNS = ('uniform', 'permutation', 'hotspot')


@dataclass(frozen=True)
class Roles:
    """Which masters take part and which slaves each may reach (indices into
    the generated TB's master_rd / slave_info), plus the hot slave."""
    masters: Tuple[int, ...]
    reach: Dict[int, Tuple[int, ...]]      # master -> connected slaves, in TOML order
    hot: int

    def targets(self, pattern: str) -> Dict[int, Tuple[int, ...]]:
        """master -> the slaves its bursts cycle through under `pattern`."""
        if pattern == 'hotspot':
            return {m: (self.hot,) for m in self.masters if self.hot in self.reach[m]}
        if pattern == 'permutation':
            # distinct slaves, one per master, each from the master's reach
            taken, out = set(), {}
            for m in self.masters:
                pick = next((s for s in self.reach[m] if s not in taken), None)
                if pick is None:
                    raise ValueError(f"no distinct slave left for master {m}")
                taken.add(pick)
                out[m] = (pick,)
            return out
        return {m: tuple(self.reach[m]) for m in self.masters}


class Cycle:
    def __init__(self, tb):
        self.tb, self.now = tb, 0

    async def run(self):
        while True:
            await RisingEdge(self.tb.clock)
            self.now += 1


def slave_beats(tb, m: int, s: int, beats: int) -> int:
    """A master burst of `beats` beats, in the slave's beats (ceil)."""
    mw, sw = tb.master_data_width[m], tb.slave_info[s][3]
    return max(1, -(-beats * mw // sw))


def _addr(tb, m: int, s: int, k: int, beats: int) -> int:
    """Burst k of master m at slave s: each master owns an eighth of the
    slave's seeded model, bursts rotate inside it."""
    _, base, _rng, _sw = tb.slave_info[s]
    cap = getattr(tb, 'SLAVE_MEM_CAP_BYTES', 64 * 1024)
    slot = cap // 8
    bpb = tb.master_data_width[m] // 8
    span = beats * bpb
    n = max(1, slot // span)
    return base + m * slot + (k % n) * span


async def open_loop(tb, clk: Cycle, targets: Dict[int, Tuple[int, ...]], gap: int, n: int,
                    beats: int = BEATS) -> Tuple[Dict[int, List[int]], List[str]]:
    """Each master issues n reads, one every `gap` cycles, at its targets in
    turn. Returns per-master latencies and any data errors."""
    lats: Dict[int, List[int]] = {m: [] for m in targets}
    errors: List[str] = []
    futs = []

    async def one(m, s, k):
        addr = _addr(tb, m, s, k, beats)
        bpb = tb.master_data_width[m] // 8
        want = [tb.slave_mem_read(s, addr + b * bpb, byte_count=bpb) for b in range(beats)]
        t0 = clk.now
        got = await tb.master_rd[m].read_transaction(addr, burst_len=beats, id=k % 16,
                                                     size=(bpb.bit_length() - 1))
        lats[m].append(clk.now - t0)
        got = [g['data'] if isinstance(g, dict) else g for g in got]
        if list(got) != want:
            errors.append(f"m{m}->s{s} read {k} @0x{addr:08X}: data mismatch")

    for k in range(n):
        for m, ts in targets.items():
            futs.append(cocotb.start_soon(one(m, ts[k % len(ts)], k)))
        await ClockCycles(tb.clock, gap)
    for _ in range(40000):
        if all(f.done() for f in futs):
            break
        await ClockCycles(tb.clock, 5)
    assert all(f.done() for f in futs), f"gap {gap}: {sum(1 for f in futs if not f.done())} reads never completed"
    for f in futs:
        f.result()
    return lats, errors


@dataclass
class Point:
    pattern: str
    gap: int
    offered: float          # slave beats per cycle, summed over the targeted slave ports
    capacity: float         # what the targeted ports can absorb of that: sum over slaves of
                            # min(offered at the slave, 1.0) -- a slave offered 1.6 can take 1.0,
                            # and a 64-bit master's 4-beat read is 8 beats at a 32-bit slave
    accepted: float         # slave R beats per cycle, summed, over the phase window
    mean_lat: Dict[int, float]
    p95_lat: Dict[int, int]
    offered_by_slave: Dict[int, float] = None
    ports: int = 0          # targeted slave ports


async def sweep(tb, roles: Roles, pattern: str, gaps: Sequence[int], n: int,
                slave_prefix: Callable[[int], str], beats: int = BEATS) -> List[Point]:
    """One open-loop point per gap; the slaves' R channels are sampled over
    the phase, and each point's accepted rate is the sum over the slaves the
    pattern targets."""
    clk = Cycle(tb)
    cocotb.start_soon(clk.run())
    targets = roles.targets(pattern)
    slaves = sorted({s for ts in targets.values() for s in ts})
    out = []
    for gap in gaps:
        smp = Sampler(tb, {f's{s}': (slave_prefix(s), 'r') for s in slaves}).start()
        lats, errors = await open_loop(tb, clk, targets, gap, n, beats)
        assert not errors, errors[:5]
        acc = 0.0
        total_beats = 0
        for s in slaves:
            b, _c, r = smp.window_rate(f's{s}')
            acc += r
            total_beats += b
        # offered: each master issues one burst per gap, cycling its targets,
        # so slave s sees (its share of m's bursts) * (m's burst in s's beats) / gap
        by_slave = {s: 0.0 for s in slaves}
        for m, ts in targets.items():
            for s in ts:
                by_slave[s] += slave_beats(tb, m, s, beats) / len(ts) / gap
        offered = sum(by_slave.values())
        capacity = sum(min(v, 1.0) for v in by_slave.values())
        out.append(Point(pattern, gap, offered, capacity, acc,
                         {m: statistics.fmean(l) for m, l in lats.items() if l},
                         {m: sorted(l)[int(0.95 * (len(l) - 1))] for m, l in lats.items() if l},
                         by_slave, len(slaves)))
        await ClockCycles(tb.clock, 50)
    return out


def table(points: Sequence[Point], masters: Sequence[int]) -> List[str]:
    hdr = "| pattern | gap | offered | capacity | accepted | " + " | ".join(
        f"m{m} mean / p95" for m in masters) + " |"
    # offered and capacity in slave beats per cycle, summed over the targeted
    # ports; capacity = sum of min(offered at the slave, 1.0)
    rows = [hdr, "|" + "---|" * (5 + len(masters))]
    for p in points:
        cells = [p.pattern, str(p.gap), f"{p.offered:.3f}", f"{p.capacity:.1f}", f"{p.accepted:.3f}"]
        cells += [f"{p.mean_lat.get(m, 0):.1f} / {p.p95_lat.get(m, 0)}" if m in p.mean_lat else "-"
                  for m in masters]
        rows.append("| " + " | ".join(cells) + " |")
    return rows
