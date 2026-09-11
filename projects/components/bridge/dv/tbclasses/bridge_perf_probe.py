# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Shared measurement helpers for the bridge's performance and arbitration
tests (BRIDGE-017): saturating BFM profiles, a one-coroutine handshake
sampler, and windowed rates.

Two rules these encode (handbook: measure-over-the-window, randomization):
random BFM timing measures the stimulus, so every channel is driven
back-to-back; and every figure is computed from the handshakes recorded
inside the phase's own window, never from a cumulative counter.
"""

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

BEATS = 16   # beats per burst in every streaming phase

BACK_TO_BACK_VALID = {'valid_delay': ([(0, 0)], [1])}
BACK_TO_BACK_READY = {'ready_delay': ([(0, 0)], [1])}


def hi(sig):
    """True when `sig` reads 1; False on 0 OR X (an exception in a sampler
    kills it silently and the test then reports on nothing)."""
    try:
        return int(sig.value) == 1
    except ValueError:
        return False


def saturate(tb):
    """Every AXI4 BFM channel back-to-back: masters present VALID at once,
    slaves answer READY at once and stream responses without gaps."""
    for bfm in tb.master_wr.values():
        bfm.aw_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.w_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.b_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
    for bfm in tb.master_rd.values():
        bfm.ar_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.r_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
    for bfm in tb.slave_wr.values():
        bfm.aw_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
        bfm.w_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
        bfm.b_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.response_delay_cycles = 0
    for bfm in tb.slave_rd.values():
        bfm.ar_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_READY))
        bfm.r_channel.set_randomizer(FlexRandomizer(BACK_TO_BACK_VALID))
        bfm.response_delay_cycles = 0


class Sampler:
    """One coroutine samples every handshake of interest once per cycle, AT
    the clock edge (the values the flops capture). Sampling in ReadOnly
    after the edge sees the post-edge state and misses one-cycle handshakes.

    Records, per named channel, the cycle number of each handshake, plus
    the cycles VALID was high without READY (the far side stalled) and the
    cycles VALID was low (the near side offered nothing) -- over a window
    those two say who owns a gap.
    """

    def __init__(self, tb, channels):
        self.tb = tb
        self.channels = {name: (getattr(tb.dut, f"{pfx}_{ch}valid"),
                                getattr(tb.dut, f"{pfx}_{ch}ready"))
                         for name, (pfx, ch) in channels.items()}
        self.marks = {name: [] for name in channels}
        self.stalled = {name: [] for name in channels}
        self.idle = {name: [] for name in channels}
        self.cycle = 0
        self.alive = False

    async def run(self):
        self.alive = True
        while True:
            await RisingEdge(self.tb.clock)
            self.cycle += 1
            for name, (v, r) in self.channels.items():
                hv, hr = hi(v), hi(r)
                if hv and hr:
                    self.marks[name].append(self.cycle)
                elif hv:
                    self.stalled[name].append(self.cycle)
                else:
                    self.idle[name].append(self.cycle)

    def start(self):
        cocotb.start_soon(self.run())
        return self

    def window_rate(self, name):
        """(beats, cycles, beats/cycle) from the first to the last handshake."""
        m = self.marks[name]
        if len(m) < 2:
            return len(m), 0, 0.0
        cycles = m[-1] - m[0] + 1
        return len(m), cycles, len(m) / cycles

    def count_in(self, name, lo, hi_):
        return sum(1 for c in self.marks[name] if lo <= c <= hi_)

    def gaps_in(self, name, lo, hi_):
        return (sum(1 for c in self.stalled[name] if lo <= c <= hi_),
                sum(1 for c in self.idle[name] if lo <= c <= hi_))

    def max_gap(self, name, lo, hi_):
        """Longest run of cycles inside the window with no handshake on the
        channel -- the worst wait a requester saw."""
        pts = [c for c in self.marks[name] if lo <= c <= hi_]
        if not pts:
            return hi_ - lo + 1
        gaps = [b - a for a, b in zip(pts, pts[1:])]
        return max(gaps) if gaps else 0


def write_plan(master, slave_base, n, tag, beats=BEATS):
    """n write bursts for `master` inside the slave's 64 KB seeded model:
    each master owns a 32 KB half."""
    return [(master, slave_base + 0x8000 * master + i * beats * 4,
             [(tag << 24) | (master << 16) | (i << 4) | k for k in range(beats)])
            for i in range(n)]


async def stream_writes(tb, plan, errors, qos=None, beats=BEATS):
    """Issue every burst of the plan concurrently (ids rotate) and wait.
    `qos` is a dict master -> AWQOS value, default 0."""
    done = []

    async def _one(m, addr, data, txn_id):
        kw = dict(id=txn_id, size=2)
        if qos and m in qos:
            kw['qos'] = qos[m]
        res = await tb.master_wr[m].write_transaction(addr, data, **kw)
        if isinstance(res, dict) and not res.get('success', True):
            errors.append(f"m{m} write @0x{addr:08X}: {res}")
        done.append(1)

    for i, (m, addr, data) in enumerate(plan):
        cocotb.start_soon(_one(m, addr, data, i % 16))
    for _ in range(40000):
        if len(done) == len(plan):
            return
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"only {len(done)}/{len(plan)} write bursts completed")


async def stream_reads(tb, plan, errors, beats=BEATS):
    done = []

    async def _one(m, addr, data, txn_id):
        got = await tb.master_rd[m].read_transaction(addr, burst_len=beats, id=txn_id, size=2)
        if list(got) != data:
            errors.append(f"m{m} read @0x{addr:08X}: data mismatch")
        done.append(1)

    for i, (m, addr, data) in enumerate(plan):
        cocotb.start_soon(_one(m, addr, data, i % 16))
    for _ in range(40000):
        if len(done) == len(plan):
            return
        await ClockCycles(tb.clock, 5)
    raise AssertionError(f"only {len(done)}/{len(plan)} read bursts completed")


def report(tb, label, **kv):
    tb.log.info("PERF " + label + ": " + ", ".join(
        f"{k}={v:.3f}" if isinstance(v, float) else f"{k}={v}" for k, v in kv.items()))
