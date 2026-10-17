# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Bandwidth characterization of a generated bridge: traffic shapes that can
saturate the fabric, measured at its ports.

Built on bridge_perf_probe (saturating profiles, the per-cycle handshake
Sampler). What this adds:

* `pipelined` requester BFMs (RDS-DV): back-to-back transactions keep VALID
  high across bursts, so a gap measured at a port is the fabric's, not the
  stimulus's. Without it a 16-beat write stream measures ~0.89 beats/cycle
  of BFM re-arm.
* streams with a fixed number of transactions in flight, rotating IDs,
  full-width beats and any burst length, every read checked against the slave
  model and every write read back;
* slave latency, out-of-order completion and READY throttling;
* port prefixes read from the generated TB class, so one harness drives any
  fixture.
"""

from __future__ import annotations

import inspect
import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

import cocotb
from cocotb.triggers import ClockCycles

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from bridge_perf_probe import Sampler, saturate

_PREFIX = re.compile(r'prefix="([^"]+)"')


def port_prefixes(tb) -> Tuple[Dict[int, str], Dict[int, str]]:
    """{index: signal prefix} for masters and slaves, from the generated
    _setup_master_<i>_* / _setup_slave_<i>_* methods."""
    out: Tuple[Dict[int, str], Dict[int, str]] = ({}, {})
    for name, fn in inspect.getmembers(type(tb), inspect.isfunction):
        m = re.match(r'_setup_(master|slave)_(\d+)_', name)
        if not m:
            continue
        pfx = _PREFIX.search(inspect.getsource(fn))
        if pfx:
            out[0 if m.group(1) == 'master' else 1][int(m.group(2))] = pfx.group(1).rstrip('_')
    return out


def pipeline(tb) -> None:
    """Saturating profiles everywhere, and requesters that never drain
    between transactions."""
    saturate(tb)
    for bfm in list(tb.master_wr.values()) + list(tb.master_rd.values()):
        bfm.pipelined = True
        # A saturated narrow slave behind a wide master legitimately holds a
        # requester off for a long time: one 256-beat burst over an 8:1
        # downsize is 2048 slave beats, so AWREADY stays low ~2k cycles while
        # the converter's queue drains, and the last of eight Bs is ~16k
        # cycles out. Both timeouts default lower: the call's (5000) and each
        # channel driver's own READY wait (1000). The channel one fired first
        # and dropped the AW it was holding -- the call then waited forever
        # for a B to a write the bridge never saw, which looked exactly like
        # a bridge deadlock.
        bfm.timeout_cycles = max(getattr(bfm, 'timeout_cycles', 0), 200_000)
        for ch in ('aw_channel', 'w_channel', 'ar_channel'):
            drv = getattr(bfm, ch, None)
            if drv is not None:
                drv.timeout_cycles = max(getattr(drv, 'timeout_cycles', 0), 200_000)


def throttle_ready(bfm_channel, duty: float) -> None:
    """Hold READY low a fraction (1 - duty) of the time on one channel."""
    if duty >= 1.0:
        prof = {'ready_delay': ([(0, 0)], [1])}
    else:
        prof = {'ready_delay': ([(0, 0), (1, 1)], [duty, 1.0 - duty])}
    bfm_channel.set_randomizer(FlexRandomizer(prof))


def axsize(width_bits: int) -> int:
    return (width_bits // 8).bit_length() - 1


@dataclass
class Stream:
    """One requester stream: `n` bursts of `beats` from master `m` to slave
    `s`, `outstanding` in flight at once, IDs rotating over `ids`."""
    kind: str                       # 'rd' or 'wr'
    m: int
    s: int
    n: int
    beats: int
    outstanding: int = 8
    ids: Sequence[int] = (0,)
    region: int = 0                 # which slice of the slave's model to use
    errors: List[str] = field(default_factory=list)
    done: int = 0


class Characterizer:
    """Runs streams on a TB and measures the ports they cross."""

    def __init__(self, tb):
        self.tb = tb
        self.mpfx, self.spfx = port_prefixes(tb)
        self.cap = getattr(tb, 'SLAVE_MEM_CAP_BYTES', 64 * 1024)

    # -- addressing -------------------------------------------------------
    def _bytes_per_beat(self, st: Stream) -> int:
        return self.tb.master_data_width[st.m] // 8

    def _addr(self, st: Stream, k: int) -> int:
        """Burst k of the stream, inside the slave's modelled window. Each
        (region) gets its own quarter so concurrent streams never overlap."""
        bpb = self._bytes_per_beat(st)
        span = st.beats * bpb
        quarter = self.cap // 4
        slots = max(1, quarter // span)
        base = self.tb.slave_info[st.s][1]
        return base + st.region * quarter + (k % slots) * span

    def _wdata(self, st: Stream, k: int) -> List[int]:
        mask = (1 << self.tb.master_data_width[st.m]) - 1
        return [((0xC0DE0000 | (st.m << 12) | (k & 0xFFF)) * (b + 1) ^ (st.region << 20)) & mask
                for b in range(st.beats)]

    # -- traffic ------------------------------------------------------------
    async def _worker(self, st: Stream, mine: Sequence[int]) -> None:
        size = axsize(self.tb.master_data_width[st.m])
        for k in mine:
            txn_id = st.ids[k % len(st.ids)]
            addr = self._addr(st, k)
            if st.kind == 'wr':
                res = await self.tb.master_wr[st.m].write_transaction(
                    addr, self._wdata(st, k), id=txn_id, size=size)
                if isinstance(res, dict) and not res.get('success', True):
                    st.errors.append(f"m{st.m} write @0x{addr:08X}: {res}")
            else:
                want = [self.tb.slave_mem_read(st.s, addr + b * self._bytes_per_beat(st),
                                               byte_count=self._bytes_per_beat(st))
                        for b in range(st.beats)]
                got = await self.tb.master_rd[st.m].read_transaction(
                    addr, burst_len=st.beats, id=txn_id, size=size)
                if list(got) != want:
                    st.errors.append(f"m{st.m} read @0x{addr:08X}: data mismatch")
            st.done += 1

    async def run(self, streams: Sequence[Stream], timeout_cycles: int = 400_000) -> None:
        """Run every stream concurrently; return when all complete."""
        for st in streams:
            lanes = max(1, min(st.outstanding, st.n))
            for w in range(lanes):
                cocotb.start_soon(self._worker(st, range(w, st.n, lanes)))
        waited = 0
        while any(st.done < st.n for st in streams):
            await ClockCycles(self.tb.clock, 8)
            waited += 8
            if waited > timeout_cycles:
                raise AssertionError("streams stalled: " + ", ".join(
                    f"{st.kind} m{st.m}->s{st.s} {st.done}/{st.n}" for st in streams))
        for st in streams:
            assert not st.errors, st.errors[:5]
        for st in streams:
            if st.kind == 'wr':
                self._check_writes(st)

    def _check_writes(self, st: Stream) -> None:
        bpb = self._bytes_per_beat(st)
        quarter = self.cap // 4
        slots = max(1, quarter // (st.beats * bpb))
        for k in range(max(0, st.n - slots), st.n):   # the last write to each slot wins
            addr = self._addr(st, k)
            for b, d in enumerate(self._wdata(st, k)):
                got = self.tb.slave_mem_read(st.s, addr + b * bpb, byte_count=bpb)
                assert got == d, (f"write m{st.m}->s{st.s} burst {k} beat {b} @0x{addr + b * bpb:08X}: "
                                  f"memory 0x{got:X}, wrote 0x{d:X}")

    # -- measurement ----------------------------------------------------------
    def sampler(self, ports: Dict[str, Tuple[str, int, str]]) -> Sampler:
        """ports: name -> ('m'|'s', index, channel). Started immediately."""
        chans = {name: ((self.mpfx if side == 'm' else self.spfx)[idx], ch)
                 for name, (side, idx, ch) in ports.items()}
        s = Sampler(self.tb, chans)
        cocotb.start_soon(s.run())
        return s


def rate(s: Sampler, name: str) -> float:
    return s.window_rate(name)[2]


def overlap(s: Sampler, names: Sequence[str]) -> Optional[Tuple[int, int]]:
    """The window where every named channel is active (first-to-last)."""
    if not all(s.marks[n] for n in names):
        return None
    lo = max(s.marks[n][0] for n in names)
    hi = min(s.marks[n][-1] for n in names)
    return (lo, hi) if hi > lo else None


def rate_in(s: Sampler, name: str, win: Tuple[int, int]) -> float:
    lo, hi = win
    return s.count_in(name, lo, hi) / (hi - lo + 1)


class AcceptLimit:
    """A slave that takes at most `limit` requests at a time, like a memory
    controller with a `limit`-deep command queue: AR (AW) READY is held low
    while `limit` reads (writes) are accepted and not yet answered (last R /
    B handshake). The test BFMs otherwise accept without bound, which hides
    how much of a contended slave the fabric lets one requester occupy.

    Drives the BFM's runtime ready_policy, so the stall takes effect from the
    next cycle -- a registered full flag."""

    def __init__(self, ch: 'Characterizer', s: int, limit: int):
        from bridge_perf_probe import hi
        self._hi = hi
        tb, pfx = ch.tb, ch.spfx[s]
        self.tb, self.limit = tb, limit
        d = tb.dut
        self.sig = {n: getattr(d, f"{pfx}_{n}") for n in
                    ('arvalid', 'arready', 'rvalid', 'rready', 'rlast',
                     'awvalid', 'awready', 'bvalid', 'bready')}
        self.ar_ch = tb.slave_rd[s].ar_channel
        self.aw_ch = tb.slave_wr[s].aw_channel
        self.rd = self.wr = 0
        self.peak_rd = self.peak_wr = 0
        self.running = True
        cocotb.start_soon(self._run())

    async def _run(self):
        from cocotb.triggers import RisingEdge
        h, g = self._hi, self.sig
        while self.running:
            await RisingEdge(self.tb.clock)
            self.rd += h(g['arvalid']) and h(g['arready'])
            self.rd -= h(g['rvalid']) and h(g['rready']) and h(g['rlast'])
            self.wr += h(g['awvalid']) and h(g['awready'])
            self.wr -= h(g['bvalid']) and h(g['bready'])
            self.peak_rd, self.peak_wr = max(self.peak_rd, self.rd), max(self.peak_wr, self.wr)
            self.ar_ch.ready_policy = 'stall' if self.rd >= self.limit else 'valid_first'
            self.aw_ch.ready_policy = 'stall' if self.wr >= self.limit else 'valid_first'

    def stop(self):
        self.running = False
        self.ar_ch.ready_policy = self.aw_ch.ready_policy = 'valid_first'


class Floors:
    """Bandwidth floors: every measurement a case makes is checked against
    the floor its shape allows, and the case fails at the end listing every
    miss (not just the first, so one run shows the whole regression).

    `known` lists the weaknesses still open, each as (label regex, floor,
    note): a matching measurement is held to that lower floor instead, so it
    cannot get worse unnoticed, and the note says why it is there. When a
    weakness is fixed its row is deleted and the shape's real floor applies.
    """

    def __init__(self, tb, known: Sequence[Tuple[str, float, str]] = ()):
        self.tb = tb
        self.known = [(re.compile(rx), fl, note) for rx, fl, note in known]
        self.misses: List[str] = []
        self.checked = 0

    def need(self, label: str, value: float, floor: float) -> None:
        note = ''
        for rx, fl, why in self.known:
            if rx.search(label):
                floor, note = min(floor, fl), f' [known: {why}]'
                break
        self.checked += 1
        ok = value >= floor
        self.tb.log.info(f"FLOOR {'ok  ' if ok else 'MISS'} {label}: {value:.3f} >= {floor:.3f}{note}")
        if not ok:
            self.misses.append(f"{label}: {value:.3f} < {floor:.3f}{note}")

    def check(self) -> None:
        assert self.checked, "no floors were checked"
        assert not self.misses, (f"{len(self.misses)} of {self.checked} bandwidth floors missed:\n  "
                                 + "\n  ".join(self.misses))
