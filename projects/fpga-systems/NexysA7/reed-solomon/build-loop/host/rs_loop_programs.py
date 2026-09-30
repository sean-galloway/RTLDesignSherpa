# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The programs the host runs against the RS loop harness -- authored ONCE and
run unmodified in the cocotb sim (dv/tests/test_rs_loop_uart.py) and on the
board (host_rs_loop.py, bin/seq_*.py). Each returns a plain result object; the
callers decide how to print it.

  smoke(drv)              BUILD_ID, SCRATCH round-trip, PROFILE
  bypass(drv, blocks)     generator -> checkers with the codec out of the loop
  run(drv, ...)           one configured run; verdict(result) says whether it
                          matched expectations for that error count
  sweep(drv, counts, ...) one run per error count; a row per count
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, List

from rs_loop import RsLoopDriver, RunResult, EXPECTED_BUILD_ID


@dataclass
class SmokeResult:
    build_id: int
    scratch: list
    profile: dict

    @property
    def build_id_ok(self) -> bool:
        return self.build_id == EXPECTED_BUILD_ID

    @property
    def ok(self) -> bool:
        return self.build_id_ok and all(ok for _, _, ok in self.scratch)


def smoke(drv: RsLoopDriver) -> SmokeResult:
    return SmokeResult(build_id=drv.build_id(), scratch=drv.scratch_roundtrip(),
                       profile=drv.profile())


def bypass(drv: RsLoopDriver, blocks: int = 8, gen_seed: int = 0) -> RunResult:
    return drv.run(mode=RsLoopDriver.INJ_NONE, blocks=blocks, gen_seed=gen_seed, bypass=True)


def run(drv: RsLoopDriver, mode: int, count: int = 0, rate: int = 0, blocks: int = 8,
        gen_seed: int = 0, inj_seed=None, throttle: bool = False, timeout_s: float = 10.0) -> RunResult:
    return drv.run(mode=mode, count=count, rate=rate, blocks=blocks, gen_seed=gen_seed,
                   inj_seed=inj_seed, throttle_a=throttle, throttle_b=throttle, timeout_s=timeout_s)


def verdict(r: RunResult, t: int) -> List[str]:
    """What is wrong with a run, as a list of complaints (empty = clean).

    The expectations depend on the regime:
      bypass, or count == 0          every block ok, no mismatching beat, CRCs match
      COUNT mode with 1 <= e <= t    every block corrected with e symbols, no mismatching
                                     beat, CRCs match
      COUNT mode with e > t          every block uncorrectable (the injector guarantees
                                     exactly e errors) and the checker DID see mismatches
      any mode                       decoders A and B agree (comparator clean), both
                                     checkers received every block, no framing errors

    What the two checker outputs mean. `data_err` is the beat-by-beat compare
    of the received words against the regenerated pattern: that is the data
    evidence. The shared checker's CRC-32 is computed over its REGENERATED
    words (axis4_slave_pattern_check in word mode), so `crc_ok` proves only
    that the checker consumed the same number of words as the generator
    produced -- it is a delivery check, not a data check, and it stays true on
    an uncorrectable block by design.
    """
    bad = []
    if r.timed_out:
        bad.append("run did not finish")
    for d in (r.a, r.b):
        if d.pkts != r.blocks:
            bad.append(f"{d.name}: {d.pkts} of {r.blocks} blocks reached its checker")
        if d.blk_frame:
            bad.append(f"{d.name}: {d.blk_frame} framing errors")
    if r.cmp_err or r.cmp_data_mismatch or r.cmp_status_mismatch:
        bad.append(f"riBM vs Euclid: {r.cmp_data_mismatch} beat and "
                   f"{r.cmp_status_mismatch} verdict mismatches")
    if r.bypass:
        for d in (r.a, r.b):
            if d.data_err or not d.crc_ok:
                bad.append(f"{d.name} checker: data_err={d.data_err} crc_ok={d.crc_ok} in bypass")
        return bad
    exact = r.mode == RsLoopDriver.INJ_COUNT
    e = r.count if exact else None
    for d in (r.a, r.b):
        if e == 0 or r.mode == RsLoopDriver.INJ_NONE:
            if d.blk_ok != r.blocks or d.data_err or not d.crc_ok:
                bad.append(f"{d.name}: clean run gave ok={d.blk_ok}/{r.blocks} "
                           f"data_err={d.data_err} crc_ok={d.crc_ok}")
        elif exact and e <= t:
            if d.blk_corr != r.blocks or d.sym_corr != e * r.blocks or d.data_err or not d.crc_ok:
                bad.append(f"{d.name}: e={e} gave corrected={d.blk_corr}/{r.blocks} "
                           f"symbols={d.sym_corr} (want {e * r.blocks}) data_err={d.data_err} "
                           f"crc_ok={d.crc_ok}")
        elif exact and e > t:
            if d.blk_unc != r.blocks:
                bad.append(f"{d.name}: e={e} > t gave uncorrectable={d.blk_unc}/{r.blocks} "
                           f"(corrected={d.blk_corr}, ok={d.blk_ok})")
            if not d.data_err:
                bad.append(f"{d.name}: e={e} > t yet the checker saw no mismatching beat -- "
                           f"the errors did not reach it")
        # BURST / RATE: only the agreement and delivery checks above apply
    if exact and r.inj_symbols != e * r.blocks:
        bad.append(f"injector placed {r.inj_symbols} symbols, expected {e * r.blocks}")
    return bad


@dataclass
class SweepRow:
    count: int
    result: RunResult
    complaints: List[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.complaints


def sweep(drv: RsLoopDriver, counts: Iterable[int], blocks: int = 16, t: int = 8,
          gen_seed: int = 0, throttle: bool = False) -> List[SweepRow]:
    rows = []
    for e in counts:
        r = run(drv, RsLoopDriver.INJ_COUNT, count=e, blocks=blocks, gen_seed=gen_seed,
                throttle=throttle)
        rows.append(SweepRow(count=e, result=r, complaints=verdict(r, t)))
    return rows


def format_row(row: SweepRow) -> str:
    r = row.result
    return (f"e={row.count:>2}  cyc/blk={r.cycles_per_block:7.1f}  "
            f"riBM ok/corr/unc={r.a.blk_ok}/{r.a.blk_corr}/{r.a.blk_unc} sym={r.a.sym_corr} data={'x' if r.a.data_err else 'ok'}  "
            f"Euclid ok/corr/unc={r.b.blk_ok}/{r.b.blk_corr}/{r.b.blk_unc} sym={r.b.sym_corr} data={'x' if r.b.data_err else 'ok'}  "
            f"A=B:{'yes' if not r.cmp_err else 'NO'}  {'PASS' if row.ok else 'FAIL ' + '; '.join(row.complaints)}")
