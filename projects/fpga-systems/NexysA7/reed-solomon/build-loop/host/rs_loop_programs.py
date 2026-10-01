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
        gen_seed: int = 0, inj_seed=None, throttle: bool = False,
        throttle_a=None, throttle_b=None, timeout_s: float = 10.0) -> RunResult:
    """One run. `throttle` throttles BOTH checkers; throttle_a/throttle_b override
    one side each.

    The asymmetric case is the interesting one and it is why they are separate.
    Throttling both together keeps the two comparator FIFOs draining in
    lockstep, which masked a missing backpressure term for the whole bring-up:
    every test here passed while a skewed drain dropped beats on the board.
    """
    return drv.run(mode=mode, count=count, rate=rate, blocks=blocks, gen_seed=gen_seed,
                   inj_seed=inj_seed, timeout_s=timeout_s,
                   throttle_a=throttle if throttle_a is None else throttle_a,
                   throttle_b=throttle if throttle_b is None else throttle_b)


def verdict(r: RunResult, t: int) -> List[str]:
    """What is wrong with a run, as a list of complaints (empty = clean).

    The expectations depend on the regime:
      bypass, or count == 0          every block ok, no mismatching beat, CRCs match
      COUNT mode with 1 <= e <= t    every block corrected with e symbols, no mismatching
                                     beat, CRCs match
      COUNT mode with e > t          almost every block uncorrectable, and the checker
                                     DID see mismatches. NOT every block: see below.
      any regime                     an accepted block beyond the threshold is REPORTED,
                                     never itself a failure; bounding its rate needs far
                                     more blocks than one run has, so the soak does it
      any mode                       decoders A and B agree (comparator clean), both
                                     checkers received every block, no framing errors

    What the two checker outputs mean. `data_err` is the beat-by-beat compare
    of the received words against the regenerated pattern: that is the data
    evidence. The shared checker's CRC-32 is computed over its REGENERATED
    words (axis4_slave_pattern_check in word mode), so `crc_ok` proves only
    that the checker consumed the same number of words as the generator
    produced -- it is a delivery check, not a data check, and it stays true on
    an uncorrectable block by design.

    Why e > t does NOT mean every block is flagged uncorrectable. Beyond the
    threshold the received word can land within distance t of a DIFFERENT valid
    codeword, and a bounded-distance decoder then corrects it -- to the wrong
    message, reporting success. That is a property of the code, not a defect,
    and no post-correction check can catch it: the re-computed syndromes really
    are zero, because the result really is a codeword.

    This rule used to demand uncorrectable on every block. It held for the
    whole bring-up and then failed 5 runs of a 199-run soak, every time as
    exactly one block in 4096. The reference model does the same thing at the
    same rate: on RS(252,236) with e = 9 it accepts about 1 block in 20,000 and
    decodes it to the wrong message. Both hardware solvers agreeing on the
    wrong answer is the signature -- a solver bug would not reproduce in
    Python. So the accepted blocks are counted and the two solvers are still
    required to agree, while bounding the RATE is left to the soak.
    """
    bad = []
    if r.timed_out:
        bad.append("run did not finish")
    for d in r.present:
        if d.pkts != r.blocks:
            bad.append(f"{d.name}: {d.pkts} of {r.blocks} blocks reached its checker")
        if d.blk_frame:
            bad.append(f"{d.name}: {d.blk_frame} framing errors")
    # NOT in bypass: bypass deliberately routes the generator straight at the
    # checkers and skips the codec chain, so every AXI4 stage correctly stays
    # at zero. Demanding a completed chain there reports the harness working
    # as designed as a failure, which is what it did on the board.
    if r.iface == "AXI4" and not r.bypass:
        # Refusal first, and INSTEAD of the stage check: a refused run leaves
        # every stage at zero, so reporting both would lead with the symptom
        # and bury the cause.
        if r.axi4_overflow:
            bad.append("AXI4 run refused: GEN_BLOCKS exceeds what the memories hold, "
                       "so the regions would wrap. Run fewer blocks per kick.")
        elif r.axi4_stage != 0x1F:
            # Five sequential jobs, each done held until the next kick, so a
            # complete run reads 0x1F. Naming the stage that stopped beats the
            # timeout that would otherwise be the only symptom.
            stages = ["seed", "encode", "inject", "decode", "drain"]
            missing = [n for i, n in enumerate(stages) if not (r.axi4_stage >> i) & 1]
            bad.append(f"AXI4 chain stopped: stage(s) {', '.join(missing)} never "
                       f"completed (STATUS.axi4_stage = 0x{r.axi4_stage:02X})")
        if r.axi4_resp_err:
            bad.append("AXI4 chain saw a non-OKAY response on some stage")
    if not r.compare:
        pass                     # single-decoder build: nothing to compare
    elif r.cmp_misaligned:
        # the counts below would be noise: a dropped beat misaligns the streams
        bad.append("the comparator overflowed -- its mismatch counts are meaningless, "
                   "a beat was dropped and the two streams are misaligned")
    elif r.cmp_err or r.cmp_data_mismatch or r.cmp_status_mismatch:
        bad.append(f"riBM vs Euclid: {r.cmp_data_mismatch} beat and "
                   f"{r.cmp_status_mismatch} verdict mismatches")
    if r.bypass:
        for d in r.present:
            if d.data_err or not d.crc_ok:
                bad.append(f"{d.name} checker: data_err={d.data_err} crc_ok={d.crc_ok} in bypass")
        return bad
    exact = r.mode == RsLoopDriver.INJ_COUNT
    e = r.count if exact else None
    for d in r.present:
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
            # Every block must be ACCOUNTED FOR, and the accepted ones are
            # miscorrections (see the docstring). A real defect shows up as a
            # block that is neither flagged nor accepted, or as the two solvers
            # disagreeing -- not as the occasional accepted block.
            if d.blk_unc + d.blk_corr + d.blk_ok != r.blocks:
                bad.append(f"{d.name}: e={e} > t left blocks unaccounted for: "
                           f"unc={d.blk_unc} + corr={d.blk_corr} + ok={d.blk_ok} "
                           f"!= {r.blocks}")
            # A clean verdict is only reachable once the error pattern can BE a
            # codeword, which takes weight >= d = 2t + 1.
            if d.blk_ok and e < 2 * t + 1:
                bad.append(f"{d.name}: e={e} > t gave {d.blk_ok} CLEAN block(s); an error "
                           f"pattern cannot be a codeword below weight {2 * t + 1}")
            if not d.data_err:
                bad.append(f"{d.name}: e={e} > t yet the checker saw no mismatching beat -- "
                           f"the errors did not reach it")
        # BURST / RATE: only the agreement and delivery checks above apply
    if exact and r.inj_symbols != e * r.blocks:
        bad.append(f"injector placed {r.inj_symbols} symbols, expected {e * r.blocks}")
    return bad


def bandwidth(r) -> str:
    """One line of bandwidth, from the meters rather than inferred from cycles.

    On the stream path the two ends should differ by n/k, because the encoder
    emits a codeword for every k symbols it takes -- so the ratio is a cheap
    check that the meters are measuring what their names claim.
    """
    if not r.obs:
        return "no meters in this bitstream"
    i, o = r.obs["in"], r.obs["out"]
    ratio = (o["productive"] / i["productive"]) if i["productive"] else 0.0
    return (f"in {i['productive']} beats / {i['window']} cyc = {i['utilisation']:.1%} "
            f"(bp {i['backpressure']}, starv {i['starvation']}); "
            f"out {o['productive']} / {o['window']} = {o['utilisation']:.1%} "
            f"(bp {o['backpressure']}, starv {o['starvation']}); "
            f"out/in beats = {ratio:.3f}")


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
