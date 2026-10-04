# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The programs the host runs against the BCH loop harness -- authored ONCE and
run unmodified in the cocotb sim (dv/tests/test_bch_loop_uart.py) and on the
board (host_bch_loop.py, bin/seq_*.py). Each returns a plain result object; the
callers decide how to print it.

  smoke(drv)              BUILD_ID, SCRATCH round-trip, PROFILE
  bypass(drv, blocks)     generator -> checker with the codec out of the loop
  run(drv, ...)           one configured run; verdict(result) says whether it
                          matched expectations for that error count
  sweep(drv, counts, ...) one run per error count; a row per count
"""
from __future__ import annotations

import binascii
from dataclasses import dataclass, field
from typing import Iterable, List

from bch_loop import BchLoopDriver, RunResult, CFG_N, CFG_K, CFG_T


@dataclass
class SmokeResult:
    build_id: int
    scratch: list
    profile: dict

    @property
    def build_id_ok(self) -> bool:
        from bch_loop import EXPECTED_BUILD_ID
        return self.build_id == EXPECTED_BUILD_ID

    @property
    def ok(self) -> bool:
        return self.build_id_ok and all(ok for _, _, ok in self.scratch)


def smoke(drv: BchLoopDriver) -> SmokeResult:
    return SmokeResult(build_id=drv.build_id(), scratch=drv.scratch_roundtrip(),
                       profile=drv.profile())


def bypass(drv: BchLoopDriver, blocks: int = 8, gen_seed: int = 0) -> RunResult:
    return drv.run(mode=BchLoopDriver.INJ_NONE, blocks=blocks, gen_seed=gen_seed, bypass=True)


def run(drv: BchLoopDriver, mode: int, count: int = 0, rate: int = 0, blocks: int = 8,
        gen_seed: int = 0, inj_seed=None, throttle: bool = False,
        throttle_a=None, throttle_b=None, timeout_s: float = 10.0,
        iface_obs: bool = False) -> RunResult:
    return drv.run(mode=mode, count=count, rate=rate, blocks=blocks, gen_seed=gen_seed,
                   inj_seed=inj_seed, timeout_s=timeout_s, iface_obs=iface_obs,
                   throttle_a=throttle if throttle_a is None else throttle_a,
                   throttle_b=throttle if throttle_b is None else throttle_b)


def _lfsr_step(value: int, taps: tuple = (23, 3, 2, 1)) -> int:
    """One Fibonacci LFSR step, matching shifter_lfsr with taps {23,3,2,1}."""
    bit = 0
    for t in taps:
        bit ^= (value >> t) & 1
    return ((value << 1) | bit) & 0xFFFFFFFF


def expected_byte_crc(gen_seed: int, blocks: int, k_bits: int = CFG_K,
                      data_width: int = 32, last_bytes: int = 3) -> int:
    """Byte-granular CRC-32 the checker computes for the generator's stream.

    The generator produces one 32-bit LFSR word per beat. Every beat except the
    last per block contributes all 4 bytes; the last contributes `last_bytes`
    bytes from lane 0. The checker runs in BYTE_CRC=1 mode, so this is the
    reference value for CRC_A.
    """
    k_beats = (k_bits + data_width - 1) // data_width
    lfsr = gen_seed & 0xFFFFFFFF
    crc_bytes = bytearray()
    for _ in range(blocks):
        for b in range(k_beats):
            word = lfsr.to_bytes(4, "little")
            if b == k_beats - 1:
                crc_bytes.extend(word[:last_bytes])
            else:
                crc_bytes.extend(word)
            lfsr = _lfsr_step(lfsr)
    return binascii.crc32(crc_bytes) & 0xFFFFFFFF


def verdict(r: RunResult, t: int = CFG_T) -> List[str]:
    """What is wrong with a run, as a list of complaints (empty = clean).

      bypass, or count == 0          every block ok, no mismatching beat, CRCs match
      COUNT mode with 1 <= e <= t    every block corrected with e bits, no mismatching
                                     beat, byte CRC matches expected
      COUNT mode with e > t          almost every block uncorrectable, and the checker
                                     DID see mismatches
      any mode                       the single decoder received every block, no framing errors
    """
    bad = []
    if r.timed_out:
        bad.append("run did not finish")
    for d in r.present:
        if d.pkts != r.blocks:
            bad.append(f"{d.name}: {d.pkts} of {r.blocks} blocks reached its checker")
        if d.blk_frame:
            bad.append(f"{d.name}: {d.blk_frame} framing errors")
    if r.iface == "AXI4" and not r.bypass:
        if r.axi4_overflow:
            bad.append("AXI4 run refused: GEN_BLOCKS exceeds what the memories hold, "
                       "so the regions would wrap. Run fewer blocks per kick.")
        elif (r.axi4_stage & AXI4_STAGE_MASK) != AXI4_STAGE_MASK:
            stages = {0: "seed", 1: "encode", 3: "decode", 4: "drain"}
            missing = [n for i, n in stages.items() if not (r.axi4_stage >> i) & 1]
            bad.append(f"AXI4 chain stopped: stage(s) {', '.join(missing)} never "
                       f"completed (STATUS.axi4_stage = 0x{r.axi4_stage:02X}, "
                       f"expected 0x{AXI4_STAGE_MASK:02X})")
        if r.axi4_resp_err:
            bad.append("AXI4 chain saw a non-OKAY response on some stage")
    if r.bypass:
        for d in r.present:
            if d.data_err:
                bad.append(f"{d.name} checker: data_err={d.data_err} in bypass")
        return bad
    exact = r.mode == BchLoopDriver.INJ_COUNT
    e = r.count if exact else None
    for d in r.present:
        if e == 0 or r.mode == BchLoopDriver.INJ_NONE:
            if d.blk_ok != r.blocks or d.data_err:
                bad.append(f"{d.name}: clean run gave ok={d.blk_ok}/{r.blocks} "
                           f"data_err={d.data_err}")
        elif exact and e <= t:
            if d.blk_corr != r.blocks or d.sym_corr != e * r.blocks or d.data_err:
                bad.append(f"{d.name}: e={e} gave corrected={d.blk_corr}/{r.blocks} "
                           f"bits={d.sym_corr} (want {e * r.blocks}) data_err={d.data_err}")
        elif exact and e > t:
            if d.blk_unc + d.blk_corr + d.blk_ok != r.blocks:
                bad.append(f"{d.name}: e={e} > t left blocks unaccounted for: "
                           f"unc={d.blk_unc} + corr={d.blk_corr} + ok={d.blk_ok} "
                           f"!= {r.blocks}")
            if d.blk_ok and e < CFG_N - CFG_K + 1:
                bad.append(f"{d.name}: e={e} > t gave {d.blk_ok} CLEAN block(s); an error "
                           f"pattern cannot be a codeword below weight {CFG_N - CFG_K + 1}")
            if not d.data_err:
                bad.append(f"{d.name}: e={e} > t yet the checker saw no mismatching beat -- "
                           f"the errors did not reach it")
        # BURST / RATE: only the agreement and delivery checks above apply
    if exact and r.inj_symbols != e * r.blocks:
        bad.append(f"injector placed {r.inj_symbols} bits, expected {e * r.blocks}")
    return bad


AXI4_STAGE_MASK = 0x1B


def iface_observers(drv: BchLoopDriver, blocks: int = 8, count: int = 0) -> RunResult:
    return run(drv, BchLoopDriver.INJ_COUNT, count=count, blocks=blocks, iface_obs=True)


def _beats(k_bits: int, n_bits: int, spb: int) -> tuple:
    k_beats = (k_bits + spb * 8 - 1) // (spb * 8)
    cw_beats = (n_bits + spb * 8 - 1) // (spb * 8)
    return k_beats, cw_beats


def format_iface_obs(r: RunResult, profile: dict, caps: dict) -> str:
    if not r.iface_obs:
        return "no interface observer data: run with iface_obs=True"
    spb = profile["spb"]
    k_beats, cw_beats = _beats(profile["k"], profile["n"], spb)
    lines = []
    for name, c in caps.items():
        stub = c["rd_ports"] == 0 and c["wr_ports"] == 0
        lines.append(f"  caps {name}: rd={c['rd_ports']} wr={c['wr_ports']} "
                     f"ch={c['channels']} bus_meter={int(c['bus_meter'])}"
                     + ("  (stub -- not this bitstream's datapath)" if stub else ""))
    if "axis" in r.iface_obs:
        obs = r.iface_obs["axis"]
        for port, beats_per_block in (("msg_in", k_beats), ("cw_out", cw_beats),
                                      ("cw_in", cw_beats), ("msg_out", k_beats)):
            d = obs.get(port)
            if not d:
                continue
            want = r.blocks * beats_per_block
            flag = "" if d["beats"] == want else f"  WANT {want}"
            lines.append(f"  {port:>7} {d['beats']:>8} beats / {d['window']:>8} cyc "
                         f"= {d['utilisation']:6.1%}  pkts {d['packets']:>5} "
                         f"bytes {d['bytes']:>8}  (bp {d['backpressure']}, "
                         f"starv {d['starvation']}, idle {d['idle']}){flag}")
    if "axi4" in r.iface_obs:
        obs = r.iface_obs["axi4"]
        for port, beats_per_block in (("enc_rd", k_beats), ("dec_rd", cw_beats),
                                      ("enc_wr", cw_beats), ("dec_wr", k_beats)):
            d = obs.get(port)
            if not d:
                continue
            want = r.blocks * beats_per_block
            flag = "" if d["productive"] == want else f"  WANT {want}"
            lines.append(f"  {port:>7} {d['productive']:>8} beats / {d['window']:>8} cyc "
                         f"= {d['utilisation']:6.1%}  timed {d['hist_total']:>5}  "
                         f"(bp {d['backpressure']}, starv {d['starvation']}, "
                         f"idle {d['idle']}){flag}")
    return "\n".join(lines)


def format_axi4_hist(hist: dict) -> str:
    lines = []
    for port, d in hist.items():
        is_write = 1 not in (d.get("hist") or {})
        for hm, bins in (d.get("hist") or {}).items():
            label = "AW->B" if is_write else ("AR->first-R", "AR->RLAST")[hm]
            total = d["hist_total"]
            binned = sum(bins)
            flag = "" if binned == total else f"  SUM {binned} != TOTAL {total}"
            nonzero = " ".join(f"{b}:{c}" for b, c in enumerate(bins) if c)
            lines.append(f"  {port:>7} {label:<11} [{nonzero}]{flag}")
    return "\n".join(lines)


def bandwidth(r: RunResult) -> str:
    if not r.obs:
        return "no meter data: either not read (meters=False) or not in this bitstream"
    lines = []
    for key, label in (("in", "msg in "), ("out", "msg out"),
                       ("cw_out", "cw  out"), ("cw_in", "cw  in ")):
        b = r.obs.get(key)
        if not b:
            continue
        lines.append(f"  {label} {b['productive']:>8} beats / {b['window']:>8} cyc "
                     f"= {b['utilisation']:6.1%}  (bp {b['backpressure']}, "
                     f"starv {b['starvation']}, idle {b['idle']})")
    i, o = r.obs.get("in"), r.obs.get("out")
    if i and o and i["productive"]:
        lines.append(f"  out/in message beats = {o['productive'] / i['productive']:.3f}")
    return "\n".join(lines)


def bandwidth_slope(small, large, n: int, k: int, s: int) -> str:
    cw_beats = -(-n // s)
    msg_beats = -(-k // s)
    db = large.blocks - small.blocks
    if db <= 0:
        return "bandwidth_slope needs two different block counts"
    out = [f"  slope over {small.blocks} -> {large.blocks} blocks "
           f"(fill cancelled; codeword {cw_beats} beats, message {msg_beats})"]
    for key, label, ideal in (("in", "msg in ", msg_beats), ("out", "msg out", msg_beats),
                              ("cw_out", "cw  out", cw_beats), ("cw_in", "cw  in ", cw_beats)):
        a, b = small.obs.get(key), large.obs.get(key)
        if not a or not b:
            continue
        d_prod = b["productive"] - a["productive"]
        d_win = b["window"] - a["window"]
        util = (d_prod / d_win) if d_win else 0.0
        per_blk = d_win / db
        out.append(f"  {label} {d_prod:>8} beats / {d_win:>8} cyc = {util:6.1%}"
                   f"   {per_blk:6.2f} cyc/block (ideal {ideal})")
    return "\n".join(out)


@dataclass
class SweepRow:
    count: int
    result: RunResult
    complaints: List[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.complaints


def sweep(drv: BchLoopDriver, counts: Iterable[int], blocks: int = 16, t: int = CFG_T,
          gen_seed: int = 0, throttle: bool = False) -> List[SweepRow]:
    rows = []
    for e in counts:
        r = run(drv, BchLoopDriver.INJ_COUNT, count=e, blocks=blocks, gen_seed=gen_seed,
                throttle=throttle)
        rows.append(SweepRow(count=e, result=r, complaints=verdict(r, t)))
    return rows


def format_row(row: SweepRow) -> str:
    r = row.result
    return (f"e={row.count:>2}  cyc/blk={r.cycles_per_block:7.1f}  "
            f"RIBM ok/corr/unc={r.a.blk_ok}/{r.a.blk_corr}/{r.a.blk_unc} sym={r.a.sym_corr} data={'x' if r.a.data_err else 'ok'}  "
            f"{'PASS' if row.ok else 'FAIL ' + '; '.join(row.complaints)}")
