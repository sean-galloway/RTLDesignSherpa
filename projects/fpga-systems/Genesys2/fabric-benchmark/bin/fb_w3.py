# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""W3, the contention pair (PRD §4.1, the DE10 PRD's F3 / F3-mirror), for sim
and board.

Two masters into one slave: STREAM and the injector (char_engine_block on M3)
both use S0 (DDR3) at once, in different regions, and the fabric decides who
gets it.

    f3      STREAM drains DDR3 region A into the CRC sink   (S0 reads)
            while the injector writes region C              (S0 writes)
    mirror  STREAM fills region A from the LFSR source      (S0 writes)
            while the injector writes region C              (S0 writes)

The injector's offered load -- and so the mix -- is set by its inter-burst
gap (owner decision 2026-10-16: the gap sets the mix; if it cannot reach a
mix, the injector is fixed rather than the definition changed). The 4-bit gap
could not: against S0's ~230 MiB/s it left the split at 50/50 at every
value, so chargen_regs gained BLEN_TXN.gap_shift and the gap is now
gap << gap_shift cycles, up to 1920. Its max_outstanding is the PRD's
outstanding axis.

Every point also ends in a data check, so contention cannot pass by
corrupting data: f3 drains a region an uncontended fill wrote and must
reproduce its LFSR CRC; the mirror's contended fill is drained afterwards,
uncontended, with the same check.

The share is measured over one window -- the STREAM observers' window, which
the injector's own bus meter shares -- as productive beats: STREAM's on the
side it uses at S0 (reads for f3, writes for the mirror) and the injector's
writes. inj_share = injector / (injector + STREAM).
"""
from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Optional

import fb_map
import fb_workloads as fw

CHARGEN_BASE = 0x0021_0000          # bridge_fb_cfg.toml, window chargen
INJ_SPAN = 16 << 20                 # the injector's whole reach: INJ_TXN_MAX x 16-beat bursts
INJ_TXN_MAX = 0xFFFF                # runs past the window; the next soft reset stops it
BEAT_BYTES = fb_map.DATA_WIDTH // 8


def _chargen_regmap() -> str:
    from TBClasses.shared.utilities import get_repo_root
    return os.path.join(get_repo_root(), 'projects/fpga-systems/rtl/mem_char_framework',
                        'dv/tbclasses/chargen_regs_regmap.py')


@dataclass(frozen=True)
class Inj:
    """One injector setting: the mix (gap << gap_shift idle cycles between
    bursts) and the outstanding axis."""
    gap: int = 0                 # BLEN_TXN.gap, 0..15
    outstanding: int = 4         # AXI_ATTR.max_outstanding (built ceiling 8)
    gap_shift: int = 0           # BLEN_TXN.gap_shift, 0..7
    burst_len: int = 16          # beats, same as STREAM's bursts
    seed: int = 0x1D2C3B4A

    def __post_init__(self):
        if not 0 <= self.gap <= 15:
            raise ValueError(f"gap {self.gap}: the injector's gap field is 0..15")
        if not 0 <= self.gap_shift <= 7:
            raise ValueError(f"gap_shift {self.gap_shift}: 0..7")
        if not 1 <= self.outstanding <= 8:
            raise ValueError(f"outstanding {self.outstanding}: built ceiling is 8")

    @property
    def idle_cycles(self) -> int:
        return self.gap << self.gap_shift

    @classmethod
    def for_idle(cls, idle: int, **kw) -> "Inj":
        """The (gap, gap_shift) with the smallest shift that reaches `idle`
        cycles, rounding down to what the register can express."""
        for shift in range(8):
            if idle >> shift <= 15:
                return cls(gap=idle >> shift, gap_shift=shift, **kw)
        return cls(gap=15, gap_shift=7, **kw)


def chargen(bridge):
    from TBClasses.harness.device import Device
    return Device(bridge, "chargen", regs_base=CHARGEN_BASE, regmap_file=_chargen_regmap())


def region_c(cfg) -> int:
    """The injector's region: right after the chain's regions A and B (the
    sim models S0 densely; an 8-channel point still lands well inside 1 GB)."""
    return fw.ddr_span(cfg)


def ddr_span(cfg) -> int:
    """Bytes of S0 a W3 point touches from 0, with room for the injector."""
    return region_c(cfg) + INJ_SPAN


def program_and_go(bridge, inj: Inj, start_addr: int) -> None:
    """Program write generator 0 by name and fire it. Runs as the runner's
    pre_kick hook: after its soft reset (which resets the injector too), just
    before STREAM's kick."""
    cg = chargen(bridge)
    n = "WR_GEN0"
    cg.write_word(f"{n}_START_ADDR", start_addr)
    cg.write_word(f"{n}_STRIDE_0", inj.burst_len * BEAT_BYTES)
    cg.write_word(f"{n}_STRIDE_1", 0)
    cg.write_word(f"{n}_WRAP_MASK_0", 0)
    cg.write_word(f"{n}_WRAP_MASK_1", 0)
    cg.write(f"{n}_BLEN_TXN", burst_len=inj.burst_len, txn_count=INJ_TXN_MAX, gap=inj.gap,
             gap_shift=inj.gap_shift)
    cg.write(f"{n}_AXI_ATTR", axi_id=0, id_mode=0, axi_size=(BEAT_BYTES - 1).bit_length(),
             axi_burst=1, data_mode=0, max_outstanding=inj.outstanding)
    cg.write_word(f"{n}_LFSR_SEED", inj.seed)
    cg.write_word(f"{n}_HASH_SEED0", 0)
    cg.write_word(f"{n}_HASH_SEED1", 0)
    cg.write_word(f"{n}_HASH_SEED2", 0)
    cg.write_word(f"{n}_FILL_PATTERN", 0)
    cg.write("GO", wr_go0=1)


def _inj_meter(bridge) -> dict:
    return {k: bridge.read(fw.C(f'INJ_WR_{k.upper()}'))
            for k in ('prod', 'bp', 'starv', 'idle')}


def _share(res: dict, side: str, bridge, hz: float) -> dict:
    met = res.get('metrics') or {}
    s_beats = ((met.get(f'{side}_aggregate') or {}).get('productive')) or 0
    inj = _inj_meter(bridge)
    window = met.get(f'{side}_window_cycles') or 0
    total = s_beats + inj['prod']
    mib = lambda beats: (beats * BEAT_BYTES / (1 << 20)) / (window / hz) if window else None
    return {'stream_beats': s_beats, 'inj_beats': inj['prod'], 'window_cycles': window,
            'inj_share': (inj['prod'] / total) if total else None,
            'stream_mibs': mib(s_beats), 'inj_mibs': mib(inj['prod']),
            'inj_meter': inj}


def quiesce(bridge, timeout_s: float = 10.0) -> bool:
    """Wait until S0 has no write outstanding (AW count == B count, stable).
    Needed before any soft reset or a step that reads what was just written:
    the run timer can stop before the last writes are committed at S0 (the
    mirror stops on STREAM's own port), and S0's controller is outside the
    soft-reset domain, so a reset with writes in flight wedges the fabric."""
    import time
    end = time.monotonic() + timeout_s
    prev = None
    while time.monotonic() < end:
        aw, b = bridge.read(fw.C('S0_AW_COUNT')), bridge.read(fw.C('S0_B_COUNT'))
        if aw == b and (aw, b) == prev:
            return True
        prev = (aw, b)
        time.sleep(0.01)
    return False


def run_point(runner, bridge, cfg, flavor: str, inj: Inj, log=print) -> dict:
    """One W3 point: the contended run and its data check. Returns the
    contended step's result with 'flavor', 'inj', share fields, 'verdict'
    and 'why'."""
    if flavor not in ('f3', 'mirror'):
        raise ValueError(f"flavor {flavor!r}: f3 or mirror")
    if not fw.wait_calib(bridge):
        return {'flavor': flavor, 'inj': inj, 'verdict': False,
                'why': ['DDR3 never finished calibrating (fb_ctl STATUS)']}
    go = lambda b: program_and_go(b, inj, region_c(cfg))
    why = []
    if flavor == 'f3':
        fill = fw.run_step(runner, bridge, cfg, 'lfsr', 'A')
        res = fw.run_step(runner, bridge, cfg, 'A', 'snk', pre_kick=go, inj_sync=True)
        inj_done = chargen(bridge).field("DONE", "wr_done") & 1
        if not quiesce(bridge):
            why.append("S0 never drained after the contended run")
        side, src_crc, drain = 'r', fill, res
    else:
        res = fw.run_step(runner, bridge, cfg, 'lfsr', 'A', wr_dst=fw.WR_DST_M2, pre_kick=go,
                          inj_sync=True)
        inj_done = chargen(bridge).field("DONE", "wr_done") & 1
        side, src_crc = 'w', res
        share_now = _share(res, side, bridge, runner.aclk_hz)   # before the drain clears it
        if not quiesce(bridge):                  # the fill must be committed before its drain
            why.append("S0 never drained after the contended fill")
        runner.reset_stream()                    # stop the injector before INJ_SYNC drops
        drain = fw.run_step(runner, bridge, cfg, 'A', 'snk')
    out = dict(res)
    out.update(share_now if flavor == 'mirror' else _share(res, side, bridge, runner.aclk_hz))
    want = cfg.num_channels * cfg.descriptors_per_channel * cfg.transfer_bytes // BEAT_BYTES
    for r, name in ((res, 'contended run'), (drain, 'drain')):
        if r.get('error'):
            why.append(f"{name}: {r['error']}")
    if out['stream_beats'] != want:
        why.append(f"STREAM moved {out['stream_beats']} beats in the window, want {want}")
    if not out['inj_beats']:
        why.append("the injector moved nothing in the window")
    if inj_done:
        why.append("the injector finished inside the window (its share is truncated)")
    a = (src_crc.get('crc') or {}).get('rd_per_ch') or []
    b = (drain.get('crc') or {}).get('wr_per_ch') or []
    for ch in range(cfg.num_channels):
        x = a[ch] if ch < len(a) else None
        y = b[ch] if ch < len(b) else None
        if not x or x != y:
            why.append(f"ch{ch}: drained CRC 0x{(y or 0):08X} != LFSR CRC 0x{(x or 0):08X}")
    out.update(flavor=flavor, inj=inj, verdict=not why, why=why)
    # Stop the injector: it runs to INJ_TXN_MAX otherwise (it sits in the soft
    # reset domain, so the runner's reset does it).
    runner.reset_stream()
    fw.set_workload(bridge, False, fw.WR_DST_SINK)
    share = out['inj_share']
    log(f"  {flavor} idle {inj.idle_cycles:4d} out {inj.outstanding}: "
        f"{'PASS' if out['verdict'] else 'FAIL'} inj_share "
        f"{'-' if share is None else f'{100 * share:5.1f}%'}  "
        f"STREAM {out['stream_mibs'] or 0:7.1f} MiB/s  inj {out['inj_mibs'] or 0:7.1f} MiB/s"
        + (f"  {'; '.join(why)}" if why else ''))
    return out
