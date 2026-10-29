# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Half-burst families (pumice TASK-060, the four board patterns, owner
2026-10-25): every host transaction is HALF a DRAM burst, and the family
sets the order the halves arrive in and the pacing between them.

    half_pair        l0 h0 l1 h1 l2 h2 ...        the two halves back to back
    half_oct         l0..l7 h0..h7 l8..l15 h8..h15 ...   eight lows, then their highs
    half_pair_sweep  half_pair with the inter-transaction gap looping 0..7 clocks
    half_oct_sweep   half_oct  with the inter-transaction gap looping 0..7 clocks

One implementation for the proxy and the board (FPGA == sim): the proxy test
and `pumice_char` both program the engines from :func:`programs` here, so a
number from either side came from the same address walk.

How the walk is formed -- pure injector programming on the one-bit index
split (`idx1_bit`, injector header): dimension 1 is the single bit k of the
transaction index (stride_1 = half a burst), dimension 0 the index with that
bit removed (stride_0 = one DRAM burst). k = 0 toggles the half every
transaction (pair), k = 3 every eight (oct). The gap sweep is the injector's
`gap_sweep`: the idle gap after transaction n is gap + (n mod 8).

At the board geometry (BL4 x16, 8-byte DRAM burst, 8-byte AXI beat) a half
burst is one 4-byte narrow beat with strobes (AxSIZE 4). Every byte of the
line is written exactly once over the two passes, so the per-32-bit-slice
address hash checks the read-back exactly.

IDs rotate per transaction (COUNTER mode, a disjoint 32-id base per thread):
a merged write's B must not pass an older same-id write's B, so with FIXED
ids the combiner would refuse every merge beyond the first.

What to read off a run: pumice's write combiner merges the high half into the
low half while the low half has not committed (`STORE_STATS_MERGE`), so
merges / host writes is the aggregation ratio and `PAGE_STATS_HIT` (column
ops) per host write is its dual -- 0.5 when every pair merged, 1.0 when none
did. The one-thread proxy knee (2026-10-25) is between a distance of 4 and 8:
half_pair should merge every pair, half_oct none, and the sweeps show how
much pacing the merge window tolerates.
"""
from __future__ import annotations

import math
import os
from typing import Dict, List, Optional, Tuple

FAM_HALF_PAIR       = "half_pair"
FAM_HALF_OCT        = "half_oct"
FAM_HALF_PAIR_SWEEP = "half_pair_sweep"
FAM_HALF_OCT_SWEEP  = "half_oct_sweep"
FAMILIES: Tuple[str, ...] = (FAM_HALF_PAIR, FAM_HALF_OCT,
                             FAM_HALF_PAIR_SWEEP, FAM_HALF_OCT_SWEEP)

# (k = the index bit that toggles the half, gap sweep on) per family
_SPEC: Dict[str, Tuple[int, bool]] = {
    FAM_HALF_PAIR:       (0, False),
    FAM_HALF_OCT:        (3, False),
    FAM_HALF_PAIR_SWEEP: (0, True),
    FAM_HALF_OCT_SWEEP:  (3, True),
}

HALF_BYTES_MIN = 4          # the narrowest half we issue (AXI_SIZE_4)
IDS_PER_THREAD = 32         # disjoint COUNTER-mode id bases


def is_half_family(fam: str) -> bool:
    return fam in _SPEC


def spec(fam: str) -> Tuple[int, bool]:
    """(k, sweep) for a family name; KeyError for anything else."""
    return _SPEC[fam]


def half_bytes(burst_bytes: int) -> int:
    half = burst_bytes // 2
    assert half >= HALF_BYTES_MIN, f"half burst {half} B below the narrowest AXI size"
    return half


def programs(fam: str, n_bursts: int, geom, dc, *, burst_bytes: int, threads: int = 1,
             line_base: int = 0, seed: int = 0x5EED_0060, seed_fields=None,
             gap: int = 0) -> List[dict]:
    """Per-thread engine programs for one direction.

    `n_bursts` DRAM bursts per thread (2 x n_bursts host transactions);
    `burst_bytes` = one DRAM burst = the controller's legal-AxLEN quantum in
    bytes; thread t owns the contiguous region t of the line. `seed_fields`
    (thread -> dict of lfsr/hash seeds) lets a caller share its seeding
    convention; without it a stable per-thread derivation of `seed` is used.
    """
    k, sweep = spec(fam)
    bb = burst_bytes
    half = half_bytes(bb)
    assert bb <= geom.beat_bytes, ("half-burst families assume one DRAM burst per AXI "
                                   f"beat (board geometry); burst {bb} B, beat {geom.beat_bytes} B")
    assert n_bursts >= (1 << k), f"{fam}: need at least {1 << k} bursts per thread, got {n_bursts}"
    size = int(math.log2(half))
    out = []
    for t in range(threads):
        fields = (seed_fields(t) if seed_fields is not None
                  else _default_seed_fields(t, seed))
        out.append(dict(start_addr=line_base + t * n_bursts * bb,
                        stride_0=bb, wrap_mask_0=0,
                        stride_1=half, wrap_mask_1=0,
                        idx1_shift=k, idx1_bit=True, addr_lfsr=False,
                        burst_len=1, txn_count=2 * n_bursts, gap=gap, gap_sweep=sweep,
                        # HALF_ID_FIXED=1: one ID per thread (a single in-order master's
                        # halves); default COUNTER (distinct IDs). granite TASK-005.
                        id_mode=(dc.ID_MODE_FIXED if os.environ.get("HALF_ID_FIXED", "0") not in ("", "0")
                                 else dc.ID_MODE_COUNTER),
                        axi_id=(t * IDS_PER_THREAD) & 0xFF,
                        axi_size=size, data_mode=True, gen=t, **fields))
    return out


def _default_seed_fields(t: int, seed: int) -> dict:
    s = (seed + 0x9E37_79B9 * (t + 1)) & 0xFFFF_FFFF
    return dict(lfsr_seed=s or 1, hash_seed0=s,
                hash_seed1=(s ^ 0x9E37_79B9) & 0xFFFF_FFFF,
                hash_seed2=(s ^ 0x85EB_CA6B) & 0xFFFF_FFFF)


def expected_order(fam: str, n: int) -> List[Tuple[int, int]]:
    """(burst, half) for transactions 0..n-1 -- the documentation of the
    walk in executable form, used by the unit check."""
    k, _ = spec(fam)
    out = []
    for i in range(n):
        half = (i >> k) & 1
        burst = (i & ((1 << k) - 1)) | ((i >> (k + 1)) << k)
        out.append((burst, half))
    return out


def aggregation(merges: Optional[int], col_ops: Optional[int], txn: int,
                prefix: str = "wr") -> dict:
    """The two aggregation figures for one pass, None-safe. `prefix` names the
    direction: the write pass counts STORE_STATS_MERGE, the read pass
    STORE_STATS_RD_MERGE (both combiners, pumice TASK-060)."""
    return {
        f"{prefix}_merges": merges, f"{prefix}_col_ops": col_ops,
        f"{prefix}_merge_ratio": (round(merges / txn, 4) if merges is not None and txn else None),
        f"{prefix}_col_ops_per_txn": (round(col_ops / txn, 4) if col_ops is not None and txn else None),
    }


def measure_dict(drv, dc, pm, pc, geom, *, fam: str, n_bursts: int, n_gen: int,
                 burst_bytes: int, clk_mhz: float, hist_mean, threads: Optional[int] = None,
                 diag=None, host_diag=None, always_diag=False, timeout_s=120,
                 seed_fields=None, reads=True) -> dict:
    """The proxy test's record for one family: a write pass (where the merge
    happens), then a read pass that checks every byte of the line."""
    t_act = n_gen if threads is None else max(1, min(int(threads), n_gen))
    prog = programs(fam, n_bursts, geom, dc, burst_bytes=burst_bytes, threads=t_act,
                    seed_fields=seed_fields)
    half = half_bytes(burst_bytes)
    txn_dir = sum(p["txn_count"] for p in prog)
    bytes_dir = txn_dir * half
    mask = (1 << t_act) - 1

    def snap():
        try:
            return pc.read_page_stats(drv)
        except Exception:                                 # noqa: BLE001
            return None

    drv.freeze_trace(True)
    for p in prog:
        drv.program_wr_engine(**p)
    drv.clear_stats(); drv.timer_clear()
    ps0 = snap()
    drv.freeze_trace(False)
    drv.start_wr(mask)
    wr_ok = pm.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
    drv.freeze_trace(True)
    ps1 = snap()
    if (not wr_ok or always_diag) and diag is not None and host_diag is not None:
        diag[f"wr_{fam}"] = host_diag(drv)
    tw = drv.timer()
    wr_cycles = max(int(tw.w_last) - int(tw.w_first), 0)
    wr_util = drv.perf_meters()["wr"].prod / max(wr_cycles, 1)
    wr_hist, wr_tot = drv.perf_hist_dump(dc.HIST_BUS_WR, dc.HIST_METRIC_0)
    delta = (ps1 - ps0) if (ps0 is not None and ps1 is not None) else None

    rd_ok, rd_cycles, rd_util, rd_hist, rd_tot = True, 0, 0.0, None, 0
    rdelta = None
    if reads:
        for p in prog:
            drv.program_rd_engine(**p)
        drv.clear_stats(); drv.timer_clear()
        rs0 = snap()
        drv.freeze_trace(False)
        drv.start_rd(mask)
        rd_ok = pm.wait_engine(drv, "rd", timeout_s=timeout_s, ignore_error=True)
        drv.freeze_trace(True)
        rs1 = snap()
        rdelta = (rs1 - rs0) if (rs0 is not None and rs1 is not None) else None
        if (not rd_ok or always_diag) and diag is not None and host_diag is not None:
            diag[f"rd_{fam}"] = host_diag(drv)
        tr = drv.timer()
        rd_cycles = max(int(tr.r_last) - int(tr.r_first), 0)
        rd_util = drv.perf_meters()["rd"].prod / max(rd_cycles, 1)
        rd_hist, rd_tot = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    mism = drv.beats_mismatched()
    k, sweep = spec(fam)
    rec = {
        "family": fam, "k": k, "gap_sweep": sweep, "burst_bytes": burst_bytes, "half_bytes": half,
        "gen_seeds": [p["lfsr_seed"] for p in prog],
        "txn": txn_dir, "burst_len": 1, "num_gen": n_gen, "threads": t_act,
        "bytes_moved": bytes_dir,
        "wr_ok": bool(wr_ok), "rd_ok": bool(rd_ok), "mismatched": int(mism),
        "wr_cycles": int(wr_cycles), "rd_cycles": int(rd_cycles),
        "wr_util": round(float(wr_util), 4), "rd_util": round(float(rd_util), 4),
        "wr_bw_mb_s": round(bytes_dir / wr_cycles * clk_mhz, 1) if wr_cycles else 0.0,
        "rd_bw_mb_s": round(bytes_dir / rd_cycles * clk_mhz, 1) if rd_cycles else 0.0,
        "wr_lat_cyc": round(hist_mean(wr_hist, wr_tot), 1),
        "rd_lat_cyc": round(hist_mean(rd_hist, rd_tot), 1) if rd_hist is not None else 0.0,
        "clk_mhz": round(clk_mhz, 4),
    }
    rec.update(aggregation(delta.merges if delta is not None else None,
                           delta.col_ops if delta is not None else None, txn_dir))
    rec.update(aggregation(rdelta.rd_merges if rdelta is not None else None,
                           rdelta.col_ops if rdelta is not None else None, txn_dir, prefix="rd"))
    return rec
