# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""half_rot<d> family (pumice TASK-060): half-DRAM-burst transactions whose two
halves arrive d transactions apart, eight threads on one line.

Owner: "have the injectors issue 1/2 the dfi BL and the address are in bl-hi,
bl-lo, bl-hi, bl-lo ... an index i=0 to 7 where at 0 the addresses are in
order, at 1 it is 1/2 a dfi BL first, then 0, at 2 it is 1 full BL ahead ...
I want to see aggregation happen, but at some point it must stop happening
much."

Thread t owns a window of d DRAM bursts and walks it twice: the LOW half of
each burst, then the HIGH half (the injector's two-dimensional index: index 0
steps bursts by `stride_0` inside `wrap_mask_0`, index 1 -- the bits above
`idx1_shift` -- adds the half offset through `stride_1`). The two halves of
one burst are therefore d transactions apart; d = 1 is lo, hi back to back.
d is a power of two (the index split and the wrap are masks).

At the board geometry (BL4 x16, 32-bit beat on a 64-bit AXI) one DRAM burst
is ONE AXI beat, so a half burst is a 32-bit narrow transfer with strobes
(`axi_size` 4 bytes). Every byte of the line is written exactly once over
the two passes, so the per-32-bit-slice address hash checks the read-back.

IDs rotate per transaction (COUNTER mode, a disjoint 32-id base per thread):
a merged write's B must not pass an older same-id write's B, so with FIXED
ids the combiner would refuse every merge beyond d = 1.

What the controller does with it: pumice's write combiner merges the second
half into the first while the first has not committed (STORE_STATS_MERGE),
so `merges / host writes` is the aggregation ratio, and `PAGE_STATS_HIT`
(column ops) per host write is its dual: 0.5 when every pair merged, 1.0
when none did. The read pass runs the same programs through the read
combiner (rd CAM + return ring, STORE_STATS_RD_MERGE): the second half rides
the first half's DRAM burst while the first has not ISSUED, a shorter window
than the writer's.
"""
from __future__ import annotations

import math

from perf_mixed_family import PERF_SEED, seed_fields

HALF_BYTES_MIN = 4   # the narrowest half we issue (AXI_SIZE_4)


def parse_distance(fam_key: str) -> int:
    """'half_rot4' -> 4. Power of two, 1..8 at eight entries."""
    d = int(fam_key[len("half_rot"):] or "1", 0)
    assert d >= 1 and (d & (d - 1)) == 0, f"half_rot distance must be a power of two, got {d}"
    return d


def programs(d, n_gen, geom, dc, *, burst_bytes, line_base=0, seed=PERF_SEED, gap=0):
    """Per-thread engine programs for one direction at distance d.
    `burst_bytes` = one DRAM burst = the controller's legal-AxLEN quantum in
    bytes (DRAM_BL device words); the test passes its own geometry constants."""
    bb = burst_bytes
    half = bb // 2
    assert half >= HALF_BYTES_MIN, f"half burst {half} B below the narrowest AXI size"
    beat_bytes = geom.beat_bytes
    assert bb <= beat_bytes, ("half_rot assumes one DRAM burst per AXI beat (board geometry); "
                              f"burst {bb} B, beat {beat_bytes} B")
    size = int(math.log2(half))           # AxSIZE for a half burst
    k = int(math.log2(d))                  # idx1_shift: index 0 counts d bursts
    out = []
    for t in range(n_gen):
        start = line_base + t * d * bb
        if d == 1:
            # one-dimensional: lo, hi (stride half, wrap inside the burst)
            prog = dict(start_addr=start, stride_0=half, wrap_mask_0=bb - 1,
                        stride_1=0, wrap_mask_1=0, idx1_shift=0)
        else:
            prog = dict(start_addr=start, stride_0=bb, wrap_mask_0=d * bb - 1,
                        stride_1=half, wrap_mask_1=bb - 1, idx1_shift=k)
        prog.update(burst_len=1, txn_count=2 * d, gap=gap,
                    id_mode=dc.ID_MODE_COUNTER, axi_id=(t * 32) & 0xFF,
                    axi_size=size, data_mode=True, addr_lfsr=False, gen=t,
                    **seed_fields(t, seed=seed))
        out.append(prog)
    return out


def measure(drv, dc, pm, pc, geom, *, d, n_gen, burst_bytes, clk_mhz, hist_mean,
            diag=None, host_diag=None, always_diag=False, timeout_s=120,
            seed=PERF_SEED, reads=True, threads=None):
    """Write pass (the merge happens here), then a read pass that checks every
    byte of the line; returns the record the proxy logs, with the merge count
    and the column ops per host write."""
    bb = burst_bytes
    half = bb // 2
    # `threads` active generators out of the n_gen built (the rest idle): with
    # several threads the port mux issues every thread's low half before any
    # high half, so the distance between one burst's halves is ~threads x d;
    # one thread measures the index alone.
    t_act = n_gen if threads is None else max(1, min(int(threads), n_gen))
    prog = programs(d, t_act, geom, dc, burst_bytes=bb, seed=seed)
    txn_dir = sum(p["txn_count"] for p in prog)          # host transactions per direction
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
        diag[f"wr_half_rot{d}"] = host_diag(drv)
    tw = drv.timer()
    wr_cycles = max(int(tw.w_last) - int(tw.w_first), 0)
    wr_util = drv.perf_meters()["wr"].prod / max(wr_cycles, 1)
    wr_hist, wr_tot = drv.perf_hist_dump(dc.HIST_BUS_WR, dc.HIST_METRIC_0)
    delta = (ps1 - ps0) if (ps0 is not None and ps1 is not None) else None
    merges = delta.merges if delta is not None else None
    col_ops = delta.col_ops if delta is not None else None

    rd_ok, rd_cycles, rd_util, rd_hist, rd_tot = True, 0, 0.0, None, 0

    rd_lx = None
    rd_merges = rd_col_ops = None
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
        if rs0 is not None and rs1 is not None:
            rdelta = rs1 - rs0
            rd_merges, rd_col_ops = rdelta.rd_merges, rdelta.col_ops
        if (not rd_ok or always_diag) and diag is not None and host_diag is not None:
            diag[f"rd_half_rot{d}"] = host_diag(drv)
        tr = drv.timer()
        rd_cycles = max(int(tr.r_last) - int(tr.r_first), 0)
        rd_util = drv.perf_meters()["rd"].prod / max(rd_cycles, 1)
        rd_hist, rd_tot = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
        rd_lx = drv.perf_hist_stats(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    mism = drv.beats_mismatched()

    rec = {
        "family": f"half_rot{d}", "distance": d, "burst_bytes": bb, "half_bytes": half,
        "seed": seed, "gen_seeds": [p["lfsr_seed"] for p in prog],
        "txn": txn_dir, "burst_len": 1, "num_gen": n_gen, "threads": t_act,
        "bytes_moved": bytes_dir,
        "wr_ok": bool(wr_ok), "rd_ok": bool(rd_ok), "mismatched": int(mism),
        "wr_cycles": int(wr_cycles), "rd_cycles": int(rd_cycles),
        "wr_util": round(float(wr_util), 4), "rd_util": round(float(rd_util), 4),
        "wr_bw_mb_s": round(bytes_dir / wr_cycles * clk_mhz, 1) if wr_cycles else 0.0,
        "rd_bw_mb_s": round(bytes_dir / rd_cycles * clk_mhz, 1) if rd_cycles else 0.0,
        "wr_lat_cyc": round(hist_mean(wr_hist, wr_tot), 1),
        "rd_lat_cyc": round(hist_mean(rd_hist, rd_tot), 1) if rd_hist is not None else 0.0,
        **dc.lat_fields("rd", rd_lx),
        "clk_mhz": round(clk_mhz, 4),
        # the aggregation numbers (write pass): None when the build has no counters
        "wr_merges": merges, "wr_col_ops": col_ops,
        "wr_merge_ratio": (round(merges / txn_dir, 4) if merges is not None else None),
        "wr_col_ops_per_txn": (round(col_ops / txn_dir, 4) if col_ops is not None else None),
        # the same two for the read pass (read combiner)
        "rd_merges": rd_merges, "rd_col_ops": rd_col_ops,
        "rd_merge_ratio": (round(rd_merges / txn_dir, 4) if rd_merges is not None else None),
        "rd_col_ops_per_txn": (round(rd_col_ops / txn_dir, 4) if rd_col_ops is not None else None),
    }
    return rec
