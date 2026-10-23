"""The `mixed` family of the ddr2_char perf proxies (pumice, granite).

The four stride families are streams: incremental and row_major are all
page hits, col_major and col_ilv are all page misses, and each phase is one
direction. None of them exercises what a scheduling window is FOR, which is
re-ordering a mix of hits and misses from several requestors so that the
hits of an open row go out together. `mixed` is that workload, built from
the harness's one-dimensional generators:

  * generators are PAIRED on a bank: generator g and generator g + n/2 both
    walk bank (g mod n/2), one row apart (row group g div n/2). Each walks
    its own row row_major, so inside a thread every burst is a page hit and
    between the two threads of a pair every burst is a conflict. A row-hit
    scheduler groups the pairs' same-row bursts; an oldest-first per-bank
    picker alternates the rows and pays a PRE + ACT per burst;
  * reads and writes run CONCURRENTLY (one GO), write region and read region
    `REGION_ROWS` rows apart in the same banks, so the window also carries
    read/write turnarounds and cross-direction bank conflicts;
  * the read region is written first, untimed, so the data check holds (a
    read of never-written DRAM mismatches by construction).

Bandwidth is the harness formula over the union window: total bytes moved
by both directions divided by (last stamp of either - first stamp of either),
plus each direction's own window as the other families report it. There is
no JEDEC floor for this family; it is compared across cores, not against a
number.

One module, imported by both proxies, so the two measure the same thing.
"""

REGION_ROWS = 8          # read region sits this many rows above the write region
MIN_GENS = 2             # one pair at least; a single generator has no conflict


def layout(n_gen, geom):
    """Per-generator (bank, row_group) placement. Pairs share a bank."""
    pairs = max(1, n_gen // 2)
    return [(g % pairs, g // pairs) for g in range(n_gen)]


def programs(n_gen, geom, dc, *, blen, txn, gap, seed, region):
    """Engine programs for one direction. `region` 0 = write rows, 1 = read
    rows (REGION_ROWS further up the same bank)."""
    beat_bytes = 1 << dc.AXI_SIZE_8
    stride = blen * beat_bytes                 # row_major: one burst after the other
    wrap = geom.page_bytes - 1                 # ... wrapped inside the page
    out = []
    for g, (bank, rowgrp) in enumerate(layout(n_gen, geom)):
        row = rowgrp + region * REGION_ROWS
        s = seed + 0x1000 * g + 0x100000 * region
        out.append(dict(start_addr=bank * geom.bank_stride + row * geom.row_stride_same_bank,
                        burst_len=blen, txn_count=txn, stride_0=stride,
                        wrap_mask_0=wrap, gap=gap, id_mode=dc.ID_MODE_FIXED,
                        axi_size=dc.AXI_SIZE_8, data_mode=True, lfsr_seed=s,
                        hash_seed0=s, hash_seed1=s ^ 0x9E3779B9,
                        hash_seed2=s ^ 0x85EBCA6B, gen=g))
    return out


def measure(drv, dc, pm, geom, *, n_gen, blen, txn, gap, clk_mhz,
            hist_mean, diag=None, host_diag=None, always_diag=False,
            timeout_s=120, seed=0xABCD1234):
    """Run the mixed family and return the record the proxies log.

    Keys match the stride families (wr_/rd_ cycles, bw, util, lat, mismatched,
    wr_ok / rd_ok) and add `mixed_cycles` / `mixed_bw_mb_s` for the union
    window and `layout` for the placement actually programmed.
    """
    assert n_gen >= MIN_GENS, f"mixed needs >= {MIN_GENS} generators (TEST_NUM_GEN={n_gen})"
    beat_bytes = 1 << dc.AXI_SIZE_8
    bytes_dir = txn * blen * beat_bytes * n_gen
    mask = (1 << n_gen) - 1
    wr_prog = programs(n_gen, geom, dc, blen=blen, txn=txn, gap=gap, seed=seed, region=0)
    rd_prog = programs(n_gen, geom, dc, blen=blen, txn=txn, gap=gap, seed=seed, region=1)

    # Untimed pre-pass: put the read region's expected data in the DRAM.
    drv.freeze_trace(True)
    for p in rd_prog:
        drv.program_wr_engine(**p)
    drv.start_wr(mask)
    pre_ok = pm.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
    if not pre_ok and diag is not None and host_diag is not None:
        diag["mixed_prepass"] = host_diag(drv)

    # Timed phase: both directions from one GO.
    for p in wr_prog:
        drv.program_wr_engine(**p)
    for p in rd_prog:
        drv.program_rd_engine(**p)
    drv.clear_stats()
    drv.timer_clear()
    drv.freeze_trace(False)
    drv.go(wr_mask=mask, rd_mask=mask)
    wr_ok = pm.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
    rd_ok = pm.wait_engine(drv, "rd", timeout_s=timeout_s, ignore_error=True)
    if (not (wr_ok and rd_ok) or always_diag) and diag is not None and host_diag is not None:
        diag["mixed"] = host_diag(drv)
    drv.freeze_trace(True)
    t = drv.timer()
    w_first, w_last = int(t.w_first), int(t.w_last)
    r_first, r_last = int(t.r_first), int(t.r_last)
    wr_cycles = max(w_last - w_first, 0)
    rd_cycles = max(r_last - r_first, 0)
    mixed_cycles = max(max(w_last, r_last) - min(w_first, r_first), 0)
    meters = drv.perf_meters()
    wr_util = meters["wr"].prod / max(wr_cycles, 1)
    rd_util = meters["rd"].prod / max(rd_cycles, 1)
    wr_hist, wr_tot = drv.perf_hist_dump(dc.HIST_BUS_WR, dc.HIST_METRIC_0)
    rd_hist, rd_tot = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    mism = drv.beats_mismatched()
    return {
        "family": "mixed", "stride": wr_prog[0]["stride_0"], "wrap": wr_prog[0]["wrap_mask_0"],
        "txn": txn, "burst_len": blen, "num_gen": n_gen,
        "bytes_moved": 2 * bytes_dir,
        "layout": layout(n_gen, geom), "region_rows": REGION_ROWS,
        "prepass_ok": bool(pre_ok),
        "wr_ok": bool(wr_ok), "rd_ok": bool(rd_ok), "mismatched": int(mism),
        "wr_cycles": int(wr_cycles), "rd_cycles": int(rd_cycles),
        "mixed_cycles": int(mixed_cycles),
        "wr_util": round(float(wr_util), 4), "rd_util": round(float(rd_util), 4),
        "wr_bw_mb_s": round(bytes_dir / wr_cycles * clk_mhz, 1) if wr_cycles else 0.0,
        "rd_bw_mb_s": round(bytes_dir / rd_cycles * clk_mhz, 1) if rd_cycles else 0.0,
        "mixed_bw_mb_s": round(2 * bytes_dir / mixed_cycles * clk_mhz, 1) if mixed_cycles else 0.0,
        "wr_lat_cyc": round(hist_mean(wr_hist, wr_tot), 1),
        "rd_lat_cyc": round(hist_mean(rd_hist, rd_tot), 1),
        "clk_mhz": round(clk_mhz, 4),
    }
