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

Two more window families live here (TASK-049), run through the proxies'
ordinary write-then-read flow with per-generator programs from
`family_programs`:

  * `row_thrash`: one thread, one bank, TWO rows, a burst to each in turn
    (idx1_shift 1: index bit 0 picks the row via stride_0 = one row, the
    rest walks bursts inside the page via stride_1 / wrap_mask_1). The
    textbook row-buffer-conflict stream: with 2-beat bursts eight of them sit
    in a 16-entry window, a row-hit scheduler serves the four A hits then the
    four B hits (two ACTs), an oldest-first per-bank picker alternates (eight).
    Thread g owns bank g.
  * `random`: one thread, an LFSR index (addr_lfsr 1) walking bursts inside a
    region of two rows across all banks (wrap_mask_0 = 2 rows - 1), so every
    burst is a random bank and one of two rows -- a hit/miss mix in random
    order. Thread g owns rows 2g, 2g+1. Addresses repeat, so the data mode
    must be the address hash (it is, in both proxies).

One module, imported by both proxies, so the two measure the same thing.
"""

ROW_THRASH_ROW = 0x11    # first of the two rows (second is the next row)
RANDOM_ROWS = 2          # rows per thread in the random region


# The ONE seed for every perf proxy (pumice, granite, LiteDRAM): thread g of a
# family gets gen_seed(g), a direction region adds 0x100000. All three proxies
# import these, so a grid cell is the same address and data stream on each
# controller by construction, and every result record carries the seeds it ran
# with (owner, 2026-10-23: "ensure all three agents are seeded the same").
PERF_SEED = 0xABCD1234


def gen_seed(g, region=0, seed=PERF_SEED):
    return seed + 0x1000 * g + 0x100000 * region


def seed_fields(g, region=0, seed=PERF_SEED):
    """Engine-program kwargs that carry the seed: the data/address LFSR seed and
    the three address-hash seeds derived from it."""
    s = gen_seed(g, region, seed)
    return dict(lfsr_seed=s, hash_seed0=s, hash_seed1=s ^ 0x9E3779B9,
                hash_seed2=s ^ 0x85EBCA6B)


def family_programs(fam, n_gen, geom, dc, *, blen, txn, gap, seed=PERF_SEED):
    """Per-generator engine programs for `row_thrash` / `random`, or None."""
    if fam not in ("row_thrash", "random"):
        return None
    beat_bytes = 1 << dc.AXI_SIZE_8
    burst = blen * beat_bytes
    out = []
    for g in range(n_gen):
        common = dict(burst_len=blen, txn_count=txn, gap=gap, id_mode=dc.ID_MODE_FIXED,
                      axi_size=dc.AXI_SIZE_8, data_mode=True, gen=g,
                      **seed_fields(g, seed=seed))
        if fam == "row_thrash":
            bank = g % (1 << geom.bank_width)
            out.append(dict(start_addr=bank * geom.bank_stride
                            + ROW_THRASH_ROW * geom.row_stride_same_bank,
                            stride_0=geom.row_stride_same_bank, wrap_mask_0=0,
                            stride_1=burst, wrap_mask_1=geom.page_bytes - 1,
                            idx1_shift=1, addr_lfsr=False, **common))
        else:
            region = RANDOM_ROWS * geom.row_stride_same_bank
            out.append(dict(start_addr=g * region, stride_0=burst, wrap_mask_0=region - 1,
                            stride_1=0, wrap_mask_1=0, idx1_shift=0, addr_lfsr=True,
                            **common))
    return out

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
        out.append(dict(start_addr=bank * geom.bank_stride + row * geom.row_stride_same_bank,
                        burst_len=blen, txn_count=txn, stride_0=stride,
                        wrap_mask_0=wrap, gap=gap, id_mode=dc.ID_MODE_FIXED,
                        axi_size=dc.AXI_SIZE_8, data_mode=True, gen=g,
                        **seed_fields(g, region, seed)))
    return out


def measure(drv, dc, pm, geom, *, n_gen, blen, txn, gap, clk_mhz,
            hist_mean, diag=None, host_diag=None, always_diag=False,
            timeout_s=120, seed=PERF_SEED):
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
    rd_lx = drv.perf_hist_stats(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    mism = drv.beats_mismatched()
    return {
        "family": "mixed", "stride": wr_prog[0]["stride_0"], "wrap": wr_prog[0]["wrap_mask_0"],
        "seed": seed, "wr_seeds": [p["lfsr_seed"] for p in wr_prog],
        "rd_seeds": [p["lfsr_seed"] for p in rd_prog],
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
        **dc.lat_fields("rd", rd_lx),
        "clk_mhz": round(clk_mhz, 4),
    }


# ---- conc_*: the board's 1 writer + 1 reader (2026-10-26) ------------------
# The board's `concurrent` profile runs one writer and one reader from one GO
# on adjacent power-of-two regions; on granite's map two adjacent regions of
# a whole walk are the SAME banks at different rows (conc_rows), and a walk
# that fits one page puts the reader in the NEXT BANK at the same row
# (conc_banks). Both collapsed on the board (54 / 45 MB/s combined against
# pumice's 553 / 571 through the same harness) while every single-direction
# stream ran at 96 percent of peak, so this is the proxy for that cell.
# Writer = generator 0, reader = generator 1 (needs TEST_NUM_GEN >= 2).
CONC_FAMILIES = ("conc_rows", "conc_banks", "conc_colmajor")


def conc_programs(fam, geom, dc, *, blen, txn, gap, seed=PERF_SEED):
    """(writer program, reader program) for one conc family."""
    beat_bytes = 1 << dc.AXI_SIZE_8
    stride = blen * beat_bytes
    span = txn * stride
    span = 1 << max(0, (span - 1).bit_length())       # the board rounds up to pow2
    if fam == "conc_rows":
        wr_start, rd_start, wrap = 0, span, 0          # adjacent regions, whole walk
    elif fam == "conc_banks":
        wr_start, rd_start = 0, geom.bank_stride        # next bank, same row
        wrap = geom.page_bytes - 1                      # ... each walk inside its page
    elif fam == "conc_colmajor":
        # the board's `concurrent` profile on col_major (measure_concurrent,
        # regions placement): a col_major walk spans the device, so writer
        # and reader split it in halves -- the same banks, rows apart -- and
        # each walks one bank's rows (stride = same-bank row stride)
        half = geom.device_bytes // 2
        wr_start, rd_start = 0, half
        stride, wrap = geom.row_stride_same_bank, half - 1
    else:
        raise ValueError(fam)
    common = dict(burst_len=blen, txn_count=txn, stride_0=stride, wrap_mask_0=wrap, gap=gap,
                  id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8, data_mode=True)
    wr = dict(start_addr=wr_start, gen=0, **common, **seed_fields(0, 0, seed))
    rd = dict(start_addr=rd_start, gen=1, **common, **seed_fields(1, 1, seed))
    return wr, rd


def measure_conc(fam, drv, dc, pm, geom, *, n_gen, blen, txn, gap, clk_mhz,
                 hist_mean, diag=None, host_diag=None, always_diag=False,
                 timeout_s=120, seed=PERF_SEED):
    """One writer and one reader from one GO; the same record shape as mixed."""
    assert n_gen >= 2, f"{fam} needs >= 2 generators (TEST_NUM_GEN={n_gen})"
    beat_bytes = 1 << dc.AXI_SIZE_8
    bytes_dir = txn * blen * beat_bytes
    wr_prog, rd_prog = conc_programs(fam, geom, dc, blen=blen, txn=txn, gap=gap, seed=seed)

    # Untimed pre-pass: the reader's region, written by generator 1's write engine.
    drv.freeze_trace(True)
    drv.program_wr_engine(**rd_prog)
    drv.start_wr(0b10)
    pre_ok = pm.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
    if not pre_ok and diag is not None and host_diag is not None:
        diag[f"{fam}_prepass"] = host_diag(drv)

    drv.program_wr_engine(**wr_prog)
    drv.program_rd_engine(**rd_prog)
    drv.clear_stats()
    drv.timer_clear()
    drv.freeze_trace(False)
    drv.go(wr_mask=0b01, rd_mask=0b10)
    wr_ok = pm.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
    rd_ok = pm.wait_engine(drv, "rd", timeout_s=timeout_s, ignore_error=True)
    if (not (wr_ok and rd_ok) or always_diag) and diag is not None and host_diag is not None:
        diag[fam] = host_diag(drv)
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
    rd_lx = drv.perf_hist_stats(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    mism = drv.beats_mismatched()
    return {
        "family": fam, "stride": wr_prog["stride_0"], "wrap": wr_prog["wrap_mask_0"],
        "wr_start": wr_prog["start_addr"], "rd_start": rd_prog["start_addr"],
        "seed": seed, "wr_seeds": [wr_prog["lfsr_seed"]], "rd_seeds": [rd_prog["lfsr_seed"]],
        "txn": txn, "burst_len": blen, "num_gen": 2,
        "bytes_moved": 2 * bytes_dir, "prepass_ok": bool(pre_ok),
        "wr_ok": bool(wr_ok), "rd_ok": bool(rd_ok), "mismatched": int(mism),
        "wr_cycles": int(wr_cycles), "rd_cycles": int(rd_cycles),
        "mixed_cycles": int(mixed_cycles),
        "wr_util": round(float(wr_util), 4), "rd_util": round(float(rd_util), 4),
        "wr_bw_mb_s": round(bytes_dir / wr_cycles * clk_mhz, 1) if wr_cycles else 0.0,
        "rd_bw_mb_s": round(bytes_dir / rd_cycles * clk_mhz, 1) if rd_cycles else 0.0,
        "mixed_bw_mb_s": round(2 * bytes_dir / mixed_cycles * clk_mhz, 1) if mixed_cycles else 0.0,
        "wr_lat_cyc": round(hist_mean(wr_hist, wr_tot), 1),
        "rd_lat_cyc": round(hist_mean(rd_hist, rd_tot), 1),
        **dc.lat_fields("rd", rd_lx),
        "clk_mhz": round(clk_mhz, 4),
    }
