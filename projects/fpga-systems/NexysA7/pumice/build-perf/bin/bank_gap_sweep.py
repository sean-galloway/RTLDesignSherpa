#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board sweep: N generators on N DIFFERENT banks, against gap and address order.

Each measured point is ONE scenario, written and then read back:

    for each (generators, address order, gap):
        program N writers  -- that order, that gap, one bank each
        run them, measure the WRITE
        program N readers  -- the SAME addressing, burst length and bases
        run them, measure the READ and check every beat

Writer and reader touch exactly the same addresses, so the point is
self-contained: nothing it reads was left there by an earlier point, and
nothing it writes is relied on by a later one. That is what lets each point
carry its own seed -- and the seed is the check. Reading a region some previous
scenario wrote shows up as a mismatch instead of as a plausible number, which
is exactly the failure a shared-seed fill cannot see.

The axes:

  generators  4, 3, 2, 1. Each gets its own bank, spread rather than adjacent
              -- four land on banks 0, 2, 4, 6 -- so a bank-group effect reads
              as a pattern rather than as one cliff.
  gap         0..15 idle clocks between bursts. Zero is back-to-back; the top
              of the range is idle enough that the controller should be able to
              close and re-open pages for free. Where the curve flattens is
              where the generators stop being the limit.
  order       cacheline  contiguous march, one burst after the next. Crosses
                         pages and banks the way a cache-line-filling master
                         does. Best case.
              row-major  wrapped inside one page, so every burst is a page HIT.
                         Isolates the column-access rate from activate cost.
              col-major  same column of the next row in the same bank, so every
                         burst is a page MISS. Isolates activate/precharge.

The gap is 0..15, not 0..16: chargen_regs' gap field is four bits
(blen_txn.gap[27:24]). Programming 16 would write 0 and silently measure the
back-to-back case a second time, so the range stops at 15 and says so here
rather than leaving a reader to wonder.

How much memory a point covers is a property of its order, not a constant: at
the default 2000 bursts of 64 B, cacheline marches through 128 KiB per
generator, col-major steps across 32 MiB of rows inside its bank, and row-major
re-reads one 2 KiB page some sixty times. That is the families doing their job.
TXN scales all three together.

    PUMICE_MC_CLK_HZ=75000000 python3 bin/bank_gap_sweep.py     # from build-perf/
    GAPS=0,4,8,15 GENS=4,1 python3 bin/bank_gap_sweep.py
    TXN=20000 python3 bin/bank_gap_sweep.py                     # wider spans
"""
import os
import sys

sys.path.insert(0, 'host')
import ddr2_char as dc
from ddr2_char import DDR2CharDriver
import pumice_master as pm
import pumice_char as pc

CLK_MHZ  = float(os.environ.get("PUMICE_MC_CLK_HZ", "75000000")) / 1e6
PEAK_MBS = 8 * CLK_MHZ                      # 8 bytes/beat at one beat/cycle

GAPS  = [int(x) for x in os.environ.get("GAPS", ",".join(str(g) for g in range(16))).split(",")]
GENS  = [int(x) for x in os.environ.get("GENS", "4,3,2,1").split(",")]
TXN   = int(os.environ.get("TXN", "2000"))
BEATS = int(os.environ.get("BEATS", "8"))   # 8 beats x 8 B = 64 B bursts

ORDERS = [
    ("cacheline", pc.FAM_INCREMENTAL),
    ("row_major", pc.FAM_ROW_MAJOR),
    ("col_major", pc.FAM_COL_MAJOR),
]

if TXN > pc.TXN_MAX:
    raise SystemExit(f"TXN={TXN} exceeds the 16-bit txn_count field ({pc.TXN_MAX})")


def _program(drv, which, geom, n_gen, family, gap, seed):
    """Program n_gen engines of one direction for this scenario, one per bank."""
    banks_apart = (1 << geom.bank_width) // n_gen      # spread, not adjacent
    sc = pc.Scenario(name=f"{family}_g{n_gen}_gap{gap}", family=family,
                     burst_len=BEATS, txn_count=TXN, gap=gap)
    stride, wrap = pc.strides_for(sc, geom)
    fn = drv.program_wr_engine if which == "wr" else drv.program_rd_engine
    for g in range(n_gen):
        fn(gen=g, start_addr=g * banks_apart * geom.bank_stride,
           burst_len=BEATS, txn_count=TXN,
           stride_0=stride, wrap_mask_0=wrap, gap=gap,
           id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8,
           data_mode=True, lfsr_seed=seed, hash_seed0=seed,
           hash_seed1=seed ^ 0x9E37_79B9, hash_seed2=seed ^ 0x85EB_CA6B)


def _phase(drv, which, n_gen, timeout_s):
    """Launch one direction, wait, and return (bandwidth MB/s, cycles, ok).

    The window comes from this engine's own hardware stamps, not timer.cycles:
    the harness timer stops only on wr_done AND rd_done, so in a single-
    direction phase it free-runs or stops on a stale other-direction done.
    """
    drv.clear_stats()
    drv.timer_clear()
    drv.freeze_trace(False)
    mask = (1 << n_gen) - 1
    drv.go(**{f"{which}_mask": mask})
    ok = pc.wait_engine(drv, which, timeout_s=timeout_s, ignore_error=True)
    drv.freeze_trace(True)
    t = drv.timer()
    cyc = max((t.w_last - t.w_first) if which == "wr" else (t.r_last - t.r_first), 0)
    byts = TXN * BEATS * 8 * n_gen
    bw = (byts / (cyc / (CLK_MHZ * 1e6))) / 1e6 if cyc else 0.0
    return bw, cyc, ok


def _point(drv, geom, n_gen, family, gap, timeout_s=60.0):
    """One scenario: write it, then read it back and check every beat."""
    # Per-point seed. Safe because writer and reader cover identical addresses,
    # and valuable because it turns "this region was written by some earlier
    # scenario" from an invisible pass into a mismatch.
    seed = pc._stable_seed(f"{family}|g{n_gen}|gap{gap}|t{TXN}|b{BEATS}")

    drv.freeze_trace(True)
    _program(drv, "wr", geom, n_gen, family, gap, seed)
    wr_bw, _, wr_ok = _phase(drv, "wr", n_gen, timeout_s)

    _program(drv, "rd", geom, n_gen, family, gap, seed)
    rd_bw, _, rd_ok = _phase(drv, "rd", n_gen, timeout_s)

    mism = drv.beats_mismatched()
    drv.freeze_trace(False)
    return wr_bw, rd_bw, mism, (wr_ok and rd_ok)


def _table(title, rows, n_gen, banks):
    print(f"=== {n_gen} generator(s) on banks {banks} -- {title} ===")
    print(f"{'gap':>4} " + " ".join(f"{nm:>18}" for nm, _ in ORDERS))
    print(f"{'':>4} " + " ".join(f"{'MB/s    %peak':>18}" for _ in ORDERS))
    for gap, cells in rows:
        print(f"{gap:>4} " + " ".join(f"{c:>18}" for c in cells))
    print()


def main() -> int:
    drv = DDR2CharDriver(port=dc.autodetect_port(115200, 'auto'))
    st = pm.SimpleTest(drv, base_addr=0, level_cache='host/level_cache.json')
    st.init(do_leveling=True)
    pc.CONFIGS['open_page'].apply(drv)
    geom = pc.DEFAULT_GEOM
    built = drv.sync_gen_config()
    n_built = min(built["num_wr_gen"], built["num_rd_gen"])
    print(f"bitstream: {n_built} generators per direction, {built['num_banks']} "
          f"banks, peak {PEAK_MBS:.0f} MB/s")
    print(f"point: {TXN} x {BEATS*8} B bursts per generator, written then read "
          f"back, own seed\n")

    gens = [n for n in GENS if n <= n_built]
    if not gens:
        raise SystemExit(f"none of GENS={GENS} fit a {n_built}-generator build")

    bad = []
    for n_gen in gens:
        banks = [g * ((1 << geom.bank_width) // n_gen) for g in range(n_gen)]
        wr_rows, rd_rows = [], []
        for gap in GAPS:
            wr_cells, rd_cells = [], []
            for _, fam in ORDERS:
                wr_bw, rd_bw, mism, ok = _point(drv, geom, n_gen, fam, gap)
                flag = "" if (ok and not mism) else ("!" if not ok else f" m{mism}")
                if not ok or mism:
                    bad.append(f"{fam} g{n_gen} gap{gap}"
                               + (" did not complete" if not ok
                                  else f" {mism} beats mismatched"))
                wr_cells.append(f"{wr_bw:7.1f} {wr_bw/PEAK_MBS*100:6.1f}%")
                rd_cells.append(f"{rd_bw:7.1f} {rd_bw/PEAK_MBS*100:6.1f}%{flag}")
            wr_rows.append((gap, wr_cells))
            rd_rows.append((gap, rd_cells))
        _table("WRITE", wr_rows, n_gen, banks)
        _table("READ", rd_rows, n_gen, banks)

    for b in bad:
        print(f"FAIL: {b}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
