#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board sweep: N generators on N DIFFERENT banks, against gap and address order.

Shape of the experiment:

  1. Fill the WHOLE device once, then stop. Every later phase is read-only, so
     the numbers describe the read path against a known memory image instead of
     a write and a read fighting each other.
  2. Give each generator its own bank. With four generators on an eight-bank
     part they land on banks 0, 2, 4, 6 -- spread rather than adjacent, so a
     bank-group effect shows up as a pattern rather than as a single cliff.
  3. Sweep the inter-burst gap 0..15 clocks. Zero is back-to-back; the top of
     the range is idle enough that the controller should be able to close and
     re-open pages without costing bandwidth. Where the curve flattens is where
     the generators stop being the limit.
  4. Sweep the address order: cacheline, row-major, column-major.
  5. Repeat the whole thing at 4, 3, 2 and 1 generators, so the bank-parallel
     gain is measured rather than assumed.

The gap is 0..15, not 0..16: chargen_regs' gap field is four bits
(blen_txn.gap[27:24]). Asking for 16 would program 0 and quietly measure the
back-to-back case a second time, so the sweep stops at 15 and says so here.

The three address orders, and what each is for:

  cacheline   contiguous march, one burst after another. Crosses pages and
              banks the way a cache-line-filling master does. Best case.
  row-major   wrapped inside one page, so every burst is a page HIT. Isolates
              the column-access rate from any activate cost.
  col-major   same column of the next row in the same bank, so every burst is
              a page MISS. Isolates activate/precharge.

One seed for the entire run, not one per scenario. The expected data is a
function of address AND seed, so a per-scenario seed would invalidate the fill
the moment the first read scenario started. That is the whole reason
pumice_char.measure()'s write-then-read-per-scenario flow is not reused here.

    PUMICE_MC_CLK_HZ=75000000 python3 bin/bank_gap_sweep.py     # from build-perf/
    GAPS=0,4,8,15 GENS=4,1 python3 bin/bank_gap_sweep.py
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

# One seed for the fill and every read after it. See the module docstring.
SEED = 0x5EED_0B01

GAPS = [int(x) for x in os.environ.get("GAPS", ",".join(str(g) for g in range(16))).split(",")]
GENS = [int(x) for x in os.environ.get("GENS", "4,3,2,1").split(",")]
ORDERS = [
    ("cacheline", pc.FAM_INCREMENTAL),
    ("row_major", pc.FAM_ROW_MAJOR),
    ("col_major", pc.FAM_COL_MAJOR),
]

# Fill: 128 beats/burst = 1 KiB, so a 16-bit txn_count reaches 64 MiB per
# generator and the whole 128 MiB device fits in two generators' worth. Using
# all four keeps each one inside its own quarter.
FILL_BURST_BEATS = 128
FILL_BURST_BYTES = FILL_BURST_BEATS * 8

# Measurement: short bursts, because the point is the gap and the bank, not the
# burst-length curve -- axlen_sweep.py owns that axis.
MEAS_BURST_BEATS = 8
MEAS_TXN         = 2000


def _fill_all(drv, geom, n_gen, timeout_s):
    """Write the whole device once, with n_gen generators side by side.

    Split into passes when one generator's share needs more bursts than the
    16-bit txn_count can express -- 64 MiB at 1 KiB/burst is already 65536,
    one over. The passes are sized to cover the share EXACTLY: rounding up and
    letting the last pass overrun would walk a generator past the top of the
    device, where the DRAM wraps physically but the address hash does not, and
    every read of that region would then report a mismatch that is an artifact
    rather than corruption.
    """
    span = geom.device_bytes
    per  = span // n_gen
    total = per // FILL_BURST_BYTES
    # A generator count that does not divide the device into whole bursts
    # leaves a tail unwritten, and col_major wraps at the device boundary --
    # so a later read of that tail reports a mismatch that is an artifact of
    # the fill, not corruption. Powers of two always divide cleanly; say so
    # loudly for anything else rather than letting it look like a defect.
    tail = span - total * FILL_BURST_BYTES * n_gen
    if tail:
        print(f"[fill] WARNING: {n_gen} generators leave {tail} B at the top of "
              f"the device unwritten ({span} is not a whole number of "
              f"{FILL_BURST_BYTES} B bursts x {n_gen}). A col_major read that "
              f"wraps into that tail will report a mismatch that is this, not "
              f"the DRAM.")
    passes = -(-total // pc.TXN_MAX)                 # ceil
    base_txn, extra = divmod(total, passes)
    print(f"[fill] {span/(1<<20):.0f} MiB with {n_gen} generator(s), "
          f"{passes} pass(es) of <={base_txn + (1 if extra else 0)} x "
          f"{FILL_BURST_BYTES}B each, seed 0x{SEED:08X}")

    ok = True
    cyc_total = 0
    done = 0
    for p in range(passes):
        txn = base_txn + (1 if p < extra else 0)      # exact cover, no overrun
        drv.freeze_trace(True)
        for g in range(n_gen):
            drv.program_wr_engine(
                gen=g, start_addr=g * per + done * FILL_BURST_BYTES,
                burst_len=FILL_BURST_BEATS, txn_count=txn,
                stride_0=FILL_BURST_BYTES, wrap_mask_0=0,
                gap=0, id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8,
                data_mode=True, lfsr_seed=SEED, hash_seed0=SEED,
                hash_seed1=SEED ^ 0x9E37_79B9, hash_seed2=SEED ^ 0x85EB_CA6B)
        drv.clear_stats()
        drv.timer_clear()
        drv.freeze_trace(False)
        drv.go(wr_mask=(1 << n_gen) - 1)
        if not pc.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True):
            ok = False
        drv.freeze_trace(True)
        t = drv.timer()
        cyc_total += max(t.w_last - t.w_first, 0)
        done += txn

    bw = (span / (cyc_total / (CLK_MHZ * 1e6))) / 1e6 if cyc_total else 0.0
    print(f"[fill] {'done' if ok else 'DID NOT COMPLETE'} in {cyc_total} cycles "
          f"({bw:.1f} MB/s)\n")
    return ok


def _read_phase(drv, geom, n_gen, family, gap, timeout_s):
    """Read-only measurement: n_gen readers, one per bank, at this gap."""
    banks_apart = (1 << geom.bank_width) // n_gen      # spread, not adjacent
    sc = pc.Scenario(name=f"{family}_g{n_gen}_gap{gap}", family=family,
                     burst_len=MEAS_BURST_BEATS, txn_count=MEAS_TXN, gap=gap)
    stride, wrap = pc.strides_for(sc, geom)

    drv.freeze_trace(True)
    for g in range(n_gen):
        drv.program_rd_engine(
            gen=g, start_addr=g * banks_apart * geom.bank_stride,
            burst_len=MEAS_BURST_BEATS, txn_count=MEAS_TXN,
            stride_0=stride, wrap_mask_0=wrap, gap=gap,
            id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8,
            data_mode=True, lfsr_seed=SEED, hash_seed0=SEED,
            hash_seed1=SEED ^ 0x9E37_79B9, hash_seed2=SEED ^ 0x85EB_CA6B)
    drv.clear_stats()
    drv.timer_clear()
    drv.freeze_trace(False)
    drv.go(rd_mask=(1 << n_gen) - 1)
    ok = pc.wait_engine(drv, "rd", timeout_s=timeout_s, ignore_error=True)
    drv.freeze_trace(True)
    t = drv.timer()
    cyc = max(t.r_last - t.r_first, 0)
    mism = drv.beats_mismatched()
    drv.freeze_trace(False)

    beats = MEAS_TXN * MEAS_BURST_BEATS * n_gen
    bw = (beats * 8 / (cyc / (CLK_MHZ * 1e6))) / 1e6 if cyc else 0.0
    return bw, cyc, mism, ok


def main() -> int:
    drv = DDR2CharDriver(port=dc.autodetect_port(115200, 'auto'))
    st = pm.SimpleTest(drv, base_addr=0, level_cache='host/level_cache.json')
    st.init(do_leveling=True)
    pc.CONFIGS['open_page'].apply(drv)
    geom = pc.DEFAULT_GEOM
    built = drv.sync_gen_config()
    n_built = min(built["num_wr_gen"], built["num_rd_gen"])
    print(f"bitstream: {n_built} generators per direction, "
          f"{built['num_banks']} banks, peak {PEAK_MBS:.0f} MB/s\n")

    gens = [n for n in GENS if n <= n_built]
    if not gens:
        raise SystemExit(f"none of GENS={GENS} fit a {n_built}-generator build")

    # Fill once, with everything the bitstream has.
    if not _fill_all(drv, geom, n_built, timeout_s=120.0):
        print("fill did not complete -- the read numbers below would be "
              "measured against an incomplete image; stopping.")
        return 1

    bad = 0
    for n_gen in gens:
        banks = [g * ((1 << geom.bank_width) // n_gen) for g in range(n_gen)]
        print(f"=== {n_gen} generator(s) on banks {banks} ===")
        print(f"{'gap':>4} " + " ".join(f"{nm:>22}" for nm, _ in ORDERS))
        print(f"{'':>4} " + " ".join(f"{'MB/s   %peak  mism':>22}" for _ in ORDERS))
        for gap in GAPS:
            cells = []
            for _, fam in ORDERS:
                bw, cyc, mism, ok = _read_phase(drv, geom, n_gen, fam, gap,
                                                timeout_s=60.0)
                if not ok or mism:
                    bad += 1
                cells.append(f"{bw:7.1f} {bw/PEAK_MBS*100:5.1f}% {mism:6d}"
                             + ("" if ok else "!"))
            print(f"{gap:>4} " + " ".join(f"{c:>22}" for c in cells))
        print()

    if bad:
        print(f"{bad} measurement(s) reported a mismatch or did not complete.")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
