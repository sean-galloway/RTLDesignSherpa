#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board sweep: concurrent read+write, N generators each, one bank apiece.

    1. Write ALL of memory once, then stop.
    2. For each (generators, address order, gap): run N writers and N readers
       AT THE SAME TIME and measure both directions over one window.

Why the prefill is not optional: the readers have to find valid data wherever
their walk takes them, and under concurrency they are not the ones putting it
there. col_major steps across 32 MiB of rows and cacheline marches out of its
starting page, so "the writer just wrote this" is not a property the readers
can rely on. Filling the whole device first makes every address a reader can
reach already correct.

Writers and readers own DISJOINT banks, and that is a correctness requirement
rather than tidiness. A reader sampling an address a writer is mid-burst on
would report a mismatch that is a race in the test, not a defect in the
controller. With eight banks and four of each, every engine gets its own:
writers on 0, 2, 4, 6 and readers on 1, 3, 5, 7. Fewer generators spread the
same way, so the two directions are always interleaved rather than clustered at
opposite ends of the device.

ONE seed for the whole run -- the prefill and every engine after it. The
expected data is a function of address AND seed, so a per-scenario seed would
invalidate the prefill the moment the first reader started. It also makes the
concurrent writers idempotent: they rewrite exactly the bytes already there, so
even a bank-assignment mistake degrades to a redundant write rather than to
corruption that the next point would inherit.

The axes:

  generators  4, 3, 2, 1 PER DIRECTION -- so 4 means eight engines running.
  gap         0..15 idle clocks between bursts, applied to both directions.
  order       cacheline  contiguous march. Crosses pages and banks the way a
                         cache-line-filling master does. Best case.
              row-major  wrapped inside one page: every burst a page HIT.
              col-major  same column of the next row in the same bank: every
                         burst a page MISS.

The gap is 0..15, not 0..16: chargen_regs' gap field is four bits
(blen_txn.gap[27:24]). Programming 16 would write 0 and silently measure the
back-to-back case twice, so the range stops at 15 and says so here.

    PUMICE_MC_CLK_HZ=75000000 python3 bin/bank_gap_sweep.py     # from build-perf/
    GAPS=0,4,8,15 GENS=4,1 python3 bin/bank_gap_sweep.py
    TXN=20000 python3 bin/bank_gap_sweep.py                     # wider spans
"""
import json
import os
import sys

sys.path.insert(0, 'host')
import ddr2_char as dc
from ddr2_char import DDR2CharDriver
import pumice_master as pm
import pumice_char as pc

CLK_MHZ  = float(os.environ.get("PUMICE_MC_CLK_HZ", "75000000")) / 1e6
PEAK_MBS = 8 * CLK_MHZ                      # 8 bytes/beat at one beat/cycle

# One seed for the prefill and every engine after it. See the module docstring.
SEED = 0x5EED_0B01

# Named gap sweeps, borrowed from the STREAM runner's DELAY_SWEEPS: a sweep you
# cannot name is a sweep you cannot repeat. GAPS takes a name OR a literal list,
# and an unknown NAME raises rather than falling back -- a typo must not
# silently measure a different curve than the one that was asked for.
GAP_SWEEPS = {
    "full":  list(range(16)),          # every gap the 4-bit field can express
    "knee":  [0, 1, 2, 3, 4, 6, 8, 12, 15],
    "ends":  [0, 15],                  # smoke: back-to-back and maximum idle
}


def resolve_gaps(spec):
    if spec in GAP_SWEEPS:
        return list(GAP_SWEEPS[spec])
    if "," in spec or spec.strip().isdigit():
        return [int(x, 0) for x in spec.split(",") if x.strip()]
    raise SystemExit(f"unknown gap sweep {spec!r}; known names: "
                     f"{', '.join(sorted(GAP_SWEEPS))} (or a literal list)")


GAPS  = resolve_gaps(os.environ.get("GAPS", "full"))
JSON_OUT = os.environ.get("JSON_OUT", "reports/bank_gap_sweep.json")
GENS  = [int(x) for x in os.environ.get("GENS", "4,3,2,1").split(",")]
TXN   = int(os.environ.get("TXN", "2000"))
BEATS = int(os.environ.get("BEATS", "8"))   # 8 beats x 8 B = 64 B bursts

ORDERS = [
    ("cacheline", pc.FAM_INCREMENTAL),
    ("row_major", pc.FAM_ROW_MAJOR),
    ("col_major", pc.FAM_COL_MAJOR),
]

# Prefill burst: 128 beats = 1 KiB, so one generator's share of a 128 MiB
# device needs 32768 bursts at four generators -- inside the 16-bit txn_count.
FILL_BEATS = 128
FILL_BYTES = FILL_BEATS * 8

if TXN > pc.TXN_MAX:
    raise SystemExit(f"TXN={TXN} exceeds the 16-bit txn_count field ({pc.TXN_MAX})")


def _seed_kw(seed):
    return dict(data_mode=True, lfsr_seed=seed, hash_seed0=seed,
                hash_seed1=seed ^ 0x9E37_79B9, hash_seed2=seed ^ 0x85EB_CA6B)


def _prefill(drv, geom, n_gen, timeout_s=120.0):
    """Write the whole device once, with n_gen writers side by side.

    Split into passes when one writer's share needs more bursts than the
    16-bit txn_count holds -- 64 MiB at 1 KiB/burst is 65536, one over. The
    passes cover the share EXACTLY: rounding up would walk a writer past the
    top of the device, where the DRAM wraps physically but the address hash
    does not, and every later read of that region would report a mismatch that
    is this arithmetic rather than the DRAM.
    """
    span = geom.device_bytes
    per = span // n_gen
    total = per // FILL_BYTES
    tail = span - total * FILL_BYTES * n_gen
    if tail:
        print(f"[prefill] WARNING: {n_gen} writers leave {tail} B at the top of "
              f"the device unwritten; a col_major read that wraps into it will "
              f"report a mismatch that is this, not the DRAM.")
    passes = -(-total // pc.TXN_MAX)
    base_txn, extra = divmod(total, passes)
    print(f"[prefill] {span/(1<<20):.0f} MiB, {n_gen} writers, {passes} pass(es), "
          f"seed 0x{SEED:08X}")

    ok, cycles, done = True, 0, 0
    for p in range(passes):
        txn = base_txn + (1 if p < extra else 0)
        drv.freeze_trace(True)
        for g in range(n_gen):
            drv.program_wr_engine(
                gen=g, start_addr=g * per + done * FILL_BYTES,
                burst_len=FILL_BEATS, txn_count=txn,
                stride_0=FILL_BYTES, wrap_mask_0=0, gap=0,
                id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8, **_seed_kw(SEED))
        drv.clear_stats()
        drv.timer_clear()
        drv.freeze_trace(False)
        drv.go(wr_mask=(1 << n_gen) - 1)
        if not pc.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True):
            ok = False
        drv.freeze_trace(True)
        t = drv.timer()
        cycles += max(t.w_last - t.w_first, 0)
        done += txn

    bw = (span / (cycles / (CLK_MHZ * 1e6))) / 1e6 if cycles else 0.0
    print(f"[prefill] {'done' if ok else 'DID NOT COMPLETE'} in {cycles} cycles "
          f"({bw:.1f} MB/s)\n")
    return ok


def _banks(geom, n_gen):
    """Disjoint bank for every engine: writers even slots, readers odd.

    Interleaved rather than clustered, so the two directions contend the way
    they would in a real mix instead of sitting at opposite ends of the part.
    """
    nb = 1 << geom.bank_width
    step = max(nb // (2 * n_gen), 1)
    wr = [(2 * g) * step for g in range(n_gen)]
    rd = [(2 * g + 1) * step for g in range(n_gen)]
    return wr, rd


def _point(drv, geom, n_gen, family, gap, timeout_s=60.0):
    """N writers and N readers, concurrent, one window."""
    sc = pc.Scenario(name=f"{family}_g{n_gen}_gap{gap}", family=family,
                     burst_len=BEATS, txn_count=TXN, gap=gap)
    stride, wrap = pc.strides_for(sc, geom)
    wr_banks, rd_banks = _banks(geom, n_gen)
    common = dict(burst_len=BEATS, txn_count=TXN, stride_0=stride,
                  wrap_mask_0=wrap, gap=gap, id_mode=dc.ID_MODE_FIXED,
                  axi_size=dc.AXI_SIZE_8, **_seed_kw(SEED))

    drv.freeze_trace(True)
    for g in range(n_gen):
        drv.program_wr_engine(gen=g, start_addr=wr_banks[g] * geom.bank_stride,
                              **common)
        drv.program_rd_engine(gen=g, start_addr=rd_banks[g] * geom.bank_stride,
                              **common)
    drv.clear_stats()
    drv.timer_clear()
    drv.freeze_trace(False)
    mask = (1 << n_gen) - 1
    drv.start_both(wr_mask=mask, rd_mask=mask)
    wr_ok = pc.wait_engine(drv, "wr", timeout_s=timeout_s, ignore_error=True)
    rd_ok = pc.wait_engine(drv, "rd", timeout_s=timeout_s, ignore_error=True)
    drv.freeze_trace(True)

    t = drv.timer()
    # Each direction on its OWN window, and the bus on the shared one.
    #
    # In theory both directions move the same bytes and finish together, so
    # wr and rd should print the same number -- but that is the theory this
    # test exists to check, so both are measured and both are printed. If they
    # differ, one direction was starved while the other ran, and that is a
    # result rather than a rounding artifact.
    wr_cyc = max(t.w_last - t.w_first, 0)
    rd_cyc = max(t.r_last - t.r_first, 0)
    window = max(max(t.w_last, t.r_last) - min(t.w_first, t.r_first), 0)
    byts = TXN * BEATS * 8 * n_gen          # per direction

    def _mbs(nbytes, cycles):
        return (nbytes / (cycles / (CLK_MHZ * 1e6))) / 1e6 if cycles else 0.0

    wr_bw  = _mbs(byts, wr_cyc)
    rd_bw  = _mbs(byts, rd_cyc)
    bus_bw = _mbs(2 * byts, window)

    # The read histogram counts transactions the bus actually returned. If it
    # disagrees with what was programmed, the MB/s above are computed from
    # bytes that did not move and the number is fiction, not a measurement.
    _, rd_txn = drv.perf_hist_dump(dc.HIST_BUS_RD, dc.HIST_METRIC_0)
    want_txn = TXN * n_gen
    mism = drv.beats_mismatched()

    # Four-bucket cycle classification per direction. This is what turns a
    # bandwidth shortfall into a named cause instead of a number: rising
    # STARVATION means the generators stopped asking (the gap did it), rising
    # BACKPRESSURE means the controller stopped accepting (the DRAM did it).
    # Raw counts sit beside the fractions so nothing downstream has to
    # re-derive a ratio, or trust one it cannot rebuild.
    meters = {d: pc._read_meter(drv, d) for d in ("wr", "rd")}
    drv.freeze_trace(False)

    def _buckets(m):
        t = m.total
        return dict(productive=m.prod, backpressure=m.bp, starvation=m.starv,
                    idle=m.idle, total=t,
                    productive_frac=(m.prod / t) if t else 0.0,
                    backpressure_frac=(m.bp / t) if t else 0.0,
                    starvation_frac=(m.starv / t) if t else 0.0,
                    idle_frac=(m.idle / t) if t else 0.0)

    return dict(
        order=family, n_gen=n_gen, gap=gap, txn=TXN, beats=BEATS,
        wr=wr_bw, rd=rd_bw, bus=bus_bw,
        # Both windows, so a disagreement between the counters and the
        # hardware stamps is visible rather than averaged away.
        wr_cycles=wr_cyc, rd_cycles=rd_cyc, window_cycles=window,
        bytes_per_direction=byts,
        # Ceiling stored per record, so a plot never re-derives it and it
        # cannot drift from the clock this run actually used.
        peak_mb_s=PEAK_MBS,
        mism=mism, ok=(wr_ok and rd_ok), rd_txn=rd_txn, want_txn=want_txn,
        buckets={d: _buckets(m) for d, m in meters.items()},
    )


SPARK = " .:-=+*#@"


def _spark(vals, lo, hi):
    """One character per gap, so the shape of a curve is visible at a glance."""
    if hi <= lo:
        return SPARK[-1] * len(vals)
    span = len(SPARK) - 1
    return "".join(SPARK[max(0, min(span, round((v - lo) / (hi - lo) * span)))]
                   for v in vals)


def _knee(gaps, vals, tol=0.03):
    """Largest gap whose bandwidth is still within `tol` of the gap-0 value.

    That is the bend: how much idle the controller absorbs before the
    generators become the limit. A high knee means the controller had slack
    at gap 0 -- it was not the bottleneck. A knee of 0 means every clock of
    injected idle cost bandwidth immediately, so it was.
    """
    if not vals or vals[0] <= 0:
        return None
    ref = vals[0]
    best = gaps[0]
    for g, v in zip(gaps, vals):
        if v >= ref * (1.0 - tol):
            best = g
        else:
            break
    return best


def _curve_table(curves):
    """One ROW per curve, gap across -- so a bend reads left to right."""
    print(f"{'MB/s by gap:':>20}" + "".join(f"{g:>5}" for g in GAPS)
          + f"{'shape':>18}{'knee':>6}")
    for name, _ in ORDERS:
        for series in ("wr", "rd", "bus"):
            vals = [curves[(name, series)][g] for g in GAPS]
            lo, hi = min(vals), max(vals)
            k = _knee(GAPS, vals)
            print(f"{name + ' ' + series:>20}"
                  + "".join(f"{v:>5.0f}" for v in vals)
                  + f"  {_spark(vals, lo, hi):>16}"
                  + (f"{k:>6}" if k is not None else f"{'-':>6}"))
        print()


def main() -> int:
    drv = DDR2CharDriver(port=dc.autodetect_port(115200, 'auto'))
    st = pm.SimpleTest(drv, base_addr=0, level_cache='host/level_cache.json')
    st.init(do_leveling=True)
    pc.CONFIGS['open_page'].apply(drv)
    geom = pc.DEFAULT_GEOM
    built = drv.sync_gen_config()
    n_built = min(built["num_wr_gen"], built["num_rd_gen"])
    nb = built["num_banks"]
    print(f"bitstream: {n_built} generators per direction, {nb} banks, "
          f"peak {PEAK_MBS:.0f} MB/s")
    print(f"point: {TXN} x {BEATS*8} B bursts per engine, read and write "
          f"concurrent, seed 0x{SEED:08X}\n")

    gens = [n for n in GENS if n <= n_built]
    if not gens:
        raise SystemExit(f"none of GENS={GENS} fit a {n_built}-generator build")
    if 2 * max(gens) > nb:
        raise SystemExit(
            f"{max(gens)} writers + {max(gens)} readers need {2*max(gens)} "
            f"disjoint banks but the device has {nb}; lower GENS.")

    if not _prefill(drv, geom, n_built):
        print("prefill did not complete -- reads below would be measured "
              "against an incomplete image; stopping.")
        return 1

    bad, records = [], []
    for n_gen in gens:
        wr_banks, rd_banks = _banks(geom, n_gen)
        print(f"=== {n_gen}+{n_gen} concurrent -- writers on banks {wr_banks}, "
              f"readers on {rd_banks} ===")
        curves = {}
        for name, fam in ORDERS:
            for gap in GAPS:
                r = _point(drv, geom, n_gen, fam, gap)
                records.append(r)
                for series in ("wr", "rd", "bus"):
                    curves.setdefault((name, series), {})[gap] = r[series]
                if not r["ok"]:
                    bad.append(f"{fam} g{n_gen} gap{gap} did not complete")
                if r["mism"]:
                    bad.append(f"{fam} g{n_gen} gap{gap}: {r['mism']} beats mismatched")
                if r["rd_txn"] != r["want_txn"]:
                    bad.append(f"{fam} g{n_gen} gap{gap}: bus returned "
                               f"{r['rd_txn']} read txns, programmed "
                               f"{r['want_txn']} -- the MB/s for this point is "
                               f"computed from bytes that did not move")
        _curve_table(curves)

    # Durable records. A sweep that only prints is a sweep whose numbers die
    # with the terminal: the plots, the report and any later comparison all
    # read this file, not the scrollback.
    if JSON_OUT:
        os.makedirs(os.path.dirname(JSON_OUT) or ".", exist_ok=True)
        with open(JSON_OUT, "w") as f:
            json.dump(records, f, indent=2, default=str)
        print(f"wrote {len(records)} records -> {JSON_OUT}")
        print(f"plot them: python3 bin/plot_bank_gap.py {JSON_OUT}")

    for b in bad:
        print(f"FAIL: {b}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
