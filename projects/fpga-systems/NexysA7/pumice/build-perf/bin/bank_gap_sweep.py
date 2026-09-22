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

Writers and readers START on disjoint banks: writers on 0, 2, 4, 6 and readers
on 1, 3, 5, 7, interleaved rather than clustered at opposite ends of the
device. Fewer generators spread the same way.

Read that as disjoint STARTING banks and nothing more. Only col_major stays in
its bank; cacheline and row_major march out of it, and a cacheline point at
board scale covers 250 KiB -- every bank, many times over. So the engines DO
overlap in address, deliberately, and the design that makes this safe is not
the bank assignment but the data function: every value is a pure hash of its
own address under one run-wide seed, so a writer rewrites exactly the bytes
already there and a reader is right to expect them no matter who wrote them
last. A reader sampling an address a writer is mid-burst on is therefore not a
race -- both agree on the value.

That distinction is load-bearing. The 2026-09-14 investigation of PUMICE-037
spent a pass on the theory that overlap explained the mismatches; it does not,
and the proof is that the 4+4 point has maximum overlap and stays clean while
the 1+1 point has the least and does not.

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

# Re-fill the device before EVERY point, not once for the run.
#
# Points are not independent otherwise, and that is not a theory: a concurrent
# read+write point with the reader gap at 8 or above leaves genuinely wrong
# data in cells (2026-09-14, PUMICE-037). Every later point then reads that
# damage and reports it as its own mismatch -- which is exactly what made the
# first full run unreadable, where row_major g1 reported an identical 3694
# mismatched beats at eight consecutive gaps. Those 3694 were the *previous*
# family's damage, re-read eight times; the point itself was clean.
#
# The fill is ~0.27 s of DRAM time, so paying it per point is cheap next to
# mistaking stale damage for a measurement. PREFILL=once restores the old
# behaviour for a deliberate damage-accumulation experiment -- do not use it
# to go faster.
PREFILL_MODE = os.environ.get("PREFILL", "point").lower()
if PREFILL_MODE not in ("point", "once"):
    raise SystemExit(f"PREFILL={PREFILL_MODE!r}: expected 'point' or 'once'")

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


def _buckets(m, window):
    """Counts as measured, fractions against the HARDWARE window.

    The meter free-runs from clear_stats() until it is read, so m.total
    spans the host's UART chatter as well as the transfer -- 7.2M cycles
    against a 16.7k-cycle window on a 1+1 point, 430x. Dividing by m.total
    made a point moving 95% of peak report "0.2% productive, 99.8%
    starvation" (2026-09-14). The counts are right -- productive lands on
    exactly the beats moved -- so only the denominator needed fixing.

    m.starv is NOT re-exported as a fraction: it absorbs all the host idle
    and carries no information about the run. What is left after
    productive, backpressure and idle is reported as `other_frac`.
    """
    w = window or m.total
    f = (lambda v: (v / w) if w else 0.0)
    prod, bp, idle = f(m.prod), f(m.bp), f(m.idle)
    return dict(productive=m.prod, backpressure=m.bp, starvation=m.starv,
                idle=m.idle, total=m.total, window=w,
                productive_frac=prod, backpressure_frac=bp,
                idle_frac=idle,
                other_frac=max(0.0, 1.0 - prod - bp - idle))


def _point(drv, geom, n_gen, family, gap, timeout_s=60.0):
    """N writers and N readers, concurrent, one window.

    Measurement is pumice_char.measure_concurrent -- the SAME call the char
    suite and the wr_batch sequence use, with placement="banks" for the
    disjoint even/odd bank layout this sweep needs. It used to program the
    engines, start them, read the timer and classify the meters itself, a
    second implementation of that function; the two then disagreed on
    identical workloads (1+1 concurrent read clean through measure_concurrent
    and "prefill did not complete" through here, 2026-09-21). One measurement,
    one prefill, one set of counters. What stays local is this script's own
    reporting: the bucket fractions, the knee finder and the plot.
    """
    sc = pc.Scenario(name=f"{family}_g{n_gen}_gap{gap}", family=family,
                     burst_len=BEATS, txn_count=TXN, gap=gap,
                     id_mode=dc.ID_MODE_FIXED, axi_size=dc.AXI_SIZE_8)
    r = pc.measure_concurrent(drv, sc, cfg=CFG, geom=geom, n_wr=n_gen,
                              n_rd=n_gen, clk_mhz=CLK_MHZ,
                              timeout_s=timeout_s, placement="banks")

    wr_cyc = r.wr_window_cyc or r.wr_cycles
    rd_cyc = r.rd_window_cyc or r.rd_cycles
    window = r.rd_cycles                      # shared window, both directions
    byts   = r.bytes_moved

    def _mbs(nbytes, cycles):
        return (nbytes / (cycles / (CLK_MHZ * 1e6))) / 1e6 if cycles else 0.0

    try:
        stray = sum(drv.stray_beats(g) for g in range(n_gen))
    except Exception:                                          # noqa: BLE001
        stray = 0
    meters = {"wr": r.wr_meter, "rd": r.rd_meter}
    return dict(
        order=family, n_gen=n_gen, gap=gap, txn=TXN, beats=BEATS,
        wr=_mbs(r.wr_bytes or byts, wr_cyc), rd=_mbs(byts, rd_cyc),
        bus=_mbs((r.wr_bytes or byts) + byts, window),
        wr_cycles=wr_cyc, rd_cycles=rd_cyc, window_cycles=window,
        bytes_per_direction=byts,
        peak_mb_s=PEAK_MBS,
        mism=r.mismatched, stray=stray, ok=r.ok,
        rd_txn=r.rd_hist_total, want_txn=TXN * n_gen,
        notes=r.notes,
        buckets={d: _buckets(m, wr_cyc if d == "wr" else rd_cyc)
                 for d, m in meters.items()},
    )


# The controller config for the whole sweep; _point passes it to
# measure_concurrent so the library applies it exactly once.
CFG = pc.CONFIGS['open_page']

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
    CFG.apply(drv)
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

    # NO separate prefill pass. measure_concurrent pre-fills each reader's own
    # region as an untimed step inside the point, against the same address-hash
    # data mode the reader validates with -- so every point is independent by
    # construction and there is nothing to keep in sync. The script's private
    # _prefill() filled the WHOLE device up front against its own bank layout;
    # it is what reported "prefill did not complete" for every 1+1 and 2+2
    # point on 2026-09-21 while the identical workload ran clean through the
    # library path in wr_batch.

    bad, records = [], []
    for n_gen in gens:
        # Placement is measure_concurrent's now (placement="banks"): writers on
        # even bank slots, readers on odd, one bank each.
        print(f"=== {n_gen}+{n_gen} concurrent -- disjoint banks, "
              f"writers even slots / readers odd ===")
        curves = {}
        for name, fam in ORDERS:
            for gap in GAPS:
                r = _point(drv, geom, n_gen, fam, gap)
                r["prefill_mode"] = "per-point (measure_concurrent)"
                records.append(r)
                for series in ("wr", "rd", "bus"):
                    curves.setdefault((name, series), {})[gap] = r[series]
                if not r["ok"]:
                    bad.append(f"{fam} g{n_gen} gap{gap} did not complete")
                if r["mism"]:
                    bad.append(f"{fam} g{n_gen} gap{gap}: {r['mism']} beats "
                               f"mismatched, {r['stray']} stray")
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
