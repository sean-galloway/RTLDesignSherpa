# ISSUE-002: jet_monlite drops J7 events under thrash (2-per-cycle queue limit)

**Priority:** P3 (measurement quality, not a functional defect — drops are
reported and counted)
**Status:** OPEN
**Filed:** 2026-11-03, from the first jet Genesys2 perf sweep (T13 step 3).

## Observation

The first silicon sweep of the jet pair rig
(`projects/fpga-systems/Genesys2/cache-ip/jet/results/perf_sweep_20261103T125016Z.json`)
showed nonzero UNEXPECTED tallies scaling with cache thrash. The first-event
latch bank (armed with catch-all `w_prof_miss`) identified the offenders:
**jet_monlite's own drop reports** — agent `0x00A2`, PktTypeError, code `0x09`
(shared `AMBER_EV_DROPPED`), payload = dropped-event data.

Root shape: `jet_monlite` (`rtl/fub/jet_monlite.sv`) has up to 6 candidate
events per cycle (retire, merge, alloc, stall-release, MSHR-occupancy-change,
WB-occupancy-change) but its output queue commits only the **top two** per
cycle and reports the rest as dropped. Under 64–128 KB thrash with
hit-under-miss, alloc+merge+retire coincide often:

| config | transactions | jmon drops |
|---|---|---|
| r16k_we64 | 2×20000 | 18 |
| r64k_we64 | 2×20000 | 600 |
| r64k_we255 | 2×20000 | 444 |
| r128k_we64 | 2×20000 | 157 |
| disjoint64k_we64 | 2×20000 | 609 |

## Implications

- J7 MSHR bins (alloc/merge/retire, profile bins 11–13) **undercount by the
  drop count** on thrash configs — up to ~1.5% of events on r64k_we64. The
  differential-bookkeeping comparisons in the J7 report must either tolerate
  this or read the drop bin (profile bin 17) alongside.
- The host profile and DV profile now carry
  `(_key(0x00A2, 4, 0, 0x09), 17)` so drops land in a named bin instead of
  UNEXPECTED; the sweep prints `jmon_drop=` per config (2026-11-03).

## Possible fixes (becomes a task if scoped)

- Widen the commit width or OUT_DEPTH in `jet_monlite` (cheap: the events are
  already priority-ordered; committing 3–4/cycle covers the realistic
  coincidence set), or
- Coalesce occupancy-change events (they are the lowest-value candidates and
  fire on every alloc/retire edge), or
- Accept the loss and treat bin 17 as the error bar in J7 reporting (current
  state — documented, counted, bounded).

## Evidence

- Latch capture of the first 16 unexpected packets (r64k_we64, armed
  catch-all): all agent `0x00A2` PktTypeError/0x09.
- Sweep JSONs: `results/perf_sweep_20261103T124213Z.json` (unc>0, pre-fix),
  `results/perf_sweep_mshr8_20261103T125016Z.json` (unc=0, jmon_drop named).
