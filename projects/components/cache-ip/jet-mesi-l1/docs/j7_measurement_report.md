<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← jet README](../README.md)**

# J7: the non-blocking delta, measured on silicon

**Status: SILICON DATA COMPLETE (amber + jet MSHR ∈ {2, 4, 8, 16})** — all
rigs swept on the Genesys 2 on 2026-11-03 (`results/perf_sweep_20261103T125952Z.json`
in the amber area, `results/perf_sweep_mshr{2,4,8,16}_*.json` in the jet
area). The grid is flat — the rig tops out at 2 outstanding misses
(see metric 2) — so amber's MSHR=1 column and jet's MSHR=2 column bracket
the whole reachable range.

J7 is the PRD's measurement success criterion: quantify what the MSHRs buy
over amber's blocking pipeline, with MonBus evidence, on identical stimulus.

## Method

- **Rigs.** amber pair rig (`fpga-systems/Genesys2/cache-ip/amber/`, 100 MHz
  since 2026-11-03 — `61a0f476e`; the sweeps quoted here were taken at its
  earlier 90 MHz clock)
  and jet pair rig (`fpga-systems/Genesys2/cache-ip/jet/`, 60 MHz before
  ISSUE-001). All J7 metrics are **cycle counts and event rates**, so the
  clock difference does not enter the comparison; wall-clock columns are
  diagnostic only.
- **Stimulus.** Identical injector configurations on both rigs: the
  `amber_perf_sweep` config matrix (working set 64 B … 128 KB × write mix ×
  shared/disjoint) at fixed seeds (`0x12345678` / `0xDEADBEEF`), with
  `count` large enough that hit/miss rates stabilize (sweep default).
  Determinism is by construction (LFSR injectors); amber and jet see the
  same address/data streams per config. **Deviation from the plan's "frozen
  trace corpus", recorded:** the injector has no trace-replay mode, so
  "identical traces" is realized as identical seeded LFSR streams; the
  cache_sim concurrency model is the cross-check against the corpus (plan
  step 3 allows the cross-check-or-documented-gap reading). If trace replay
  is later wanted, it is an injector feature, not a rig change.
- **Measurement window.** Per run: settle → freeze → read → clear
  (formal/amber TASK-001 protocol). Latency stats come from the injector
  CSRs (min/max/sum, log2 histogram, run cycles); event rates from the
  MonBus tally bins; both are read per config, per rig.
- **MSHR grid.** jet is built at `MSHR_COUNT ∈ {2, 4, 8, 16}`
  (`MSHR_COUNT=<n> make -C build-bringup bitstream` — the Vivado generic is
  wired in `fpga/tcl/create_project.tcl`); amber is the degenerate
  `MSHR_COUNT=1` column. `VICTIM_DEPTH=2` fixed for v1.
- **Cross-check.** The cache_sim concurrency model
  (`bin/apps/cache_sim/js/model.js`) predicts the jet occupancy/merge
  behaviour for the same traces; where the model lacks a concurrency
  feature the gap is documented rather than fudged.

## Headline (2026-11-03 silicon)

Identical seeded stimulus, 2×20000 transactions per run, injector-reported
run cycles (ci0; ci1 within 0.5% everywhere). jet columns: pre-ISSUE-001 and
post-step-0 (registered coh sideband), both at the committed 60 MHz rig
clock — the "+coh_reg" sideband register costs ~3% on thrash configs (one
extra cycle of snoop-issue latency) and nothing on the all-hit config.
(The "100 MHz" figure quoted earlier on 2026-11-03 was a mislabeled 60 MHz
build — the Makefile clock knobs were vestigial; the clock lives in the RTL
parameters. Cycle counts are clock-independent, so the data stands.)

| config | amber 90 MHz cyc | jet 60 MHz cyc | jet 60 MHz +coh_reg cyc | delta |
| --- | --- | --- | --- | --- |
| smoke4k_we64 (all-hit) | 121616 | 100621 | 100494 | **−17.4%** |
| r64k_we64 | 466833 | 389438 | 401763 | **−13.9%** |
| r64k_we255 (write storm) | 677491 | 464335 | 476278 | **−29.7%** |
| r128k_we64 | 612753 | 512157 | 528278 | −13.8% |
| disjoint64k_we64 | 468601 | 391885 | 402042 | −14.2% |

(The serve-pend v2 step adds one more hit-latency cycle; its sweep numbers
land with the v3 measurement pass.)

(2026-11-10: the v3 lookup split and the BRAM sync-read array had taken the
hit to 6 cycles in the FPGA review bins; jet TASK-003 brought it back to 3
-- data-array address lead, transparent empty request skid, response-ring
head-deposit bypass -- with every sweep CRC unchanged. The tables below
stand as measured; bin 16's resident configs are within 144 cycles of them.)

Hit latency is 3 cycles on jet vs 4 on amber (pipeline depth), which already
accounts for the all-hit row; the thrash rows add the non-blocking overlap.
Fill counts match across rigs (e.g. r64k_we64: jet 21710 vs amber 22085
`fill_end`) — same misses, served faster; the per-rig "miss" bins use
different event semantics (see metric 1 note) and are **not** comparable.

## The four metrics (jet MAS ch04 §metrics)

Latencies are quoted **load-to-use**: request accept → data usable
(the §9.10.3 rule), which is exactly the injector's accept→response count.

### 1. Hit-latency distribution under a miss stream

The J6 claim: hits proceed while misses are in flight. Per config:
latency histograms (8 log2 buckets, bucket *b* = [2^b, 2^(b+1)−1] cycles)
for jet vs amber at the same working set; the separation at 4 KB shared
(heavy snoop + miss traffic) is the headline cell.

ci0 accept→response (load-to-use), count=20000. Means are `lat_sum/count`.

| config | rig | min | mean | max | hist (b0..b7) |
| --- | --- | --- | --- | --- | --- |
| smoke4k_we64 | amber | 4 | 4.08 | 29 | 0, 0, 19935, 0, 65, 0, 0, 0 |
| smoke4k_we64 | jet MSHR=8 | 3 | 3.03 | 41 | 0, 19983, 0, 0, 1, 16, 0, 0 |
| r64k_we64 | amber | 4 | 21.34 | 60 | 0, 0, 8909, 0, 8399, 2692, 0, 0 |
| r64k_we64 | jet MSHR=8 | 3 | 17.47 | 41 | 0, 8958, 0, 0, 8343, 2699, 0, 0 |
| r64k_we255 | amber | 4 | 31.87 | 60 | 0, 0, 8786, 0, 471, 10743, 0, 0 |
| r64k_we255 | jet MSHR=8 | 3 | 21.22 | 41 | 0, 8788, 0, 0, 467, 10745, 0, 0 |
| r128k_we64 | amber | 4 | 28.64 | 60 | 0, 0, 4314, 0, 11552, 4134, 0, 0 |
| r128k_we64 | jet MSHR=8 | 3 | 23.61 | 41 | 0, 4331, 0, 0, 11551, 4118, 0, 0 |

Reading: the bucket *populations* match almost exactly between rigs
(8958 vs 8909 hits in b1/b2, …) — identical stimulus, same misses — but
jet's whole distribution sits one bucket left (hit = 3 cyc not 4, miss
tail ends at 41 not 60). The b4/b5 miss populations are the same size on
both rigs; jet's non-blocking pipeline serves them ~18–33% faster on
average and caps the tail.

**Event-semantics caveat:** amber's `hit` bin fires once per served access
(post-miss replays re-hit), so amber's bin0 = 40000 = all accesses; jet's
`hit` bin counts clean hits only (most miss-path traffic in jet reports
through MSHR events instead). Compare `fill_end` for miss volume, never
the raw `miss` bins across rigs.

### 2. MSHR occupancy histogram

From the `MSHR_OCCUPANCY` (0x13) gauge samples in the tally stream (jet
profile keys in `host/jet_board.py:build_default_profile()`), per MSHR_COUNT.
The amber column is structurally 1-outstanding.

**Documented gap (2026-11-03):** the tally counts events, not payloads, so
the occupancy *distribution* (mean/peak/%-full) is not recoverable from the
bins — the gauge value rides in the discarded packet payload. What the bins
do give per MSHR_COUNT: alloc/merge/retire event counts, occupancy-change
event counts, tag-full stall counts, and jet_monlite drops (bin 17,
ISSUE-002). The exact occupancy distribution is available from the jet DV
waveforms / cache_sim cross-check if wanted.

MSHR=8 silicon (r64k_we64, 2×20000 tx): alloc=15203, merge=**0**,
retire=21918, occ-change=25075, stall-tag-full=**0**, jmon_drop=600.
At 8 entries this stimulus never fills the MSHR file (no stalls) and never
merges (LFSR streams over 1024 lines rarely collide with an in-flight
fill) — the grid columns below are where those bins are expected to move.

**Grid finding (2026-11-03): the rig tops out at 2 outstanding misses.**
`amber_cycle_injector` is a strict IDLE→ISSUE→WAIT_RSP loop — one
outstanding transaction per injector, so two injectors put at most two
misses in flight. MSHR_COUNT=2 already saturates: identical run cycles,
latencies, stall and drop counts to MSHR=8 on every config (e.g.
r64k_we64: 390471 vs 389438 ci0 cycles, 0 stalls, 0 merges on both).
Deeper-MSHR evaluation needs a multi-outstanding injector — an injector
feature, recorded here as the same class of documented gap as trace
replay.

| MSHR_COUNT | run cyc (r64k_we64, ci0) | stall-tag-full | merge | jmon_drop |
| --- | --- | --- | --- | --- |
| 2 | 390471 | 0 | 0 | 604 |
| 4 | 390471 (bit-identical to 2) | 0 | 0 | 604 |
| 8 | 389438 | 0 | 0 | 600 |
| 16 | 390471 (bit-identical to 2) | 0 | 0 | 604 |

(The MSHR=8 run's 0.26% cycle delta is sweep-order state carryover — a
standalone smoke ran before it — not an MSHR effect; 2/4/16 are
bit-identical because the design never exceeds 2 outstanding misses.)

### 3. Sustained fill bandwidth

`fill_end` bin per run vs injector run cycles (ci0), per rig/config —
lines/cycle into the cache under the r64k/r128k (thrash) configs:

| config | amber lines/cyc | jet MSHR=8 lines/cyc | delta |
| --- | --- | --- | --- |
| r64k_we64 | 0.0473 | 0.0558 | +17.8% |
| r64k_we255 | 0.0330 | 0.0454 | +37.5% |
| r128k_we64 | 0.0511 | 0.0602 | +17.8% |
| disjoint64k_we64 | 0.0474 | 0.0560 | +18.1% |

The write-storm row is where drain/fill overlap (metric 4) pays: amber
serializes drain→fill, jet does not.

### 4. Drain/fill overlap

`WB_OCCUPANCY` (0x14) gauge vs fill activity: cycles where a drain and a
fill are simultaneously in flight, as a fraction of fill-busy cycles
(jet only; amber serializes drain→fill by construction).

**Measured proxy + documented gap.** The tally bins count events, not
cycle-level coincidence, so the exact "both in flight" cycle fraction is
not recoverable from this rig (the occupancy payload is discarded by the
bin counter — same gap as metric 2). What silicon does show:

- WB occupancy change events per run (jet, MSHR=8): 10078 on r64k_we64,
  **39844** on r64k_we255, 14163 on r128k_we64 — the write buffer is
  continuously active under write thrash, in parallel with 21k fills.
- The r64k_we255 run-cycle delta (−31.5%) is ~2× the read-lean delta
  (−16.6%) at the same working set — the extra win is exactly the
  drain/fill serialization amber pays and jet doesn't.

Jet DV (occupancy waveforms) or the cache_sim cross-check can supply the
exact overlap fraction if it is ever needed; the bins carry the bound.

## Reproduction

```bash
# amber rig (90 MHz build already committed)
python3 projects/fpga-systems/Genesys2/cache-ip/amber/host/amber_perf_sweep.py

# jet rig, per MSHR_COUNT (build once per value, then sweep)
MSHR_COUNT=8 make -C projects/fpga-systems/Genesys2/cache-ip/jet/build-bringup bitstream
python3 projects/fpga-systems/Genesys2/cache-ip/jet/host/jet_perf_sweep.py
```

Raw JSON lands in each area's `results/`; this report's tables are derived
from those files (filenames recorded alongside each table when filled).

---

**Last Updated:** 2026-11-03
**Maintained By:** RTL Design Sherpa Project
