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

**Status: METHOD FROZEN, DATA PENDING** — the jet Genesys2 pair rig is built
and timing-clean (`projects/fpga-systems/Genesys2/cache-ip/jet/`, 60 MHz, WNS
+0.220 ns); the sweep runs when the board is on the bench. Every table below
is a fill-in.

J7 is the PRD's measurement success criterion: quantify what the MSHRs buy
over amber's blocking pipeline, with MonBus evidence, on identical stimulus.

## Method

- **Rigs.** amber pair rig (`fpga-systems/Genesys2/cache-ip/amber/`, 90 MHz)
  and jet pair rig (`fpga-systems/Genesys2/cache-ip/jet/`, 60 MHz — jet
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

## The four metrics (jet MAS ch04 §metrics)

Latencies are quoted **load-to-use**: request accept → data usable
(the §9.10.3 rule), which is exactly the injector's accept→response count.

### 1. Hit-latency distribution under a miss stream

The J6 claim: hits proceed while misses are in flight. Per config:
latency histograms (8 log2 buckets) for jet vs amber at the same working
set; the separation at 4 KB shared (heavy snoop + miss traffic) is the
headline cell.

| config | rig | min | mean | max | hist (b0..b7) |
| --- | --- | --- | --- | --- | --- |
| smoke4k_we64 | amber | _pending_ | | | |
| smoke4k_we64 | jet MSHR=8 | _pending_ | | | |
| r64k_we64 | amber | _pending_ | | | |
| r64k_we64 | jet MSHR=8 | _pending_ | | | |

### 2. MSHR occupancy histogram

From the `MSHR_OCCUPANCY` (0x13) gauge samples in the tally stream (jet
profile keys in `host/jet_board.py:build_jet_profile()`), per MSHR_COUNT.
The amber column is structurally 1-outstanding.

| MSHR_COUNT | mean occupancy | peak | % cycles full |
| --- | --- | --- | --- |
| 2 | _pending_ | | |
| 4 | _pending_ | | |
| 8 | _pending_ | | |
| 16 | _pending_ | | |

### 3. Sustained fill bandwidth

`fill_end` bin delta per run vs run cycles, per rig/config — lines/cycle
into the cache under the r64k/r128k (thrash) configs.

### 4. Drain/fill overlap

`WB_OCCUPANCY` (0x14) gauge vs fill activity: cycles where a drain and a
fill are simultaneously in flight, as a fraction of fill-busy cycles
(jet only; amber serializes drain→fill by construction).

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

**Last Updated:** 2026-11-02
**Maintained By:** RTL Design Sherpa Project
