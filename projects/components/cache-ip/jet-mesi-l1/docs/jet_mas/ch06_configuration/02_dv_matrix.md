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

# DV Matrix Dimensions

**Status:** the grid's RTL find is FIXED (BUG-004, 2026-10-29): the
pend_eff repeat-snoop resolution in `jet_control` (inherited from
amber's `l1_control`) resolved a repeat snoop against the original
post-fill state instead of chaining the armed pending effect — armed
DOWNGRADE_S + READ_ONCE on an in-flight write-miss fill invalidated the
line at commit and silently dropped the store.  Both modules now chain
the effect against the armed state (the grant-cycle CRRESP still answers
at the post-fill row); the corner is pinned by the `PendArmedDowngradeRO`
directed test (all levels), the amber oracle row
`IM + SNOOP_READ_ONCE+in_pending=S`, and the formal `ap_pend_chain`
safety property.  See the Task-12 report
(.superpowers/sdd/2026-10-28-jet-mshr-implementation/task-12-report.md).
The grid multiplies amber's matrix by the two jet knobs:

| Axis | Values |
|---|---|
| Level | GATE / FUNC / FULL |
| Geometry | tiny (16/2) / default (128/4) |
| `MSHR_COUNT` | 2 / 4 / 8 / 16 |
| `VICTIM_DEPTH` | 1 / 2 / 4 |
| Replacement policy | LRU / FIFO / RANDOM (cache_sim parity); tree-PLRU by RTL self-check |
| Rig | pair (`jet_top`) / onyx (`jet_ace_top`, when onyx lands) |

FULL at the sweep corners is the sign-off grid; the interior is sampled
(seeds pinned per node by the repo-root conftest, as everywhere else).

**Grid cells (the sign-off run, 2026-10-29, SEED=1, REG_LEVEL=FULL —
ALL GREEN, 0 mismatches in every cell):**

- `test_jet_core` FULL: 32 cells -- every corner (MSHR {2,16} x VICTIM
  {1,4}) x {LRU,FIFO,RANDOM} x both geometries (24) + interior samples
  (4,2,LRU) / (8,2,LRU) at both geometries, (4,2,FIFO) / (8,2,RANDOM)
  at both geometries (8).  Each cell: the directed suite + the FULL
  content below + the 10k amber-depth soak.  Executed: 36/36 green
  (32 grid + 2 gate + 2 func at the FULL reg level).
- `test_jet_pair_rig` FULL: 20 cells -- the default-knob cell at both
  geometries + corners (MSHR {2,16} x VICTIM {1,4}) x {LRU,FIFO} x both
  geometries (16) + (4,2,LRU) / (8,2,FIFO) interior at 128/4 (2).
  Executed: 26/26 green (incl. gate/func cells at the FULL reg level).
  RANDOM runs on the core grid: the pair rig's WB-snarf and
  dirty-eviction directed constructions are eldest-victim timed
  (LRU/FIFO), and the policy axis's cache_sim parity is single-cache by
  construction (amber's pair rig precedent is LRU-only).
- `test_jet_parity` FULL: 30 cells -- the five committed cache_sim
  traces x {LRU,FIFO,RANDOM} x both geometries, exact
  hits/misses/compulsory/capacity/conflict parity against
  `bin/apps/cache_sim/js/model.js` (RANDOM via the recorded LFSR
  extension), at the J1 default knobs (the sweep cells pin the victim
  way at every alloc against the same policy models).  Executed: 66/66
  green (30 FULL + gate/func cells).

## What FULL contains (beyond amber's soak)

- Miss streams at maximal sustainable MSHR pressure with concurrent
  hits and snoops (`MshrSaturation`).  **Measured structural ceiling:**
  jet's lookup allocates at most one entry per fill-launch window (the
  launch register waits for the single-outstanding fill engine --
  amber's unchanged `l1_fill`), so the file's sustainable occupancy is
  the engine pipeline (one filling + one launch-pending entry) plus the
  done-not-retired backlog the commit pacer allows.  Occupancy at
  `MSHR_COUNT` is literal at the K=2 corner; at K >= 4 the integrated
  rig plateaus at 3-5 live entries (the wider file is burst-absorption
  headroom by design; MSHR-full at K=16 is covered at the unit level
  and the formal corner is proven at K=2).  The scenario pins the
  plateau floor and, at K=2, literal full + the `mshr_full` stall.
- Merge storms: repeated aliases to outstanding lines (`MergeStorm`).
- Set-oversubscription pressure: miss bursts into one set
  (`SetOversubscription`).  The stall window is `L_commit0 > 2 fast fill
  times` (the overflow miss allocates at `fill_done(2)`; claim 0 frees
  at commit-0 retire), so the v4 construction holds fill 0 GLACIAL while
  the miss pair allocates and the merge list fills (cap `MSHR_COUNT`),
  then runs FAST fills behind commit 0's merge lag.  The
  `set_oversubscribed`/`mshr_full` stall is pinned at every cell except
  K=4/WAYS=4, where the merge cap bounds the commit lag at ~19 cycles
  against the ~26-cycle requirement — there the pin is the claim floor
  (>= 3) and the stall stays covered by the K=2/WAYS=2 cells, the unit
  TB, and the formal K=2 corner (the plateau finding above).
- The composed corner: maximal MSHR pressure + WB-full (VICTIM_DEPTH
  reached) + snoop soak, dynamically (`ComposedCorner`) --
  complementing the formal proof (ch05/01) at the tiny geometry; the
  simultaneous full-MSHR + full-WB corner is asserted at the K=2 cells.
- The amber FULL suite re-run on jet unchanged (the inheritance claim:
  amber's DV content is jet's subset): the 10k-transaction randomized
  oracle-lockstep + interleaved snoop soak at amber's FULL depth on the
  inherited machinery, plus the cache_sim trace-replay parity grid
  (`test_jet_parity`, the mechanism amber's `test_amber_parity` proves
  for the policy axis).
