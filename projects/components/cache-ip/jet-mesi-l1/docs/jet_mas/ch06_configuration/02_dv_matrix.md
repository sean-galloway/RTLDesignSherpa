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

**Status:** BLOCKED on a real RTL bug found by the grid (Task 12,
2026-10-29): the pend_eff repeat-snoop resolution in `jet_control`
(inherited from amber's `l1_control`) resolves a repeat snoop against the
original post-fill state instead of chaining the armed pending effect —
armed DOWNGRADE_S + READ_ONCE on an in-flight write-miss fill invalidates
the line at commit and silently drops the store.  See the Task-12 report
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

**Grid cells (the sign-off run is pending the RTL ruling above):**

- `test_jet_core` FULL: 32 cells -- every corner (MSHR {2,16} x VICTIM
  {1,4}) x {LRU,FIFO,RANDOM} x both geometries (24) + interior samples
  (4,2,LRU) / (8,2,LRU) at both geometries, (4,2,FIFO) / (8,2,RANDOM)
  at both geometries (8).  Each cell: the directed suite + the FULL
  content below + the 10k amber-depth soak.
- `test_jet_pair_rig` FULL: 20 cells -- the default-knob cell at both
  geometries + corners (MSHR {2,16} x VICTIM {1,4}) x {LRU,FIFO} x both
  geometries (16) + (4,2,LRU) / (8,2,FIFO) interior at 128/4 (2).
  RANDOM runs on the core grid: the pair rig's WB-snarf and
  dirty-eviction directed constructions are eldest-victim timed
  (LRU/FIFO), and the policy axis's cache_sim parity is single-cache by
  construction (amber's pair rig precedent is LRU-only).
- `test_jet_parity` FULL: 30 cells -- the five committed cache_sim
  traces x {LRU,FIFO,RANDOM} x both geometries, exact
  hits/misses/compulsory/capacity/conflict parity against
  `bin/apps/cache_sim/js/model.js` (RANDOM via the recorded LFSR
  extension), at the J1 default knobs (the sweep cells pin the victim
  way at every alloc against the same policy models).  The gate tier
  (seq_1k x 3 policies x both geometries) is green.

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
  (`SetOversubscription`).
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
