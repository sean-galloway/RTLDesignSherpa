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

# Characterization

**Stub at 0.1–0.2; J7 CLOSED 2026-10-28.** This chapter defines the
measurement protocol for the pair-rig experiment as ruled.

## The frozen experiment (J7, DECIDED 2026-10-28, Sean)

Same trace suite and same board as amber — the cache_sim trace corpus and
the Genesys2 pair rig — with identical traces driven at both caches and
identical observation conditions (amber D8 `*_monlite` taps, MonBus tally
capture).

**Four metrics, all from MonBus evidence:**

1. **Hit-latency distribution** under a background miss stream (the
   hit-under-miss win: hit latency with fills outstanding vs amber's
   blocked pipeline).
2. **MSHR occupancy histogram** (how much of the file the workload
   actually uses).
3. **Sustained fill bandwidth** (lines/cycle under streaming misses,
   amber vs jet).
4. **Drain/writeback overlap** (drain cycles hidden under fills vs
   amber's serialized victim handling).

**Sweep:** `MSHR_COUNT` ∈ {2, 4, 8, 16} at default geometry — the
occupancy→bandwidth curve is itself a result.

**Model cross-check:** cache_sim gains a concurrency model predicting
jet's occupancy and bandwidth numbers, or the model gap is documented as
a finding (per the PRD success criteria).

fmax reporting methodology and observer-cost quantification follow the
amber rig's conventions (and inherit its rig-upgrade work, formal
TASK-001) when the board sweep runs.
