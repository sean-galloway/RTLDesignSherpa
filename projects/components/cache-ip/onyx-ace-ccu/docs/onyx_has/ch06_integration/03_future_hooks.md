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

# Future Hooks

This chapter records scope-growth options and upgrade paths that are out of the onyx v1 scope but must not be closed off accidentally. The material is a mix of real candidate direction and stubs for open N rows.

## AxLock / PoS monitor for exclusives (N2)

**Open candidate.** For cross-master exclusive transactions, arm a PoS monitor on `AxLock`. One master receives `EXOKAY` (pass); competing `CleanUnique` transactions receive `OKAY` (fail); invalidation snoops are withheld from the winning master until its store completes. Chinnakonda §7.9–7.10 and §14.36 describe this as the livelock-reduction recipe for store exclusives. This is out of the initial D2 subset; recorded as a candidate upgrade.

## WLU/WU + WC/WE coherent-DMA support (N5)

**Open scope-growth option.** Add `WriteLineUnique` / `WriteUnique` for coherent DMA / mem-copy, plus `WriteClean` / `WriteEvict` for clean-victim handling. Chinnakonda §7.3–7.4 and §11.1–11.3 tie WLU/WU to mem-copy traffic (read stream → `ReadShared` + `Evict`, write stream → `WriteLineUnique`); WC/WE handle clean victims and LLC victim caching. If promoted, the front-end decoder, fanout/adjudication, and conformance matrix all expand.

## DVM upgrade path (N6)

**Open scope-growth option.** If DVM is ever promoted, follow the book's recipe: DVM Messages are two-beat read transactions sent back-to-back with no intervening transaction; one DVM Sync per cluster is serialized at the SI; DVM Complete uses a unique ARID and is sent only after all translated-address buffers have drained. Chinnakonda §7.16. Revisits the D8/DVM non-goal but does not promote it.

## Prefetch-traffic constraint (N7)

**Open invariant.** The CCU must never see speculative store-ownership requests. Prefetch traffic, if it reaches onyx at all, is speculative `ReadShared` / `ReadClean` only. Chinnakonda §13.3: processors do not prefetch for stores because prefetches are speculative and must not make speculative state changes or set Dirty bits. This is a constraint on the caches and the BFM scenario matrix, not a new onyx feature.

## Barrier support beyond D8

**Future IP or later decision.** D8 recommends single shareability domain with barriers ignored. Full barrier ordering is a scope-growth option, not a v1 requirement.

## Multi-CCU / multi-domain

**Future IP.** onyx v1 is a single manager instance in a single shareability domain. Connecting multiple onyx instances or multiple domains is not architecture at 0.1.

## Status

None of these hooks is architecture at 0.1. The N2–N7 rows must close before any of them becomes real design content.
