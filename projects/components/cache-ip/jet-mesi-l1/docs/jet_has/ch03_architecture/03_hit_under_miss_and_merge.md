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

# Hit-Under-Miss and Miss Merging

**Stub: open until J2 and J3 decide.** This chapter records the decision landscape for hit-under-miss scope and miss merging policy. No architecture is recorded here until J2 and J3 close.

## J2: hit-under-miss scope

The candidates from the jet PRD are:

| Candidate | Implication |
|---|---|
| Hits to any resident line | Maximum concurrency; must check every access against all pending addresses for hazards. |
| Hits only to lines not conflicting with a pending fill | Simpler hazard logic; may artificially serialize accesses to the same set. |
| Reads-only hit-under-miss | Writes still block; lower replay complexity, smaller write-ordering exposure. |

The choice determines the hazard logic between the fill port and the hit port and the replay queue structure.

## J3: miss merging policy

The candidates from the jet PRD are:

| Candidate | Implication |
|---|---|
| Merge only exact-line aliases | Simplest match; no partial-forwarding complexity. |
| Merge line plus offset range | Allows forwarding partial data from a pending fill; more hazard cases. |
| No merging | Issue duplicate fetches and dedupe on return; highest memory traffic, simplest table. |

The choice drives memory traffic, MSHR occupancy, and fairness.

## Status

No architecture recorded. J2 must decide the hit-under-miss scope; J3 must decide the merge policy. The architecture here will be written after both close.
