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

# MSHR Organization

**Stub at 0.1–0.2; J1 CLOSED 2026-10-28.** This chapter records the MSHR organization decision and what it drives.

## Decision (J1, DECIDED 2026-10-28, Sean)

**Fully associative CAM keyed by line address; capacity an elaboration
parameter `MSHR_COUNT` in 2–16, default 4.**

Rationale: merge (J3) and hazard (J2) checks are exact-address comparators
over N valid entries — the same shape as amber's per-way tag hit-compare,
which already scales to 4 ways. At N ≤ 16 the CAM is small; the formal
surface is just "the set of outstanding lines", one valid bit and one line
address per entry. Direct-mapped-by-index would still pay the tag compare
for merge while wasting entries on index conflicts; set-indexed banks sit
between the two without beating either.

## Sizing

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, §10.10 (file
10.8): derive outstanding-buffer count from average loaded latency, bus
width, and line size. At 64 B lines over a 64-bit bus (8 beats),
~50–100-cycle memory latency, and a streaming miss rate of ~1 per 10
cycles, 4–13 entries cover the bandwidth window. The default is 4; the DV
grid sweeps 2/4/8/16 so the occupancy→bandwidth curve is itself a J7
result.

## Liveness (allocation rule)

Per Chinnakonda §8.2: buffer reservation must let the oldest non-
speculative access always make progress. Jet has no speculative or
prefetch entries (PRD non-goals), so the rule collapses to: **a fill once
started always retires; MSHR-full stalls new miss allocation (J6 strict
stall)**. No reservation pool is needed.

## What the decision drives

- the miss queue structure: one CAM row per entry
  {valid, line addr, fill class, expected install state, requester
  sequence tag};
- the merge logic for J3 (exact-line match = one comparator per entry);
- the hazard logic for J2 (hit-vs-pending-fill exclusion = the same
  comparators);
- the formal surface (which addresses can be outstanding simultaneously:
  any N distinct lines);
- `jet_pkg` parameterization (`MSHR_COUNT`).
