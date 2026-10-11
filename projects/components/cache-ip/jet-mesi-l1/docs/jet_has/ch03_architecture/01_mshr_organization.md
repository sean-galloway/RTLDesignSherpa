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

**Stub: open until J1 decides.** This chapter records the decision landscape for the MSHR organization. No architecture is recorded here until J1 closes.

## Candidates

The jet PRD lists three candidate organizations:

| Candidate | Implication |
|---|---|
| Full associativity keyed by address | Simple merge logic; scales poorly with entry count; CAM or pseudo-CAM cost. |
| Direct-mapped by line index | Cheap indexing; bank-conflict hotspots; index conflicts can waste entries. |
| CAM of pending lines | Flexible placement; match-by-address for merge; higher area and timing pressure. |

Capacity is an elaboration parameter in the range 2–16 entries.

## What the decision drives

J1 drives:

- the miss queue structure and its match logic;
- the merge logic for J3;
- the hazard logic for J2;
- the formal surface (which addresses can be outstanding simultaneously);
- the parameterization of `jet_pkg`.

## Background material

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, §10.10 (file 10.8) "Number of outstanding accesses in L2" gives a sizing rule: derive the number of outstanding buffers from average loaded latency, bus width, and cache line size, then scale by expected efficiency. The L2 numbers are larger than jet's L1 MSHR file, but the same latency/bandwidth reasoning is the sizing input for J1.

§8.2 "Deadlocks" notes that buffer reservation is often required so that the oldest non-speculative access can always make progress. The J1 organization must reserve enough structure to avoid the deadlock where a new miss cannot allocate because all MSHRs are held by younger speculative entries.

## Status

No architecture recorded. J1 must decide the organization, capacity parameter, and reservation rule.
