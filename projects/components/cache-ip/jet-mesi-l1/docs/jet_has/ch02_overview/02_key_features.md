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

# Key Features

- **MSHRs.** A fully associative CAM of outstanding misses (J1: exact-line
  match, `MSHR_COUNT` 2–16, default 8), so the cache does not stall on
  every miss.
- **Hit-under-miss.** Reads AND writes to any resident line proceed while
  fills are in flight (J2); the single write port arbitrates fill beats
  over write hits.
- **Miss merging.** Later misses to the same line join the outstanding
  entry instead of issuing duplicate fetches (J3: exact-line aliases,
  same-class joins, cross-class waits — no in-flight escalation).
- **Snoop-during-miss correctness.** Incoming snoops to a pending line are
  answered at the post-fill state by a per-entry bypass (J4); responses
  release to the CPU in issue order while fills complete out of order
  internally.
- **Eviction under misses.** Dirty victims are captured to a decoupled
  writeback buffer at miss start and drained oldest-first without blocking
  the fill (J5: `VICTIM_DEPTH` 1–4, default 2).
- **Congestion/fairness.** Strict stall on MSHR-full / writeback-full;
  snoops arbitrate ahead of new CPU accepts (J6); a bounded snoop hold-off
  after an upgrade grant prevents the CU livelock.
- **Measurement by construction.** MonBus observation exposes MSHR
  occupancy, hit latency distribution, and miss concurrency to answer J7.

Everything else — MESI coherence, the shared core, the GAXI/AXI4/ACE interfaces, the ACE-shaped snoop port, and the monlite observer — is inherited from amber.
