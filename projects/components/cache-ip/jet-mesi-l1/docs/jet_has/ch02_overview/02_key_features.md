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

- **MSHRs.** A small table of outstanding misses so the cache does not stall on every miss. Capacity and organization are J1.
- **Hit-under-miss.** Resident lines continue to serve hits while fills are in flight. Scope is J2.
- **Miss merging.** Later misses to the same line join the outstanding entry instead of issuing duplicate fetches. Policy is J3.
- **Snoop-during-miss correctness.** Incoming snoops see either the post-fill state or a clean stall; ordering guarantees are J4.
- **Eviction under misses.** Dirty victims behind outstanding fills write back without deadlocking. Depth and policy are J5.
- **Congestion/fairness policy.** Behavior when MSHRs are full, plus snoop-vs-fill arbitration, is J6.
- **Measurement by construction.** MonBus observation exposes MSHR occupancy, hit latency distribution, and miss concurrency to answer J7.

Everything else — MESI coherence, the shared core, the GAXI/AXI4/ACE interfaces, the ACE-shaped snoop port, and the monlite observer — is inherited from amber.
