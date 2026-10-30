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

# gem5 FSM Cross-Check

**Status:** planned contract. The coherence semantics are per-line and
timing-free, so the gem5-derived `l1_fsm_oracle` carries over unchanged:
every stable and transient transition is still pinned against the
`MESI_Two_Level-L1cache.sm` derivation, and jet adds NO line states.

What changes is the temporal mapping, and the cross-check grows one axis:

- **Per-line lockstep (unchanged):** each line's observed
  snoop/fill/commit effects must match the oracle's state sequence.
- **Concurrency (new):** the cache_sim golden model must predict jet's
  concurrency numbers (MSHR occupancy, merge rate, bandwidth) or the gap
  is documented as a finding — the J7 success criterion. The plan: extend
  cache_sim with an outstanding-miss model (alloc on miss, retire at a
  parameterized fill latency, merge on alias) and cross-check the
  occupancy histogram against the RTL's MonBus capture on the same trace.

The transient-state coverage that amber's oracle encodes (IS/IM/SM/IS_I/
M_I/SINK_WB_ACK) maps onto jet's MSHR entry states one-for-one: an
outstanding RNSD fill IS the line's IS transient; the WB-buffered victim
IS M_I; a snarfed drain IS SINK_WB_ACK. The oracle already speaks jet's
language; only the timing it tolerates widens.
