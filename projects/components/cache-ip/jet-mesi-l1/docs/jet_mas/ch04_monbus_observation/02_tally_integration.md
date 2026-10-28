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

# Drop-and-Count Behavior and monbus_tally_axil

**Status:** planned contract, inherited from amber's observation
integration (amber MAS ch04/02) with the jet classes added.

## Tally structure

The standard `monbus_tally_axil` agent bins jet's classes the same way it
bins amber's; the J7 histograms come from two places:

- **Occupancy histograms:** the tally's per-class bins count alloc/retire
  events; the occupancy DISTRIBUTION comes from the gauge payloads binned
  by the host-side reduction (the events carry occupancy-after).
- **Latency distributions:** fill latency and hit-under-miss latency ride
  as payload fields; the host bins them (the tally counts, the host
  histograms — same split as amber's perf counters).

## Drop policy under concurrency

MSHR concurrency raises the event rate at fixed observer bandwidth; the
drop counter is therefore a first-class J7 output: a sweep point whose drop
count is nonzero reports its metrics with the drop count attached, and the
observer-cost experiment (HAS ch04/02) re-runs with `jet_monlite` removed
to quantify perturbation.
