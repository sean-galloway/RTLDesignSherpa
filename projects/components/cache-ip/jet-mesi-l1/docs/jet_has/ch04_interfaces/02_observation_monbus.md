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

# Observation: MonBus and the J7 Measurement Classes

## Inherited observation path

jet observes through `*_monlite` wrappers only, inherited from amber D8. The rationale is the same: a heavyweight `_mon` wrapper that stalls when its tables fill would corrupt the miss-latency numbers the cache exists to produce. `jet_monlite` is drop-and-count: packets are emitted when possible, dropped and counted when not, and the observed path never stalls.

The base MonBus packet content is the same as amber ch04 `05_observation_monbus.md`: hit, miss, snoop, eviction, MESI transition, and fill/drain events.

## J7 measurement classes

To answer the research question, the observer must expose the following classes at minimum:

| Class | What it measures | Why it matters |
|---|---|---|
| MSHR occupancy | Number of allocated MSHR entries per cycle | Correlates concurrency with latency and bandwidth. |
| Hit latency distribution | Cycle latency of hits that complete while misses are outstanding | Quantifies the hit-under-miss benefit. |
| Miss concurrency | Number of distinct lines outstanding, merge events, duplicate fetches | Validates J3 and the cache_sim extension. |
| Fill latency | Time from miss issue to fill return, per line | Baseline for the latency delta claim. |
| Victim buffer occupancy | Number of dirty victims waiting behind fills | Exposes the J5 deadlock corner under stress. |
| Snoop-during-miss events | Snoops that match pending lines or victim buffers | Validates J4 correctness. |

: Table 4.0: J7 measurement classes

These classes are the observation requirements the architecture must expose. The exact bit assignments and counter widths are deferred to the MAS, but the MonBus path must be wide enough to carry them.

## Observer cost

The cost of observation is measured in the characterization sweep ([Chapter 6.3](../ch06_integration/03_characterization.md)): LUT/FF/RAM and fmax are reported with `jet_monlite` present and with it removed, so the claim "the observer does not perturb what it measures" is quantified.
