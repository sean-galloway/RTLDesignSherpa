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

# Observation: MonBus through amber_monlite

## Observation decision

amber observes through `*_monlite` wrappers only, not the heavyweight `_mon` (amber D8). The rationale is measurement integrity: a `_mon` wrapper that stalls the port when its tracking tables fill would corrupt the very miss-latency numbers the cache exists to produce. `amber_monlite` is drop-and-count: packets are emitted when possible, dropped and counted when not, and the observed path never stalls.

## MonBus packet content

`amber_monlite` emits 128-bit MonBus packets with the standard UNIT/AGENT ids. Event classes:

| Event class | Payload highlights |
|---|---|
| hit (read/write) | address set, way, MESI state before/after |
| miss | address set, way, miss class (compulsory/capacity/conflict when the golden model supplies it) |
| snoop | snoop type, hit/miss, response class |
| eviction | clean/dirty, address set/way |
| MESI transition | old state, new state, cause |
| fill/drain start+end | address, direction, transaction type |

: Table 4.6: MonBus event classes

`monbus_tally_axil` tallies these packets exactly like every other component in the repo. Event classification uses the same cache_sim per-access miss-class computation: compulsory, capacity, and conflict.

## Observer cost

The cost of observation is measured in the characterization sweep (Chapter 6.3): LUT/FF/RAM and fmax are reported with `amber_monlite` present and with it removed, so the claim "the observer does not perturb what it measures" is quantified.
