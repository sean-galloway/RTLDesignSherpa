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

# Characterization

## Board targets

amber is characterized on the same FPGA boards the repo uses for other components: Nexys A7 and Genesys 2. The default geometry (32 KiB / 64 B / 4-way) is expected to consume roughly 9 of the 135 36 Kb BRAMs on the Nexys A7, leaving headroom for the rest of the system.

## Sweep dimensions

| Dimension | Values |
|---|---|
| Geometry | default (128 sets / 4 ways / 64 B), tiny (16 sets / 2 ways / 64 B), and boundary points from the 4–32 KiB / 2–8 way range |
| Replacement policy | LRU, tree-PLRU, FIFO, RANDOM |
| Rig | `amber` top, `amber_ace` top |
| Observation | `amber_monlite` present, `amber_monlite` absent |

: Table 6.0: Characterization sweep dimensions

## Reported metrics

For each point, the characterization records LUT, FF, RAMB36 (and RAMB18 where relevant), and fmax. The report follows the pumice pattern: a markdown table per board, a note on the critical path, and the observer-cost delta. A single characterization run is not the goal; the sweep is, because replacement policy and observation are the variables the research questions depend on.

## Critical-path expectation

The expected critical path is through `amber_tag_array` port A: address decode → tag compare → hit/miss decision → data-array enable. The dual-port split (port B for snoops) removes snoop traffic from the CPU hit path, so the path should be comparable to a non-snoopy cache of the same geometry plus the CRRESP combinatorial decode in `amber_control`.
