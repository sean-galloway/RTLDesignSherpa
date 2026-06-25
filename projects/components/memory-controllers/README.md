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

# Memory Controllers

Unified parameterized memory-controller families. Each family combines a
`DDR` and `LPDDR` generation (which share contemporary process node and
JEDEC era) into a single controller engine with a swappable command encoder.

## Families

| Directory | Controller scope | DFI version | Notes |
|---|---|---|---|
| [`ddr2-lpddr2/`](ddr2-lpddr2/) | DDR2 + LPDDR2 unified | v2.1 | Status: HAS v0.3 published; pre-architecture stage |
| [`ddr3-lpddr3/`](ddr3-lpddr3/) | DDR3 + LPDDR3 unified | v3.1 | Planned; structure only |
| [`ddr4-lpddr4/`](ddr4-lpddr4/) | DDR4 + LPDDR4 unified | v4.0 | Planned; structure only |

See [`../stream/README.md`](../stream/README.md) for the per-component
layout convention this directory follows.
