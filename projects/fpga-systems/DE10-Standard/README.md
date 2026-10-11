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

**[← Back to FPGA Systems Index](../index.md)**

# DE10-Standard Board Area

Terasic DE10-Standard: Cyclone V SoC (5CSXFC6D6F31C8) — ARM HPS with hard DDR3
memory controller + FPGA fabric. Toolchain: Intel Quartus Prime 24.1 Standard.

## Contents

| Area | Description |
| --- | --- |
| [fabric-benchmark](fabric-benchmark/) | Fabric comparison campaign: bridge-generated crossbar vs Intel Platform Designer interconnect, size + bandwidth/latency on identical traffic |

## Status

Bring-up has not started. The Quartus projects for both legs land under
`fabric-benchmark/quartus/` once the DE10 collateral (Quartus/Platform
Designer IP inventory, HPS DDR configuration) is available.
