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

# DDR3 / LPDDR3 Family Memory Controller

Unified parameterized memory controller targeting both DDR3 SDRAM and
LPDDR3 SDRAM via DFI v3.1. Planned successor to the DDR2/LPDDR2 family.

## Status

**Structure only** — directory baseline created. No HAS, no RTL.

## Planned Deltas vs DDR2/LPDDR2

- Write leveling support (DDR3 and LPDDR3 both add it)
- ZQ calibration via dedicated ZQCS/ZQCL commands
- Faster data rates (DDR3-1600, LPDDR3-1866/2133)
- LPDDR3 inherits LPDDR2 10-bit CA bus encoding (no protocol break)
- CSR field set largely inherited from DDR2/LPDDR2

## See Also

- Parent: [`../README.md`](../README.md)
- DDR2/LPDDR2 reference HAS: [`../ddr2-lpddr2/docs/DDR2_LPDDR2_HAS_v0.3.pdf`](../ddr2-lpddr2/docs/DDR2_LPDDR2_HAS_v0.3.pdf)
