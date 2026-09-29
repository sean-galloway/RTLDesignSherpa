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

# DDR4 / LPDDR4 Family Memory Controller

Unified parameterized memory controller targeting both DDR4 SDRAM and
LPDDR4 SDRAM via DFI v4.0. Planned successor to the DDR3/LPDDR3 family.

## Status

**Structure only** — directory baseline created. No HAS, no RTL.

## Planned Deltas vs DDR3/LPDDR3

- Bank groups (4 groups × 4 banks); tCCD_L vs tCCD_S scheduler awareness
- act_n as a separate primary command bit (DDR4)
- Command/Address parity with ALERT_n recovery FSM
- LPDDR4 uses a fundamentally different 6-bit CA bus (clean break from LPDDR2/3)
- Dual-channel architecture for LPDDR4 dies
- Mandatory Command Bus Training (CBT) for LPDDR4
- Write CRC, DBI

## See Also

- Parent: [`../README.md`](../README.md)
