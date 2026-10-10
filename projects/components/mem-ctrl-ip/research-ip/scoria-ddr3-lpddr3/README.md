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
LPDDR3 SDRAM via DFI v3.1. Successor to the pumice DDR2/LPDDR2 controller,
from which its architecture is derived.

## Status

**Implemented and verified in simulation; board work in progress.**

- HAS v0.8 (2026-10-03): `docs/scoria_has/` — reconciled against the RTL
  and the first board work; Q1-Q5 resolved. The published book is
  `docs/DDR3_LPDDR3_HAS_v0.8.pdf`.
- RTL complete: AXI4 slave and APB CSR in, DFI v3.1 master out. Measured
  2026-10-01: 221 tests passing, 9 formal blocks, and a top tier running
  AXI in and DFI out with data through the whole datapath.
- Target design point: Digilent Genesys 2, K7DDRPHY, 2 x MT41J256M16,
  DDR3-800 — 3200 MB/s theoretical peak. See HAS Chapter 2.4.
- Board build flow exists (`projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/build-scoria/`,
  board top + harness, passing lint); no bitstream yet. First out-of-context
  synthesis found the design point missing 100 MHz by ~2 ns
  ([BUG-003](../../../../../vault/Tasks/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/bug/closed/BUG-003.md), P1).

## Deltas vs DDR2/LPDDR2 (pumice)

Delivered against the original plan; the HAS marks every block INHERITED,
MODIFIED or NEW:

- Write leveling support (DDR3 and LPDDR3 both add it) — interface in RTL,
  search in firmware, per decision D2
- ZQ calibration via dedicated ZQCS/ZQCL commands (`scoria_zq_ctrl`)
- Faster data rates (DDR3-1600, LPDDR3-1866/2133)
- LPDDR3 inherits LPDDR2 10-bit CA bus encoding (no protocol break)
- CSR field set largely inherited from DDR2/LPDDR2, plus ZQ, write-leveling
  and refresh-mode groups

## See Also

- [PRD](PRD.md) — product requirements
- [Design requirements](docs/design-requirements.md) — the binding delta
  analysis against JESD79-3F / JESD209-3C / DFI v3.1
- [HAS index](docs/scoria_has/scoria_has_index.md)
- Parent: [`../README.md`](../../README.md)
- Work items: [`vault/Tasks/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/`](../../../../../vault/Tasks/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/INDEX.md)
- DDR2/LPDDR2 predecessor: `../pumice-ddr2-lpddr2/`
