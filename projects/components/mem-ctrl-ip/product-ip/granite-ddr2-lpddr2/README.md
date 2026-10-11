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

# granite — DDR2 / LPDDR2 product (v2)

The v2 product SKU and the family's **bypass-validation testbed**: the
cheapest full proof that the common core runs correctly with its optional
layers at minimum and absent, before gabbro/diorite spend area on features
the v2 generation will never see
([common_has ch5.2](../../common-ip/docs/common_has/ch05_lineup/02_products_and_research.md)).

| | |
|---|---|
| Generation | v2 (DDR2 / LPDDR2, one engine + swappable encoder) |
| DFI layer | `mc_dfi_2p1_layer` |
| Source rock | [`pumice-ddr2-lpddr2`](../../research-ip/pumice-ddr2-lpddr2/) — board-validated (Nexys A7 DDR2) |
| Board target | Nexys A7-class product board — TBD |
| Status | **Scaffold (2026-10-11)** — not built |

## Configuration intent (ch5.2 defaults for v2)

- **Storage layer, lite configuration** — N=1 in-order seam; the entry
  store shrinks toward one entry, never to zero.
- **RAS layer absent** — true bypass: no transform pair instantiated, no
  scrub; only the reserved CSR decode.
- **Write-data buffer at SKU minimum** — sized by the product burst
  profile, not the research characterization sweep.
- **Never omitted** — entry store, write-data staging, aclk↔dfi_clk CDC,
  maintenance request/grant path.

The v2 generation needs no bank groups, no FGR, no DBI, no CA parity —
none appear in this SKU.

## Contents

- [`config/product_config.md`](config/product_config.md) — the chosen
  configuration (to be filled at build time; the SKU's single source of
  truth).

The product book, when granite is built, is short by doctrine: the
[common architecture book](../../common-ip/docs/common_has/common_has_index.md)
+ this configuration + the product's board.
