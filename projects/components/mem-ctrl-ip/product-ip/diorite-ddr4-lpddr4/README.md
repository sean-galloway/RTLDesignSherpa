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

# diorite — DDR4 / LPDDR4 product (v4)

The v4 product SKU, built from the common stack proven on
[andesite](../../research-ip/andesite-ddr4-lpddr4/).

| | |
|---|---|
| Generation | v4 (DDR4 / LPDDR4 unified) |
| DFI layer | `mc_dfi_4p0_layer` |
| Source rock | [`andesite-ddr4-lpddr4`](../../research-ip/andesite-ddr4-lpddr4/) — planned; structure and books first |
| Board target | Owner Kintex-7 board (planned) — TBD |
| Status | **Scaffold (2026-10-11)** — not built; the research rock it consumes is itself not built |

## Configuration intent

- Full storage layer; RAS layer present per SKU need.
- Carries the v4 generation command surface on the DFI 4.0 layer: bank
  groups (`cmd_bg`), gear-down phase mask, CA parity / `alert_n`, DBI —
  see the `mc_dfi_4p0_layer` chapter of the
  [common MAS](../../common-ip/docs/common_mas/common_mas_index.md) for the
  current feature state (gear-down and CA parity are §TBC there).

## Contents

- [`config/product_config.md`](config/product_config.md) — the chosen
  configuration (filled at build time).
