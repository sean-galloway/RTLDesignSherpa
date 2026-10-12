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

# gabbro — DDR3 / LPDDR3 product (v3)

The v3 product SKU, built from the common stack proven on
[scoria](../../research-ip/scoria-ddr3-lpddr3/).

| | |
|---|---|
| Generation | v3 (DDR3 / LPDDR3 unified) |
| DFI plane | `mc_dfi_3p1_plane` |
| Source rock | [`scoria-ddr3-lpddr3`](../../research-ip/scoria-ddr3-lpddr3/) — RTL complete, sim-verified |
| Board target | Owner Kintex-7 board (planned, shared with the LPDDR2/3/4 bring-up plan) — TBD |
| Status | **Scaffold (2026-10-11)** — not built |

## Configuration intent

- Full storage plane (the v3 generation benefits from reordering; no lite
  configuration by default).
- RAS plane present per SKU need (ECC is the doctrine-9-gated candidate).
- Refresh: scoria's **elastic refresh (v3)** — postpone/pull-in with ±8
  credits — is the intended refresh base; its convergence into the common
  scheduler plane is an open common-ip item this product consumes.

## Contents

- [`config/product_config.md`](config/product_config.md) — the chosen
  configuration (filled at build time).
