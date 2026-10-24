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
planes at minimum and absent, before gabbro/diorite spend area on features
the v2 generation will never see
([common_has ch5.2](../../common-ip/docs/common_has/ch05_lineup/02_products_and_research.md)).

| | |
|---|---|
| Generation | v2 (DDR2 / LPDDR2, one engine + swappable encoder) |
| DFI plane | `mc_dfi_2p1_plane` |
| Source rock | [`pumice-ddr2-lpddr2`](../../research-ip/pumice-ddr2-lpddr2/) — board-validated (Nexys A7 DDR2) |
| Board target | Nexys A7-class product board — TBD |
| Status | **Scaffold (2026-10-11)** — not built |

## Configuration intent (ch5.2 defaults for v2)

- **Storage plane, lite configuration** — N=8 slots per direction on the
  per-bank FIFO store (`mc_bank_fifo_store`, `STORE_BACKEND=1`, the default
  since 2026-10-23): bank queues pool-deep, head records read off the
  queue fronts, no age matrix. `STORE_BACKEND=0` keeps the entry store +
  `mc_bank_head_records` for A/B. Storage "off" shrinks toward one, never
  to zero. `HAS_LPDDR2=0` compiles the LPDDR2 training plane out of a
  DDR2-only build; `FIXED_TIMINGS=1` replaces the TIMINGS CSRs with the
  `T_*` constants (one-part product). Measured in the mem-ctrl recovery
  Phase 3 report, section 5.10.
- **RAS plane absent** — true bypass: no transform pair instantiated, no
  scrub; only the reserved CSR decode.
- **Write-data buffer at SKU minimum** — sized by the product burst
  profile, not the research characterization sweep.
- **Never omitted** — entry store, write-data staging, aclk↔dfi_clk CDC,
  maintenance request/grant path.

The v2 generation needs no bank groups, no FGR, no DBI, no CA parity —
none appear in this SKU.

## Contents

- [`config/product_config.md`](config/product_config.md) — the chosen
  configuration (plane selection, reasoning, open values).
- [`rtl/includes/granite_pkg.sv`](rtl/includes/granite_pkg.sv) — the SKU
  parameter package (lite storage N=8, SKU write-data staging, frequency
  plan placeholders).
- [`rtl/filelists/top/granite.f`](rtl/filelists/top/granite.f) — the
  plane selection as a filelist: common-ip only, by construction. There is
  deliberately no `granite_core.sv` yet — see TASK-001 (wrapper dissolution)
  in this product's vault area.

The product book, when granite is built, is short by doctrine: the
[common architecture book](../../common-ip/docs/common_has/common_has_index.md)
+ this configuration + the product's board.
