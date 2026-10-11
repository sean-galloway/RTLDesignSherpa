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

# mem-ctrl-ip family docs

This directory holds what no single controller owns: the shared-core design
(`mem_ctrl_pkg`), the family doctrine, the DFI boundary lineage, the
JEDEC generation deltas, and — as of the Phase-2 campaign (2026-10-09 →
2026-10-10) — the family's two book-length specifications: the overarching
HAS (the layer-stack architecture) and the common MAS (per-block
microarchitecture of every block in `common-ip/rtl/`). Three controllers
live under this tree — pumice (DDR2/LPDDR2), scoria (DDR3/LPDDR3), andesite
(DDR4/LPDDR4) — and the designs in here migrate across all of them or none
of them.

> **The ownership rule.** A design or doctrine that no single controller owns
> lives here, at family level. A controller's book references these documents
> — it never restates them. When a controller's book and a family doc
> disagree, the family doc wins and the book is the defect.

| Doc | Owns | Status |
|---|---|---|
| [common_has/](common_has/common_has_index.md) | the overarching HAS: the layer-stack architecture, the descriptor seam, the DFI generation naming, doctrines 6–11, the product/research line-up | v0.1 partner-review draft |
| [common_mas/](common_mas/common_mas_index.md) | per-block MAS: `mc_common_pkg`, the eight layers, and the shared FUBs inside their owning layer's chapter | v0.1 partner-review draft |
| [01_mem_ctrl_pkg.md](01_mem_ctrl_pkg.md) | the shared-core design: memtype enum, shared timing-struct inventory, migration plan with conditions | v0.1 design record |
| [02_family_doctrine.md](02_family_doctrine.md) | the five doctrines every controller book follows | v0.1 |
| [03_dfi_boundary_lineage.md](03_dfi_boundary_lineage.md) | the DFI 2.1 → 3.1 → 4.0 boundary story | v0.1 stub (pointers only) |
| [04_jedec_generation_deltas.md](04_jedec_generation_deltas.md) | the DDR2→3→4 / LPDDR2→3→4 reuse argument | v0.1 stub (pointers only) |

: Table 0.0: The family documents and what each owns

The andesite docs tranche (2026-10-03 spec) seeded this directory; the
Phase-2 campaign added the two books. RTL lives in `common-ip/rtl/`; the
knobs inventories (`mc_*_knobs.md`) record each block's parameter surface.
