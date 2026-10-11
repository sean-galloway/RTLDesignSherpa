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

# Document Information

| Field | Value |
|---|---|
| Document | mem-ctrl-ip Common IP — Micro-Architecture Specification |
| Version | 0.1 |
| Date | 2026-10-10 |
| Status | Partner-review draft, land-and-review with the common_has v0.1 book |
| Owner | mem-ctrl-ip family (common-ip/docs/) |
| Scope | One chapter per common block: package, eight layers, and the shared FUBs inside their owning layer's chapter |

## Revision history

| Version | Date | Change |
|---|---|---|
| 0.1 | 2026-10-10 | First edition, written against the Phase-2 extraction as landed: `mc_common_pkg`, eight layers (`mc_axi4_layer`, `mc_storage_layer`, `mc_scheduler_layer`, `mc_training_layer`, `mc_ras_layer`, `mc_dfi_2p1_layer`, `mc_dfi_3p1_layer`, `mc_dfi_4p0_layer`), and seventeen shared FUBs. Skeleton blocks (`mc_ras_layer`, `mc_training_layer` shell, per-generation DFI deltas) are documented honestly thin. |

## Chapter conventions

- RTL citations use `path:line` against `common-ip/rtl/` unless noted.
- Provenance citations use the rock books (`pumice_mas`, `scoria_mas`,
  `andesite_mas`) and the rock bug/issue records (pumice BUG-021, scoria
  BUG-001/002, ISSUE-002, and the campaign ledger).
- Parameter/knob detail lives in the knobs inventories
  (`mc_*_knobs.md` beside this book) and is summarized, not duplicated.
- The evidentiary rule (index "Read this first") applies to every chapter.
