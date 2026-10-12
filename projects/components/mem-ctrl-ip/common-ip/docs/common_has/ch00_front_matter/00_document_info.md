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
| Document | mem-ctrl-ip Family — Overarching Hardware Architecture Specification |
| Version | 0.1 |
| Date | 2026-10-10 |
| Status | Partner-review draft — the owner reads and comments before scoria/andesite books are moved to this stack |
| Owner | mem-ctrl-ip family (common-ip/docs/) |
| Audience | Anyone building, porting, or productizing a family memory controller |
| Binding force | Family level: controller books reference this; they never restate it |

## Revision history

| Version | Date | Change |
|---|---|---|
| 0.1 | 2026-10-10 | First edition. The Phase-2 common-IP campaign (2026-10-09 → 2026-10-10) extracted the shared package, eight planes, and seventeen FUBs into common-ip; this book records the architecture those blocks implement — the partner's planeed-stack vision — as the family's binding contract. Doctrines added by the campaign are Chapter 4; the original five doctrines remain in [02_family_doctrine.md](../../02_family_doctrine.md) and are not restated. |

## Related documents

| Document | Relationship |
|---|---|
| [common_mas](../../common_mas/common_mas_index.md) | the per-block microarchitecture of every block this book names |
| [02_family_doctrine.md](../../02_family_doctrine.md) | the original five doctrines; Chapter 4 adds to them, never replaces them |
| [01_mem_ctrl_pkg.md](../../01_mem_ctrl_pkg.md) | the shared package design (memtype enum, shared types) |
| [03_dfi_boundary_lineage.md](../../03_dfi_boundary_lineage.md) | the DFI 2.1 → 3.1 → 4.0 boundary story this book's Chapter 3 summarizes |
| Rock HAS/MAS books (pumice, scoria, andesite) | per-rock instantiations of this architecture; deltas recorded there, not here |
