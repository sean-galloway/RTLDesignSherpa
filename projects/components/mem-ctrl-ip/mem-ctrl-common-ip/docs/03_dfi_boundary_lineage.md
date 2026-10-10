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

# DFI boundary lineage

**Version:** 0.1 (stub)
**Date:** 2026-10-04
**Status:** v0.1 stub — purpose and pointers only, per the docs tranche plan.
The 2.1 → 3.1 → 4.0 delta tables land when the andesite HAS ch04 work gives
them something to summarize.

## What this will own

The family-level story of the DFI boundary: what the 2.1 → 3.1 → 4.0
revisions changed at the controller/PHY seam, which controller drives which
revision, and what each generation's boundary costs and buys. Per the
ownership rule, each controller's ch04 stays authoritative for its own
interface — this doc is the lineage that lets a reader see the seam move
across the family without opening three books.

## Pointers until then

- pumice drives DFI 2.1: the DFI layer is
  `pumice-ddr2-lpddr2/rtl/macro/pumice_dfi_layer.sv`.
- scoria's ch04 is the 3.1 reference, including the v2.1.1 delta it inherited:
  `scoria-ddr3-lpddr3/docs/scoria_has/ch04_interfaces/01_dfi_v31.md`.
- andesite's ch04 (`andesite-ddr4-lpddr4/docs/andesite_has/ch04_interfaces/`)
  owns the 4.0 boundary; the DFI 4.0 spec PDF is on disk in the operator's
  research storage (`/mnt/data/github/dfi-specs/`, cited 2026-10-04) and
  the study ran on 2026-10-04 as andesite TASK-005. Clause citations in
  the HAS ch04, MAS ch03, and HAS ch06 are now real DFI 4.0 section
  numbers; study corrections for the v3.1 → v4.0 chip-select rename, the
  missing `dfi_wrdata_dbi` pin, and the `dfi_init`/`dfi_ca_capture`
  mismatches are recorded in those files. The in-house BFM gap list and
  integration note are in HAS ch06; the task record is
  `vault/Tasks/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/task/open/TASK-005.md`.
- andesite's foundation document, `scoria-ddr3-lpddr3/docs/design-requirements.md`,
  is where the boundary was argued against the actual revisions.
