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

# mem-ctrl-ip Common IP — Micro-Architecture Specification

**Version:** 0.2
**Date:** 2026-10-20
**Status:** v0.1. One chapter per common block. The architecture these blocks
implement — the plane stack, the descriptor seam, the doctrines — is the
family HAS ([common_has](../common_has/common_has_index.md)); this book is
the per-block microarchitecture and never restates the architecture. Where
the two disagree, the HAS wins and this book is the defect.

> **Read this first.** Every claim in a chapter is one of: (a) read from the
> RTL it documents (cited `file:line`), (b) inherited from a named rock's
> measured history (cited to the rock's book or bug record), or (c) an
> explicitly marked open question. Nothing else is asserted. Silicon-bug
> history (`BUG-*`, `ISSUE-*`, measured regression numbers) is invariant
> documentation and is carried verbatim from the RTL comments.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: The Family Package

- [`mc_common_pkg` — types, memtype enum, shared opcodes](ch01_package/01_mc_common_pkg.md)

### Chapter 2: `mc_axi4_plane` and the Host-Side FUBs

- [`mc_axi4_plane` — AXI slaves, intakes, coalescing, return ring](ch02_axi4_plane/01_mc_axi4_plane.md)

### Chapter 3: `mc_storage_plane` and the Entry-Pool FUBs

- [`mc_storage_plane` — CAMs, read snooping, bank image](ch03_storage_plane/01_mc_storage_plane.md)

### Chapter 4: `mc_scheduler_plane` and the Pick Machinery

- [`mc_scheduler_plane` — schedulable-entry view, timers, arbiter](ch04_scheduler_plane/01_mc_scheduler_plane.md)

### Chapter 5: `mc_training_plane`

- [`mc_training_plane` — LPDDR2 clients, generic shell, maintenance slot](ch05_training_plane/01_mc_training_plane.md)

### Chapter 6: `mc_ras_plane`

- [`mc_ras_plane` — skeleton, transform pair, reserved CSR surface](ch06_ras_plane/01_mc_ras_plane.md)

### Chapter 7: `mc_dfi_2p1_plane` and the Shared DFI Pipeline

- [`mc_dfi_2p1_plane` — DFI 2.1 command/data pipeline + CDC](ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md)

### Chapter 8: `mc_dfi_3p1_plane`

- [`mc_dfi_3p1_plane` — the 3.1 generation delta](ch08_dfi_3p1_plane/01_mc_dfi_3p1_plane.md)

### Chapter 9: `mc_dfi_4p0_plane`

- [`mc_dfi_4p0_plane` — the 4.0 generation delta](ch09_dfi_4p0_plane/01_mc_dfi_4p0_plane.md)

### Chapter 10: `mc_init_plane`

- [`mc_init_plane` — JEDEC init, MR shadow, PHY handshake](ch10_init_plane/01_mc_init_plane.md)

> Command-flow order (per the family HAS plane stack) places the init plane
> between the storage plane and the scheduler plane; it is filed as chapter
> 10 so chapters 2–9 keep stable paths for inbound links. The architecture
> statement is the HAS stack, not the chapter number.
