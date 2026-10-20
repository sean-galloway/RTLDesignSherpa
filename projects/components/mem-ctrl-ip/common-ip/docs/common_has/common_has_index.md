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

# mem-ctrl-ip Family — Overarching Hardware Architecture Specification

**Version:** 0.2
**Date:** 2026-10-20
**Status:** v0.1, the vision edition. This book is the family-level HAS: the
plane-stack architecture the partner set out during the Phase-2 common-IP
campaign, written down as the binding contract the rocks and the products are
built against. The per-block microarchitecture lives in
[common_mas](../common_mas/common_mas_index.md); this book owns the shape of
the whole and the rules no single block owns.

> **Read this first.** A controller book (pumice/scoria/andesite HAS/MAS) and
> a family doc disagree → the family doc wins and the book is the defect. That
> rule predates this book (the family INDEX states it); this book is one of
> the docs it protects. Every claim here is either (a) measured in a named
> rock, (b) a cited JEDEC/DFI clause, or (c) an explicitly marked open
> question. Nothing else is asserted.

> **Warning:** every timing CSR in this family is a count of MC-clock cycles,
> correct only at the MC clock frequency it was derived for. A frequency
> change invalidates the whole timing set at once; software must re-derive
> and reprogram it before traffic resumes. Stale values present as data
> corruption, not errors. Each rock's HAS carries this warning at the
> register map; this book makes it family doctrine (Ch 4).

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose, Scope, and the Two Lines](ch01_introduction/01_purpose.md)

### Chapter 2: The Plane Stack

- [The Architecture: axi4 → storage → scheduler → (ras) → training → dfi](ch02_architecture/01_plane_stack.md)
- [The Descriptor Seam](ch02_architecture/02_descriptor_seam.md)

### Chapter 3: The DFI Generations

- [Why `dfi_2p1_plane` / `dfi_3p1_plane` / `dfi_4p0_plane` Are Separate Blocks](ch03_dfi_generations/01_dfi_planes.md)

### Chapter 4: Doctrines Added by the Common-IP Campaign

- [New Family Doctrines](ch04_doctrine/01_new_doctrines.md)

### Chapter 5: The Line-Up

- [The common-ip Layout](ch05_lineup/01_common_ip_layout.md)
- [Products and Research: granite / gabbro / diorite](ch05_lineup/02_products_and_research.md)
