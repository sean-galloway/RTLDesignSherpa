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

# andesite DDR4/LPDDR4 Family Controller — Hardware Architecture Specification

**Version:** 0.1
**Date:** 2026-10-03
**Status:** v0.1, written from the delta analysis before RTL exists, per the
spec. No RTL exists for andesite; every block here is specified, not
described. Every block is marked **INHERITED**, **MODIFIED** or **NEW**
against the scoria DDR3/LPDDR3 controller, which is the architecture andesite
is derived from and whose books, CSR flow and verification apparatus are the
reuse pool.

**Foundation:** `../../../../../../docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md`
— the bootstrap design spec (amended: shared-core design and doctrine moved to
family level). That document is binding on this one; where the two disagree,
it is a defect in this one. The family docs
(`../../../docs/`) carry what no single controller owns: the
`mem_ctrl_pkg` shared-core design, the family doctrine, the DFI boundary
lineage, the JEDEC generation deltas.

> **Read this first.** A specification written before the RTL can be wrong in
> a way a description cannot: it can specify something unbuildable. Every
> claim here is therefore either (a) inherited from scoria, where it is built
> and measured, (b) cited to a JEDEC or DFI clause, or (c) recorded as an
> open question in Chapter 6. No DFI 4.0 spec exists on disk: any DFI 4.0
> claim whose clause can't be verified in-house is suffixed `§TBC(TASK-005)`
> — a named task confirms or corrects it. Nothing else is asserted.

---

## Provenance and what is settled

| Decision | Settled as | Where |
|---|---|---|
| PHY boundary | DFI 4.0 (ACT_n, gear-down, CA parity/`alert_n`, DBI wires); the BFM is andesite TASK-005 | Ch 4 |
| Design point | DDR4-1600 x8, 4 bank groups x 4 banks = 16 banks (MT40A1G8-class); LPDDR4-1600 x16, 8 banks per channel; timings runtime CSRs | Ch 2.4 |
| Book shape | One DDR4-led book, LPDDR4 per-chapter deltas, sim-only (no board — 7-series targets carry no DDR4) | Ch 2 |
| Shared core | `mem_ctrl_pkg` design lives at family level (`mem-ctrl-ip/docs/`); this book references it | Ch 1.2, Ch 5 |
| Kmap depth | Command-encoding focused, generated with `bin/kmaps` | andesite TASK-004 |

: Table 0.0: Settled decisions binding on this specification

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose and Scope](ch01_introduction/01_purpose.md)
- [Document Conventions](ch01_introduction/02_conventions.md)
- [Definitions and Acronyms](ch01_introduction/03_definitions.md)

### Chapter 2: System Overview

- [Scope and Goals](ch02_overview/01_scope.md)
- [Block Diagram](ch02_overview/02_block_diagram.md)
- [Module Hierarchy](ch02_overview/03_module_hierarchy.md)
- [The Target Design Point](ch02_overview/04_design_point.md)

### Chapter 3: Architecture

- [What Is Inherited, and the Ten Areas That Change](ch03_architecture/01_deltas.md)
- [Init and ZQ: RESET#, MR0-MR6, Gear-Down](ch03_architecture/02_init_zq.md)
- [Training: Write Leveling Inherited, Read Leveling New](ch03_architecture/03_training.md)
- [Refresh: FGR and Controller-Directed Per-Bank](ch03_architecture/04_refresh.md)
- [ODT: Dynamic, with a New odt_ctrl](ch03_architecture/05_odt.md)
- [The LPDDR4 Deltas, Chapter by Chapter](ch03_architecture/06_lpddr4_deltas.md)

### Chapter 4: Interfaces

- [DFI v4.0 Master Interface, and the v3.1 Delta](ch04_interfaces/01_dfi_v40.md)
- [AXI4 Slave and APB CSR (both inherited)](ch04_interfaces/02_axi4_apb.md)

### Chapter 5: Parameters

- [andesite_pkg, and Build-Time vs Runtime](ch05_parameters/01_package_and_params.md)

### Chapter 6: Integration

(lands with Task 7)

- `ch06_integration/01_verification_open.md` — Verification Strategy, and the Open Questions

---

## Figures

| Figure | Source | Subject |
|---|---|---|
| 2.1 | `assets/mermaid/01_block_diagram.mmd` | the controller, with each block colour-marked inherited / modified / new against scoria |

: Table 0.1: Figures and their sources
