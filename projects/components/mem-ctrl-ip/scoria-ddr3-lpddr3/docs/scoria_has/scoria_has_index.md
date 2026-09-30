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

# scoria DDR3/LPDDR3 Family Controller — Hardware Architecture Specification

**Version:** 0.7
**Date:** 2026-09-29
**Status:** v0.4, pre-RTL. **No open questions remain** -- Q1-Q5 are answered or struck (Ch 6). This document SPECIFIES the controller; it
does not describe an implementation, because there is none yet. Every block is
marked **INHERITED**, **MODIFIED** or **NEW** against the pumice DDR2/LPDDR2
controller, which is the architecture scoria is derived from.

**Foundation:** `../design-requirements.md` — the delta analysis against
JESD79-3F, JESD209-3C, DFI v3.1 and DFI v2.1.1, with decisions D1-D3 settled.
That document is binding on this one; where the two disagree, it is a defect in
this one.

> **Read this first.** A specification written before the RTL can be wrong in a
> way a description cannot: it can specify something unbuildable. Every claim
> here is therefore either (a) inherited from pumice, where it is already
> built and measured, (b) cited to a JEDEC or DFI clause, or (c) explicitly
> marked as an open question in Chapter 6. Nothing else is asserted.

---

## Provenance and what is settled

| Decision | Settled as | Where |
|---|---|---|
| DFI revision | v3.1; its DDR4/LPDDR4 surface stays unimplemented | Ch 4 |
| Write leveling | firmware-driven; no hardware calibration FSM | Ch 3, Ch 6 |
| Package | own `scoria_pkg`; shared family package when DDR4 starts | Ch 5 |
| Target design point | Genesys 2, K7DDRPHY, 2 x MT41J256M16, DDR3-800, 3200 MB/s peak | Ch 2.4 |

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

- [What Is Inherited, and the Three Blocks That Change](ch03_architecture/01_deltas.md)
- [Init Sequencer: RESET#, MR0-MR3, ZQ Calibration](ch03_architecture/02_init_zq.md)
- [Write Leveling: the Interface, Not the Search](ch03_architecture/03_write_leveling.md)
- [Refresh: DDR3 All-Bank and LPDDR3 Per-Bank](ch03_architecture/04_refresh.md)

### Chapter 4: Interfaces

- [DFI v3.1 Master Interface, and the v2.1.1 Delta](ch04_interfaces/01_dfi_v31.md)
- [AXI4 Slave and APB CSR (both inherited)](ch04_interfaces/02_axi4_apb.md)

### Chapter 5: Parameters

- [scoria_pkg, and Build-Time vs Runtime](ch05_parameters/01_package_and_params.md)

### Chapter 6: Integration

- [Verification Strategy, and the Open Questions](ch06_integration/01_verification_open.md)

---

## Figures

| Figure | Source | Subject |
|---|---|---|
| 2.1 | `assets/graphviz/01_block_diagram.dot` | the controller, with each block marked inherited / modified / new |

: Table 0.1: Figures and their sources
