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

# Reed-Solomon Codec Micro-Architecture Specification Index

## Overview

**Version:** 0.1 (draft)
**Date:** 2026-10-04
**Purpose:** Micro-architecture specification — the HAS taken one level down:
per-block signal tables, cycle behavior, FSM policy, and verification
references for the Reed-Solomon codec component
(`projects/components/ecc-ip/reed-solomon/`). Written against the landed RTL;
the `.sv` files are the ground truth this document cites.

---

## Related Modules

Listed as paths, not links: the document build inlines every Markdown link in
this index, and these are companions, not chapters.

- **PRD** - `projects/components/ecc-ip/reed-solomon/PRD.md` - product requirements: the decision table and candidate profiles
- **HAS** - `projects/components/ecc-ip/reed-solomon/docs/reed_solomon_has/reed_solomon_has_index.md` - high-level architecture: block diagram, data flow, solver options, interfaces, parameters
- **FUB catalog** - `projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md` - every block bottom-up with what it instantiates, as planned; this MAS is the landed-RTL check on it
- **References** - `projects/components/ecc-ip/reed-solomon/References/README.md` - standards and papers, with source and licence
- **CLAUDE.md** - `projects/components/ecc-ip/reed-solomon/CLAUDE.md` - area facts for a session working here

---

## Navigation

**Note:** Every chapter below is one source file; the document build assembles the spec from these links.

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview
- [Methodology](ch01_overview/01_methodology.md)
- [Block Inventory](ch01_overview/02_block_inventory.md)

### Chapter 2: Functional Blocks
- [Encoder Core](ch02_blocks/01_encoder.md)
- [Syndrome Unit](ch02_blocks/02_syndrome_unit.md)
- [Key Equation Solver — riBM](ch02_blocks/03_key_equation_solver_ribm.md)
- [Key Equation Solver — Euclidean](ch02_blocks/04_key_equation_solver_euclid.md)
- [Chien Search](ch02_blocks/05_chien_search.md)
- [Forney Evaluator](ch02_blocks/06_forney_evaluator.md)
- [Erasure Unit](ch02_blocks/07_erasure_unit.md)
- [Decoder Core Integration](ch02_blocks/08_decoder_core.md)

### Chapter 3: Interfaces
- [Core Signals](ch03_interfaces/01_core_signals.md)

### Chapter 4: Contracts and Verification
- [Signal Contracts and Golden Model](ch04_contracts/01_signal_contracts.md)

---
