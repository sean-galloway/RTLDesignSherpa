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

# Binary BCH Codec Micro-Architecture Specification Index

## Overview

**Version:** 0.1 (draft)
**Date:** 2026-10-03
**Purpose:** Micro-architecture specification — the HAS taken one level down:
per-block signal tables, cycle behavior, FSM policy, and signal-contract
references for the Binary BCH codec component
(`projects/components/ecc-ip/bch/`).

---

## Related Modules

Listed as paths, not links: the document build inlines every Markdown link in
this index, and these are companions, not chapters.

- **PRD** - `projects/components/ecc-ip/bch/PRD.md` - product requirements: the decision table and candidate profiles
- **HAS** - `projects/components/ecc-ip/bch/docs/bch_has/bch_has_index.md` - high-level architecture: block diagram, data flow, solver options, interfaces, parameters
- **References** - `projects/components/ecc-ip/bch/References/README.md` - standards and papers, with source and licence
- **CLAUDE.md** - `projects/components/ecc-ip/bch/CLAUDE.md` - area facts for a session working here
- **Signal contracts** - `projects/components/ecc-ip/bch/docs/bch_signal_contracts.xlsx` - generated contract/kmap workbook

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
- [Key Equation Solver](ch02_blocks/03_key_equation_solver.md)
- [Chien Search](ch02_blocks/04_chien_search.md)
- [Decoder Core Integration](ch02_blocks/05_decoder_core.md)

### Chapter 3: Interfaces
- [Core Signals](ch03_interfaces/01_core_signals.md)

### Chapter 4: Signal Contracts
- [Signal Contracts and K-maps](ch04_contracts/01_signal_contracts.md)

---
