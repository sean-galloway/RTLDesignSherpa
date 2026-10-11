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

**Version:** 0.1
**Date:** 2026-10-10
**Status:** v0.1. One chapter per common block. The architecture these blocks
implement — the layer stack, the descriptor seam, the doctrines — is the
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

### Chapter 2: `mc_axi4_layer` and the Host-Side FUBs

- [`mc_axi4_layer` — AXI slaves, intakes, coalescing, return ring](ch02_axi4_layer/01_mc_axi4_layer.md)

### Chapter 3: `mc_storage_layer` and the Entry-Pool FUBs

- [`mc_storage_layer` — CAMs, read snooping, bank image](ch03_storage_layer/01_mc_storage_layer.md)

### Chapter 4: `mc_scheduler_layer` and the Pick Machinery

- [`mc_scheduler_layer` — schedulable-entry view, timers, arbiter](ch04_scheduler_layer/01_mc_scheduler_layer.md)

### Chapter 5: `mc_training_layer`

- [`mc_training_layer` — shell, maintenance slot, rock wrappers](ch05_training_layer/01_mc_training_layer.md)

### Chapter 6: `mc_ras_layer`

- [`mc_ras_layer` — skeleton, transform pair, reserved CSR surface](ch06_ras_layer/01_mc_ras_layer.md)

### Chapter 7: `mc_dfi_2p1_layer` and the Shared DFI Pipeline

- [`mc_dfi_2p1_layer` — DFI 2.1 command/data pipeline + CDC](ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md)

### Chapter 8: `mc_dfi_3p1_layer`

- [`mc_dfi_3p1_layer` — the 3.1 generation delta](ch08_dfi_3p1_layer/01_mc_dfi_3p1_layer.md)

### Chapter 9: `mc_dfi_4p0_layer`

- [`mc_dfi_4p0_layer` — the 4.0 generation delta](ch09_dfi_4p0_layer/01_mc_dfi_4p0_layer.md)
