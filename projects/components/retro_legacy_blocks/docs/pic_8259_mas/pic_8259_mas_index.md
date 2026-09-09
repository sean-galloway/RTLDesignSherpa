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

# pic_8259 MAS -- Micro Architecture Specification

**Component:** APB 8259A-Compatible Programmable Interrupt Controller
**Version:** 1.1
**Last Updated:** 2026-09-09
**Status:** RTL Functional -- acknowledge by read (PIC_INTA), live ISR with
fully nested priority, all EOI/rotation variants, special mask mode, strict
address decode with PSLVERR and a synchronized `irq_in` (issue #50 fixes,
2026-09-09). Cascade, buffered mode, SFNM and OCW3 poll/read-select are
software-visible storage only.

## Overview

This is the micro-architecture specification for the pic_8259, an APB
8259A-compatible Programmable Interrupt Controller. The register interface
and the interrupt semantics are validated; every chapter in this set
describes the RTL as it exists -- not the 8259A you remember from the
datasheet. Where the two part ways (there is no INTA pin, so the acknowledge
is a read; there is no cascade, so ICW3 is storage) the text says so, plainly.

![PIC 8259 Block Diagram](assets/svg/pic_8259_top.png)

### Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-12-01 | RTL Design Sherpa | Initial specification |
| 1.1 | 2026-09-09 | RTL Design Sherpa | Issue #50 fixes: PIC_INTA acknowledge-by-read with pre-acknowledge vector and spurious IRQ7, live ISR (nesting, non-specific/specific/rotating EOI, set-priority, one-shot rotate-on-AEOI), in-service and special-mask blocking rules, single-copy IMR, OCW2/OCW3 gated on init_complete and pic_enable, edge-taken init_mode with hardware-precedence auto-clear, strict decode with PSLVERR (no aliases), SYNC_STAGES irq_in synchronizer; storage-only fields stated |

## Navigation

> Status (2026-07-22): Only the Chapter 1 overview and the Chapter 5 register map exist
> in this tree today. The remaining chapters listed below are planned but not yet
> written; they are shown without links.

### Chapter 1: Overview
- [01_overview.md](ch01_overview/01_overview.md) - Component overview
- 02_architecture.md - Architecture *(planned, not yet written)*

### Chapter 2: Blocks
- 00_overview.md - Block hierarchy *(planned, not yet written)*

### Chapter 3: Interfaces
- 00_overview.md - Interface summary *(planned, not yet written)*

### Chapter 4: Programming Model
- 00_overview.md - Programming overview *(planned, not yet written)*

### Chapter 5: Registers
- [01_register_map.md](ch05_registers/01_register_map.md) - Register map
