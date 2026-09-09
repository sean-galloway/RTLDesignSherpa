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
**Version:** 1.0
**Last Updated:** 2025-12-01
**Status:** RTL Partial -- register interface validated; ISR/INTA/cascade
are inert, the ISR-clearing half of EOI is inert while its ROTATION side
effects stay live (0xA0 pins the priority base to 0), and edge-mode IRR
has no clear-on-acknowledge (see the implementation notes and issue #50)

## Overview

This is the micro-architecture specification for the pic_8259, an APB
8259A-compatible Programmable Interrupt Controller. Read the status line
above twice before you design against anything in here. The register
interface is validated; several classic-8259A behaviors are not, and every
chapter in this set is written to describe the RTL as it exists -- not the
8259A you remember from the datasheet. Where a register name implies a
feature the hardware doesn't have, the text says so, plainly.

![PIC 8259 Block Diagram](assets/svg/pic_8259_top.png)

### Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-12-01 | RTL Design Sherpa | Initial specification |

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
