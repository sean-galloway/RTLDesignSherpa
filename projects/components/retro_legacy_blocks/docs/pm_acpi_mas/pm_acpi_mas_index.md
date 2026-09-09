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

# pm_acpi MAS -- Micro Architecture Specification

**Component:** APB Power Management / ACPI Controller
**Version:** 1.0
**Last Updated:** 2025-12-01
**Status:** RTL Partial -- the register layout is validated, but GPE status,
the W1C status fields, power-button wake and RESET_STATUS are non-functional
or deviant in the current RTL. Read the Chapter 5 Design Notes and issue #54
before you trust any of them.

---

## Overview

> Status (2026-07-22): Only the Chapter 1 overview and the Chapter 5 register
> map exist in this tree today. The remaining chapters listed below are planned
> but not yet written; they are shown without links.

### Block Diagram

![PM/ACPI Block Diagram](assets/svg/pm_acpi_top.png)

### Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-12-01 | RTL Design Sherpa | Initial specification |

---

## Navigation

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
