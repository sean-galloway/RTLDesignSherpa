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


# GATLING-RV32ITETRAD Micro-Architecture Specification Index

**Version:** 0.1
**Date:** 2026-10-22
**Purpose:** Block-level micro-architecture specification for gatling, the four-context barrel RV32I

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Machine Organization](ch01_overview/01_overview.md)

### Chapter 2: Functional Blocks

- [gatling_core (top)](ch02_blocks/01_gatling_core.md)
- [gatling_regfile](ch02_blocks/02_gatling_regfile.md)
- [gatling_mem_bram](ch02_blocks/03_gatling_mem_bram.md)

### Chapter 3: Internal Interfaces

- [The Memory Contract](ch03_interfaces/01_memory_contract.md)

### Chapter 4: Micro-Architecture Behavior

- [The Rotation](ch04_behavior/01_the_rotation.md)

### Chapter 5: Verification

- [DV and Formal](ch05_verification/01_verification.md)

### Chapter 6: Configuration

- [Parameters and Filelists](ch06_configuration/01_configuration.md)

### Chapter 7: Board Result

- [Nexys A7-100T](ch07_board/01_board_result.md)

---

## Related Documentation

- **[GATLING HAS](../gatling_has/gatling_has_index.md)** - Hardware Architecture Specification (external view)
- **[The Barrel Model](../barrel_model/barrel_model.md)** - Why four contexts
- **[KESTREL MAS](../../../kestrel-rv32i/docs/kestrel_mas/kestrel_mas_index.md)** - The decode, immediate and ALU blocks gatling reuses
- **[GATLING PRD](../../PRD.md)** - Requirements and owner decisions
- **[Reading list](../../../references/microarchitecture-papers.md)** - The barrel's primary sources (entries 16-20) and the textbook chapters cited

---

**Last Updated:** 2026-10-22
**Maintained By:** RTL Design Sherpa Project
