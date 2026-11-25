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

# PEREGRINE-RV32IM Hardware Architecture Specification Index

**Version:** 0.1
**Date:** 2026-11-25
**Purpose:** High-level hardware architecture specification for the peregrine-rv32im pipelined RV32IM core with branch prediction, precise machine-mode traps and split L1 caches

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose and Scope](ch01_introduction/01_purpose_and_scope.md)

### Chapter 2: System Overview

- [System Overview and Context](ch02_system_overview/01_system_overview.md)

### Chapter 3: Architecture

- [ISA Scope](ch03_architecture/01_isa_scope.md)
- [Programmer-Visible Machine State and Traps](ch03_architecture/02_machine_state.md)
- [Address Map](ch03_architecture/03_address_map.md)

### Chapter 4: Interfaces

- [peregrine_core Port Specification](ch04_interfaces/01_core_port_spec.md)
- [peregrine_top Port Specification](ch04_interfaces/02_top_port_spec.md)
- [Memory Contract](ch04_interfaces/03_memory_contract.md)
- [Trap and Interrupt Behavior](ch04_interfaces/04_trap_and_interrupt_behavior.md)

### Chapter 5: Performance

- [Performance Characteristics](ch05_performance/01_performance.md)

### Chapter 6: Integration

- [Integration Guide](ch06_integration/01_integration.md)

### Chapter 7: Verification

- [Verification Summary](ch07_verification/01_verification_summary.md)

---

## Related Documentation

- **[PEREGRINE MAS](../peregrine_mas/peregrine_mas_index.md)** - Micro-Architecture Specification (block-level implementation)
- **[PEREGRINE PRD](../../PRD.md)** - Requirements and the P1-P14 decision rows
- **[RISC-V Falcon Suite README](../../../README.md)** - Suite overview and rung ladder
- **[MERLIN HAS](../../../merlin-rv32i/docs/merlin_has/merlin_has_index.md)** - The 5-stage predecessor peregrine extends

---

**Last Updated:** 2026-11-25
**Maintained By:** RTL Design Sherpa Project
