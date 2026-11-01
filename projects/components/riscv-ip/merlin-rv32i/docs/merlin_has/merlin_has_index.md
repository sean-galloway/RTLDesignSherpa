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

# MERLIN-RV32I Hardware Architecture Specification Index

**Version:** 0.1
**Date:** 2026-11-01
**Purpose:** High-level hardware architecture specification for the merlin-rv32i 5-stage pipelined RV32I core

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
- [Programmer-Visible Machine State](ch03_architecture/02_machine_state.md)

### Chapter 4: Interfaces

- [merlin_core Port Specification](ch04_interfaces/01_core_port_spec.md)
- [Memory Contract](ch04_interfaces/02_memory_contract.md)
- [Halt and Trap Behavior](ch04_interfaces/03_halt_and_trap_behavior.md)

### Chapter 5: Performance

- [Performance Characteristics](ch05_performance/01_performance.md)

### Chapter 6: Integration

- [Integration Guide](ch06_integration/01_integration.md)

---

## Related Documentation

- **[MERLIN MAS](../merlin_mas/merlin_mas_index.md)** - Micro-Architecture Specification (block-level implementation)
- **[KESTREL HAS](../../../kestrel-rv32i/docs/kestrel_has/kestrel_has_index.md)** - Hardware Architecture Specification for the single-cycle predecessor
- **[RISC-V Falcon Suite README](../../../README.md)** - Suite overview and rung ladder
- **[RISC-V Unprivileged ISA](../../../references/riscv-spec.pdf)** - ISA authority (cited by chapter)
- **[Testplans](../../../kestrel-rv32i/dv/testplans/README.md)** - V&V cross-reference (kestrel predecessor; merlin testplans to follow)

---

**Last Updated:** 2026-11-01
**Maintained By:** RTL Design Sherpa Project
