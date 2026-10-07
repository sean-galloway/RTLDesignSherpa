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

# KESTREL-RV32I Hardware Architecture Specification Index

**Version:** 0.1
**Date:** 2026-10-07
**Purpose:** High-level hardware architecture specification for the kestrel-rv32i single-cycle RV32I core

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

- [kestrel_core Port Specification](ch04_interfaces/01_core_port_spec.md)
- [Memory Contract](ch04_interfaces/02_memory_contract.md)
- [Halt and Trap Behavior](ch04_interfaces/03_halt_and_trap_behavior.md)
- [kestrel_mem_loader and AXIL Programming Interface](ch04_interfaces/04_mem_loader.md)

### Chapter 5: Performance

- [Performance Characteristics](ch05_performance/01_performance.md)

### Chapter 6: Integration

- [Integration Guide](ch06_integration/01_integration.md)

---

## Related Documentation

- **[KESTREL MAS](../kestrel_mas/kestrel_mas_index.md)** - Micro-Architecture Specification (block-level implementation)
- **[Simplified RV32I: kestrel](../simplified_rv32i/simplified_rv32i_index.md)** - Tutorial-study book this core is documented by
- **[RISC-V Falcon Suite README](../../../README.md)** - Suite overview and rung ladder
- **[RISC-V Unprivileged ISA](../../../references/riscv-spec.pdf)** - ISA authority (cited by chapter)
- **[Testplans](../../dv/testplans/README.md)** - V&V cross-reference (six plans)

---

**Last Updated:** 2026-10-07
**Maintained By:** RTL Design Sherpa Project
