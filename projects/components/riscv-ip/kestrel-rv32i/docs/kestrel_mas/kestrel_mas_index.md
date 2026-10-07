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

# KESTREL-RV32I Micro-Architecture Specification Index

**Version:** 0.1
**Date:** 2026-10-07
**Purpose:** Block-level micro-architecture specification for the kestrel-rv32i single-cycle RV32I core

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Design Philosophy and Machine Organization](ch01_overview/01_overview.md)

### Chapter 2: Functional Blocks

- [kestrel_core (top)](ch02_blocks/01_kestrel_core.md)
- [kestrel_decode](ch02_blocks/02_kestrel_decode.md)
- [kestrel_imm_gen](ch02_blocks/03_kestrel_imm_gen.md)
- [kestrel_alu](ch02_blocks/04_kestrel_alu.md)
- [kestrel_regfile](ch02_blocks/05_kestrel_regfile.md)
- [kestrel_mem_loader](ch02_blocks/06_kestrel_mem_loader.md)

### Chapter 3: Internal Interfaces

- [Package Types and Top-Level Wiring](ch03_interfaces/01_package_and_wiring.md)

### Chapter 4: Micro-Architecture Behavior

- [The Single Cycle, Step by Step](ch04_behavior/01_the_single_cycle.md)
- [Cross-Word Misaligned Retry](ch04_behavior/02_misaligned_retry.md)
- [Halt, IALIGN, and the System Layer](ch04_behavior/03_halt_ialign_csr.md)
- [RVFI Aggregation](ch04_behavior/04_rvfi_aggregation.md)

### Chapter 5: Verification Hooks

- [Verification Hooks and Observability](ch05_verification/01_verification_hooks.md)

### Chapter 6: Configuration

- [Parameters, Defines, and Filelists](ch06_configuration/01_configuration.md)

---

## Related Documentation

- **[KESTREL HAS](../kestrel_has/kestrel_has_index.md)** - Hardware Architecture Specification (external view)
- **[Simplified RV32I: kestrel](../simplified_rv32i/simplified_rv32i_index.md)** - Tutorial-study book this core is documented by
- **[RISC-V Falcon Suite README](../../../README.md)** - Suite overview and rung ladder
- **[riscv-formal rvfi.md](../../../../../../vendor/riscv-formal/docs/rvfi.md)** - Retire-channel field semantics
- **[Testplans](../../dv/testplans/README.md)** - V&V cross-reference (six plans)

---

**Last Updated:** 2026-10-07
**Maintained By:** RTL Design Sherpa Project
