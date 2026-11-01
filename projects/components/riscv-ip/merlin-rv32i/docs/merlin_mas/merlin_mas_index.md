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

# MERLIN-RV32I Micro-Architecture Specification Index

**Version:** 0.1
**Date:** 2026-11-01
**Purpose:** Block-level micro-architecture specification for the merlin-rv32i 5-stage pipelined RV32I core

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Design Philosophy and Machine Organization](ch01_overview/01_overview.md)

### Chapter 2: Functional Blocks

- [merlin_core (top)](ch02_blocks/01_merlin_core.md)
- [rv32i_decode](ch02_blocks/02_rv32i_decode.md)
- [rv32i_imm_gen](ch02_blocks/03_rv32i_imm_gen.md)
- [rv32i_alu](ch02_blocks/04_rv32i_alu.md)
- [kestrel_regfile](ch02_blocks/05_kestrel_regfile.md)
- [merlin_if_id](ch02_blocks/06_merlin_if_id.md)
- [merlin_id_ex](ch02_blocks/07_merlin_id_ex.md)
- [merlin_ex_mem](ch02_blocks/08_merlin_ex_mem.md)
- [merlin_mem_wb](ch02_blocks/09_merlin_mem_wb.md)
- [merlin_hazard](ch02_blocks/10_merlin_hazard.md)

### Chapter 3: Internal Interfaces

- [Package Types and Top-Level Wiring](ch03_interfaces/01_package_and_wiring.md)

### Chapter 4: Micro-Architecture Behavior

- [The Pipelined Cycle, Step by Step](ch04_behavior/01_pipeline_cycle.md)
- [Hazard Detection and Operand Forwarding](ch04_behavior/02_hazard_forwarding.md)
- [Branch Resolution and Flush](ch04_behavior/03_branch_flush.md)
- [Load-Use Interlock](ch04_behavior/04_load_use_interlock.md)
- [RVFI Aggregation](ch04_behavior/05_rvfi_aggregation.md)

### Chapter 5: Verification Hooks

- [Verification Hooks and Observability](ch05_verification/01_verification_hooks.md)

### Chapter 6: Configuration

- [Parameters, Defines, and Filelists](ch06_configuration/01_configuration.md)

---

## Related Documentation

- **[MERLIN HAS](../merlin_has/merlin_has_index.md)** - Hardware Architecture Specification (external view)
- **[KESTREL MAS](../../../kestrel-rv32i/docs/kestrel_mas/kestrel_mas_index.md)** - Micro-Architecture Specification for the single-cycle predecessor
- **[RISC-V Falcon Suite README](../../../README.md)** - Suite overview and rung ladder
- **[riscv-formal rvfi.md](../../../../../../vendor/riscv-formal/docs/rvfi.md)** - Retire-channel field semantics
- **[Testplans](../../../kestrel-rv32i/dv/testplans/README.md)** - V&V cross-reference (kestrel predecessor; merlin testplans to follow)

---

**Last Updated:** 2026-11-01
**Maintained By:** RTL Design Sherpa Project
