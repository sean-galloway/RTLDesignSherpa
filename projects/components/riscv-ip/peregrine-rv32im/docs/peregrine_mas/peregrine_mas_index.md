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

# PEREGRINE-RV32IM Micro-Architecture Specification Index

**Version:** 0.1
**Date:** 2026-11-25
**Purpose:** Block-level micro-architecture specification for the peregrine-rv32im pipelined RV32IM core: the predictor, the trap machinery, the M unit, the caches and the cycle rules that tie them together

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Design Philosophy and Machine Organization](ch01_overview/01_overview.md)

### Chapter 2: Functional Blocks

- [peregrine_core (top)](ch02_blocks/01_peregrine_core.md)
- [peregrine_bpred](ch02_blocks/02_peregrine_bpred.md)
- [peregrine_csr](ch02_blocks/03_peregrine_csr.md)
- [peregrine_mdu](ch02_blocks/04_peregrine_mdu.md)
- [peregrine_hazard](ch02_blocks/05_peregrine_hazard.md)
- [Pipeline Registers](ch02_blocks/06_pipeline_registers.md)
- [peregrine_icache](ch02_blocks/07_peregrine_icache.md)
- [peregrine_top (D-side wrapper)](ch02_blocks/08_peregrine_top.md)
- [peregrine_clint](ch02_blocks/09_peregrine_clint.md)
- [peregrine_uc_axi](ch02_blocks/10_peregrine_uc_axi.md)
- [peregrine_axi4_arb](ch02_blocks/11_peregrine_axi4_arb.md)
- [Shared Blocks](ch02_blocks/12_shared_blocks.md)

### Chapter 3: Internal Interfaces

- [Package Types and Encodings](ch03_interfaces/01_package_and_wiring.md)

### Chapter 4: Micro-Architecture Behavior

- [The Pipelined Cycle](ch04_behavior/01_pipeline_cycle.md)
- [Hazards, Forwarding and Interlocks](ch04_behavior/02_hazards_forwarding.md)
- [Branch Prediction and Recovery](ch04_behavior/03_branch_prediction.md)
- [Traps, Interrupts and the Commit Point](ch04_behavior/04_traps.md)
- [The M Unit and Hold-in-EX](ch04_behavior/05_m_unit.md)
- [The D Side: Loads in MEM, Holds and Early Responses](ch04_behavior/06_d_side.md)
- [fence.i](ch04_behavior/07_fence_i.md)
- [RVFI Aggregation](ch04_behavior/08_rvfi.md)

### Chapter 5: Verification Hooks

- [Verification Hooks and Observability](ch05_verification/01_verification_hooks.md)

### Chapter 6: Configuration

- [Parameters, Defines and Filelists](ch06_configuration/01_configuration.md)

---

## Related Documentation

- **[PEREGRINE HAS](../peregrine_has/peregrine_has_index.md)** - Hardware Architecture Specification (external view)
- **[PEREGRINE PRD](../../PRD.md)** - Requirements and the P1-P14 decision rows
- **[MERLIN MAS](../../../merlin-rv32i/docs/merlin_mas/merlin_mas_index.md)** - The five-stage predecessor
- **[RISC-V Falcon Suite README](../../../README.md)** - Suite overview and rung ladder

---

**Last Updated:** 2026-11-25
**Maintained By:** RTL Design Sherpa Project
