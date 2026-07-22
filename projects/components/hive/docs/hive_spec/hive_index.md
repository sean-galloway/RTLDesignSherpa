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

# HIVE System Specification Index
**Hierarchical Intelligent Vector Environment**
Version 0.3 - Early Proof of Concept

---

## Document Organization

This specification is organized into five chapters covering HIVE's architecture, components, interfaces, programming models, and performance characteristics.

> Status (2026-07-22): only Chapter 1 (all sections) and Chapter 2.0 have been
> written as chapter files. The remaining sections (2.1-2.4, Chapters 3-5) are
> planned; their content currently lives in the single-file specification
> [../hive_specification.md](../hive_specification.md).

---

## Chapter 1: Overview

Provides high-level system architecture and design goals.

- **[1.1 Overview](ch01_overview/01_overview.md)** - Executive summary, system architecture, hierarchical organization
- **[1.2 Architectural Requirements](ch01_overview/02_architectural_requirements.md)** - Functional, performance, and educational requirements
- **[1.3 Clocks and Reset](ch01_overview/03_clocks_and_reset.md)** - Clock domains, frequencies, reset strategy
- **[1.4 Acronyms](ch01_overview/04_acronyms.md)** - Glossary of terms and abbreviations
- **[1.5 References](ch01_overview/05_references.md)** - Related specifications and external resources

---

## Chapter 2: Block Specifications

Detailed specifications for each HIVE component.

- **[2.0 Block Overview](ch02_blocks/00_overview.md)** - Component organization and resource budget
- **2.1 HIVE-C Master Controller** *(planned - see [hive_specification.md](../hive_specification.md) section 6)* - VexRiscv master controller specification
- **2.2 SERV Monitor** *(planned - see [hive_specification.md](../hive_specification.md) section 5)* - Per-tile traffic monitoring and control
- **2.3 Control Network** *(planned - see [hive_specification.md](../hive_specification.md) section 2)* - HIVE-C to SERV communication infrastructure
- **2.4 Configuration Manager** *(planned - see [hive_specification.md](../hive_specification.md) section 4)* - Network reconfiguration and context switching

---

## Chapter 3: Interface Specifications

Protocol specifications for HIVE interfaces.

*(Chapter 3 files are planned; interface content currently lives in [hive_specification.md](../hive_specification.md) sections 2-3.)*

- **3.1 Top-Level Interfaces** *(planned)* - System-level connections and signal definitions
- **3.2 AXIS Packet Classification** *(planned)* - PKT_DATA, CDA, PKT_CONFIG, PKT_STATUS encoding
- **3.3 Control Network Protocol** *(planned)* - HIVE-C to SERV communication

---

## Chapter 4: Programming Models

Software architecture and firmware development.

*(Chapter 4 files are planned; programming-model content currently lives in [hive_specification.md](../hive_specification.md) sections 4-6.)*

- **4.1 HIVE-C Firmware Architecture** *(planned)* - VexRiscv firmware structure and APIs
- **4.2 SERV Programming** *(planned)* - Monitor firmware and assembly programming
- **4.3 Descriptor Scheduling** *(planned)* - RAPIDS DMA descriptor management
- **4.4 Network Reconfiguration** *(planned)* - Context switching and topology management

---

## Chapter 5: Performance and Verification

Performance modeling, tradeoffs, and verification strategy.

*(Chapter 5 files are planned; performance/verification content currently lives in [hive_specification.md](../hive_specification.md) sections 7 and 10-11.)*

- **5.1 SimPy Performance Models** *(planned)* - Analytical models for educational exploration
- **5.2 Performance Tradeoffs** *(planned)* - Design decision analysis and quantified tradeoffs
- **5.3 Verification Strategy** *(planned)* - Unit tests, integration tests, formal verification
- **5.4 Implementation Roadmap** *(planned)* - Development phases and milestones

---

## Quick Navigation

### For First-Time Readers
1. Start with [Chapter 1.1 Overview](ch01_overview/01_overview.md)
2. Review [Chapter 2.0 Block Overview](ch02_blocks/00_overview.md)
3. Understand AXIS packet classification ([hive_specification.md](../hive_specification.md) section 3)

### For Firmware Developers
1. HIVE-C control software ([hive_specification.md](../hive_specification.md) section 6)
2. Descriptor scheduling ([hive_specification.md](../hive_specification.md) section 6)
3. AXIS packet encoding ([hive_specification.md](../hive_specification.md) section 3)

### For Hardware Engineers
1. [Chapter 2: Block Specifications](ch02_blocks/00_overview.md)
2. System architecture and interfaces ([hive_specification.md](../hive_specification.md) section 2)
3. [Chapter 1.3 Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### For Performance Analysis
1. Performance modeling ([hive_specification.md](../hive_specification.md) section 7)
2. Performance tradeoffs ([hive_specification.md](../hive_specification.md) section 7.2)
3. [Chapter 2.0 Resource Budget](ch02_blocks/00_overview.md)

---

## Document Status

**Version:** 0.3 (Early Proof of Concept - Draft)
**Last Updated:** 2025-10-19
**Status:** Preliminary specification, subject to significant change
**Maintained By:** HIVE Development Team

---

## Related Specifications

- **[RAPIDS Beats HAS](../../../dmas/rapids/docs/rapids_beats_has/rapids_beats_has_index.md)** - DMA engine controlled by HIVE-C
- **[Delta Network Specification](../../../delta/docs/delta_spec/delta_index.md)** - 4×4 mesh NoC for compute fabric
- **[STREAM Specification](../../../dmas/stream/PRD.md)** - Simplified DMA tutorial project

---

**Back to:** [HIVE Component Root](../../PRD.md)
