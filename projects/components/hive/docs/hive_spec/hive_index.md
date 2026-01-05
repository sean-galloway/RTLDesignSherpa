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
- **[2.1 HIVE-C Master Controller](ch02_blocks/01_hive_c_controller.md)** - VexRiscv master controller specification
- **[2.2 SERV Monitor](ch02_blocks/02_serv_monitor.md)** - Per-tile traffic monitoring and control
- **[2.3 Control Network](ch02_blocks/03_control_network.md)** - HIVE-C to SERV communication infrastructure
- **[2.4 Configuration Manager](ch02_blocks/04_config_manager.md)** - Network reconfiguration and context switching

---

## Chapter 3: Interface Specifications

Protocol specifications for HIVE interfaces.

- **[3.1 Top-Level Interfaces](ch03_interfaces/01_top_level.md)** - System-level connections and signal definitions
- **[3.2 AXIS Packet Classification](ch03_interfaces/02_axis_packet_spec.md)** - PKT_DATA, CDA, PKT_CONFIG, PKT_STATUS encoding
- **[3.3 Control Network Protocol](ch03_interfaces/03_control_network_spec.md)** - HIVE-C to SERV communication

---

## Chapter 4: Programming Models

Software architecture and firmware development.

- **[4.1 HIVE-C Firmware Architecture](ch04_programming_models/01_hive_c_firmware.md)** - VexRiscv firmware structure and APIs
- **[4.2 SERV Programming](ch04_programming_models/02_serv_programming.md)** - Monitor firmware and assembly programming
- **[4.3 Descriptor Scheduling](ch04_programming_models/03_descriptor_scheduling.md)** - RAPIDS DMA descriptor management
- **[4.4 Network Reconfiguration](ch04_programming_models/04_network_reconfiguration.md)** - Context switching and topology management

---

## Chapter 5: Performance and Verification

Performance modeling, tradeoffs, and verification strategy.

- **[5.1 SimPy Performance Models](ch05_performance/01_simpy_models.md)** - Analytical models for educational exploration
- **[5.2 Performance Tradeoffs](ch05_performance/02_performance_tradeoffs.md)** - Design decision analysis and quantified tradeoffs
- **[5.3 Verification Strategy](ch05_performance/03_verification_strategy.md)** - Unit tests, integration tests, formal verification
- **[5.4 Implementation Roadmap](ch05_performance/04_implementation_roadmap.md)** - Development phases and milestones

---

## Quick Navigation

### For First-Time Readers
1. Start with [Chapter 1.1 Overview](ch01_overview/01_overview.md)
2. Review [Chapter 2.0 Block Overview](ch02_blocks/00_overview.md)
3. Understand [Chapter 3.2 AXIS Packet Classification](ch03_interfaces/02_axis_packet_spec.md)

### For Firmware Developers
1. [Chapter 4.1 HIVE-C Firmware](ch04_programming_models/01_hive_c_firmware.md)
2. [Chapter 4.3 Descriptor Scheduling](ch04_programming_models/03_descriptor_scheduling.md)
3. [Chapter 3.2 AXIS Packet Spec](ch03_interfaces/02_axis_packet_spec.md)

### For Hardware Engineers
1. [Chapter 2: Block Specifications](ch02_blocks/00_overview.md)
2. [Chapter 3: Interface Specifications](ch03_interfaces/01_top_level.md) (AXIS-based control only)
3. [Chapter 1.3 Clocks and Reset](ch01_overview/03_clocks_and_reset.md)

### For Performance Analysis
1. [Chapter 5.1 SimPy Models](ch05_performance/01_simpy_models.md)
2. [Chapter 5.2 Performance Tradeoffs](ch05_performance/02_performance_tradeoffs.md)
3. [Chapter 2.0 Resource Budget](ch02_blocks/00_overview.md)

---

## Document Status

**Version:** 0.3 (Early Proof of Concept - Draft)
**Last Updated:** 2025-10-19
**Status:** Preliminary specification, subject to significant change
**Maintained By:** HIVE Development Team

---

## Related Specifications

- **[RAPIDS Specification](../../rapids/docs/rapids_spec/rapids_index.md)** - DMA engine controlled by HIVE-C
- **[Delta Network Specification](../../delta/docs/delta_spec/delta_index.md)** - 4×4 mesh NoC for compute fabric
- **[STREAM Specification](../../stream/PRD.md)** - Simplified DMA tutorial project

---

**Back to:** [HIVE Component Root](../../README.md)
