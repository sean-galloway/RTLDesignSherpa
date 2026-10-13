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

# HIVE Hardware Architecture Specification Index

**Hierarchical Intelligent Vector Environment**

**Version:** 0.1
**Date:** 2026-10-12
**Purpose:** System-level hardware architecture specification for the HIVE
distributed control and monitoring subsystem (1 VexRiscv master + 16 SERV
monitors) coordinating RAPIDS and Delta.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose and Scope](ch01_introduction/01_purpose_and_scope.md)

### Chapter 2: System Overview

- [System Overview and Context](ch02_system_overview/01_system_overview.md)

### Chapter 3: Subsystem Architecture

- [Subsystem Architecture](ch03_architecture/01_subsystem_architecture.md) - the four blocks, inter-block communication, resource budget

### Chapter 4: Interfaces

- [Top-Level Interfaces](ch04_interfaces/01_top_level_interfaces.md)
- [Packet Formats and Routing Rules](ch04_interfaces/02_packet_formats.md)
- [Memory Map and Register Spaces](ch04_interfaces/03_memory_map_and_registers.md)

### Chapter 5: Programming Model

- [HIVE-C Firmware Architecture](ch05_programming_model/01_hive_c_firmware.md)
- [Descriptor Scheduling](ch05_programming_model/02_descriptor_scheduling.md)
- [SERV Monitor Programming](ch05_programming_model/03_serv_monitor_programming.md)
- [Network Reconfiguration Workflow](ch05_programming_model/04_network_reconfiguration.md)

### Chapter 6: Performance

- [Performance Characteristics](ch06_performance/01_performance.md)

### Chapter 7: Integration and Verification

- [Integration and Verification](ch07_integration/01_integration_and_verification.md)

---

## Related Documentation

- **[HIVE MAS](../hive_mas/hive_mas_index.md)** - Micro-Architecture Specification (block-level implementation intent)
- **[HIVE PRD](../../PRD.md)** - Product requirements and use cases
- **[HIVE CLAUDE](../../CLAUDE.md)** - AI assistance guide for this subsystem
- **[RAPIDS Beats HAS](../../../../dma-ip/rapids/docs/rapids_beats_has/rapids_beats_has_index.md)** - the DMA engine HIVE-C controls
- **[Delta HAS](../../../../fabric-gen-ip/delta/docs/delta_has/delta_has_index.md)** - the network fabric HIVE configures
- **[RISC-V Falcon Suite README](../../../README.md)** - suite overview and hive-serv placement beside the ladder

---

**Last Updated:** 2026-10-12
**Maintained By:** RTL Design Sherpa Project
