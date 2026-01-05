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

# STREAM Hardware Architecture Specification Index

**Version:** 0.90
**Date:** 2026-01-03
**Purpose:** High-level hardware architecture specification for STREAM subsystem

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose and Scope](ch01_introduction/01_purpose.md)
- [Document Conventions](ch01_introduction/02_conventions.md)
- [Definitions and Acronyms](ch01_introduction/03_definitions.md)

### Chapter 2: System Overview

- [Use Cases](ch02_system_overview/01_use_cases.md)
- [Key Features](ch02_system_overview/02_key_features.md)
- [System Context](ch02_system_overview/03_system_context.md)

### Chapter 3: Architecture

- [Block Diagram](ch03_architecture/01_block_diagram.md)
- [Data Flow](ch03_architecture/02_data_flow.md)
- [Multi-Channel Architecture](ch03_architecture/03_channel_architecture.md)

### Chapter 4: Interfaces

- [AXI Master Interfaces](ch04_interfaces/01_axi_masters.md)
- [APB Configuration Interface](ch04_interfaces/02_apb_slave.md)
- [Monitoring Interface](ch04_interfaces/03_monitoring.md)

### Chapter 5: Performance

- [Throughput Targets](ch05_performance/01_throughput.md)
- [Latency Characteristics](ch05_performance/02_latency.md)
- [Resource Estimates](ch05_performance/03_resources.md)

### Chapter 6: Integration

- [System Requirements](ch06_integration/01_system_requirements.md)
- [Clocking and Reset](ch06_integration/02_clocking.md)
- [Verification Strategy](ch06_integration/03_verification.md)

---

## Related Documentation

- **[STREAM MAS](../stream_spec/stream_index.md)** - Micro-Architecture Specification (detailed block-level)
- **[PRD.md](../../PRD.md)** - Product requirements and overview
- **[CLAUDE.md](../../CLAUDE.md)** - AI development guide

---

**Last Updated:** 2026-01-03
**Maintained By:** STREAM Architecture Team
