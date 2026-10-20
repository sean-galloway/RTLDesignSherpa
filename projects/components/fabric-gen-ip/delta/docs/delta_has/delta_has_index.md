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

# Delta Hardware Architecture Specification Index

## Overview

**Version:** 1.3
**Date:** 2026-10-20
**Purpose:** High-level hardware architecture specification for the Delta AXI4-Stream crossbar generator, including the planned mesh network mode

---

## Related Modules

- **[Delta MAS](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/delta/docs/delta_mas/delta_mas_index.md)** - Micro-Architecture Specification (detailed block-level)
- **[PRD.md](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/PRD.md)** - Product requirements and overview
- **[CLAUDE.md](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/CLAUDE.md)** - AI development guide
- **[QUICK_START.md](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/QUICK_START.md)** - Hands-on generator guide

---

## Navigation

**Note:** Every chapter below is one source file; the document build assembles the spec from these links.

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
- [Protocol Support](ch03_architecture/03_protocol_support.md)

### Chapter 4: Interfaces

- [AXI-Stream Base Interface](ch04_interfaces/01_axis_base_interface.md)
- [AXI-Stream Rich Interface (TSTRB + AMBA5)](ch04_interfaces/02_axis_rich_interface.md)
- [Clock and Reset](ch04_interfaces/03_clock_reset.md)

### Chapter 5: Performance

- [Throughput Characteristics](ch05_performance/01_throughput.md)
- [Latency Analysis](ch05_performance/02_latency.md)
- [Resources](ch05_performance/03_resources.md)

### Chapter 6: Integration

- [System Requirements](ch06_integration/01_system_requirements.md)
- [Parameter Configuration](ch06_integration/02_parameters.md)
- [Verification Strategy](ch06_integration/03_verification.md)
- [Synthesis and Implementation](ch06_integration/04_synthesis.md)

### Chapter 7: Mesh Network

- [Hierarchy](ch07_mesh_network/01_hierarchy.md)
- [Cell and Flit](ch07_mesh_network/02_cell_and_flit.md)
- [Routing and Configuration](ch07_mesh_network/03_routing_and_config.md)
- [Flow Control and Deadlock](ch07_mesh_network/04_flow_control_and_deadlock.md)
- [Quality of Service](ch07_mesh_network/05_qos.md)
- [Multicast](ch07_mesh_network/06_multicast.md)
- [Systolic Support and Fabric Modes](ch07_mesh_network/07_systolic_and_modes.md)
- [Observability and DFT](ch07_mesh_network/08_observability_and_dft.md)
- [Performance and Verification](ch07_mesh_network/09_performance_and_verification.md)
- [Deferred Items](ch07_mesh_network/10_deferred_items.md)
- [Resilient Routing: Open Hazards](ch07_mesh_network/11_resilient_routing.md)

---

**Last Updated:** 2026-10-14
**Maintained By:** RTL Design Sherpa Project
