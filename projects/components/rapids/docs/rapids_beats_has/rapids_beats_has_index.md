# RAPIDS Beats Architecture HAS

**Version:** 1.0
**Date:** 2026-01-17
**Purpose:** Hardware Architecture Specification for RAPIDS Phase 1 "Beats" Architecture
**Classification:** External Interface Specification

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)
- [Revision History](ch00_front_matter/01_revision_history.md)
- [Acronyms and Definitions](ch00_front_matter/02_acronyms.md)

### Chapter 1: Overview

- [Product Overview](ch01_overview/01_product_overview.md)
- [Key Features](ch01_overview/02_key_features.md)
- [System Context](ch01_overview/03_system_context.md)

### Chapter 2: Architecture

- [Block Diagram](ch02_architecture/01_block_diagram.md)
- [Data Flow](ch02_architecture/02_data_flow.md)
- [Channel Architecture](ch02_architecture/03_channel_architecture.md)

### Chapter 3: Interfaces

- [Interface Summary](ch03_interfaces/01_interface_summary.md)
- [AXI4 Master Interface](ch03_interfaces/02_axi4_interface.md)
- [AXIS Interface](ch03_interfaces/03_axis_interface.md)
- [APB Configuration Interface](ch03_interfaces/04_apb_interface.md)
- [Monitor Bus Interface](ch03_interfaces/05_monbus_interface.md)

### Chapter 4: Use Cases

- [Network-to-Memory Transfer](ch04_use_cases/01_network_to_memory.md)
- [Memory-to-Network Transfer](ch04_use_cases/02_memory_to_network.md)
- [Descriptor Chaining](ch04_use_cases/03_descriptor_chaining.md)
- [Multi-Channel Operation](ch04_use_cases/04_multi_channel.md)

### Chapter 5: Programming Model

- [Descriptor Format](ch05_programming/01_descriptor_format.md)
- [Register Map](ch05_programming/02_register_map.md)
- [Initialization Sequence](ch05_programming/03_initialization.md)
- [Error Handling](ch05_programming/04_error_handling.md)

---

## Quick Reference

### RAPIDS Beats at a Glance

| Feature | Specification |
|---------|---------------|
| **Architecture** | Network-to-Memory Accelerator |
| **Channels** | 8 independent DMA channels |
| **Data Width** | 512-bit (configurable) |
| **Address Width** | 64-bit |
| **Descriptor Size** | 256-bit |
| **AXI Protocol** | AXI4 (Read/Write Masters) |
| **Network Protocol** | AXI-Stream (Sink/Source) |
| **Monitoring** | 64-bit MonBus packets |

: RAPIDS Beats Feature Summary

### Interface Summary

| Interface | Type | Direction | Width | Purpose |
|-----------|------|-----------|-------|---------|
| Descriptor AXI | AXI4 Master | Bidirectional | 256-bit | Descriptor fetch |
| Sink AXI | AXI4 Master | Write | 512-bit | Memory write |
| Source AXI | AXI4 Master | Read | 512-bit | Memory read |
| Sink AXIS | AXIS Slave | Input | 512-bit | Network ingress |
| Source AXIS | AXIS Master | Output | 512-bit | Network egress |
| MonBus | Custom | Output | 64-bit | Monitoring |

: External Interface Summary

---

## Related Documentation

- **[RAPIDS Beats MAS](../rapids_beats_mas/rapids_beats_mas_index.md)** - Module Architecture Specification
- **[PRD.md](../../PRD.md)** - Product requirements
- **[ADDRESS_INCREMENT_PATTERNS.md](../ADDRESS_INCREMENT_PATTERNS.md)** - DMA addressing patterns

---

## Specification Conventions

### Signal Naming

- **Clock:** `aclk` (AXI clock domain)
- **Reset:** `aresetn` (active-low, async assert, sync deassert)
- **AXI Signals:** Standard ARM AMBA naming
- **AXIS Signals:** Standard AXI-Stream naming

### Diagram Conventions

- **Mermaid:** Block diagrams and flowcharts
- **WaveDrom:** Timing diagrams
- **Tables:** Interface specifications and register maps

---

**Last Updated:** 2026-01-17
**Maintained By:** RAPIDS Architecture Team
