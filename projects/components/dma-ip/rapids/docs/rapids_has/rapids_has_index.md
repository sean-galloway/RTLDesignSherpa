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

# RAPIDS Architecture HAS

**Version:** 0.1
**Date:** 2026-09-30
**Purpose:** Hardware Architecture Specification for byte-granular RAPIDS, the product design that succeeds the RAPIDS Beats stepping stone
**Classification:** External Interface Specification

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

Chapters marked **(shared with RAPIDS Beats)** are the RAPIDS Beats HAS
chapters, linked rather than copied: the two designs share them exactly.
Where such a chapter names a module, the byte-granular module is the same
name without the `_beats` suffix (`rapids_top` for `rapids_beats_top`).

### Front Matter
- [Document Information](ch00_front_matter/00_document_info.md)
- [Revision History](ch00_front_matter/01_revision_history.md)
- [Acronyms and Definitions](../rapids_beats_has/ch00_front_matter/02_acronyms.md) (shared with RAPIDS Beats)

### Chapter 1: Overview
- [Product Overview](ch01_overview/01_product_overview.md)
- [Key Features](ch01_overview/02_key_features.md)
- [System Context](ch01_overview/03_system_context.md)

### Chapter 2: Architecture
- [Block Diagram](ch02_architecture/01_block_diagram.md)
- [Data Flow](ch02_architecture/02_data_flow.md)
- [Channel Architecture](../rapids_beats_has/ch02_architecture/03_channel_architecture.md) (shared with RAPIDS Beats)

### Chapter 3: Interfaces
- [Interface Summary](../rapids_beats_has/ch03_interfaces/01_interface_summary.md) (shared with RAPIDS Beats)
- [AXI4 Master Interface](ch03_interfaces/02_axi4_interface.md)
- [AXIS Interface](ch03_interfaces/03_axis_interface.md)
- [APB Configuration Interface](../rapids_beats_has/ch03_interfaces/04_apb_interface.md) (shared with RAPIDS Beats)
- [Monitor Bus Interface](../rapids_beats_has/ch03_interfaces/05_monbus_interface.md) (shared with RAPIDS Beats)

### Chapter 4: Use Cases
- [Network-to-Memory Transfer](ch04_use_cases/01_network_to_memory.md)
- [Memory-to-Network Transfer](ch04_use_cases/02_memory_to_network.md)
- [Descriptor Chaining](../rapids_beats_has/ch04_use_cases/03_descriptor_chaining.md) (shared with RAPIDS Beats)
- [Multi-Channel Operation](../rapids_beats_has/ch04_use_cases/04_multi_channel.md) (shared with RAPIDS Beats)

### Chapter 5: Programming Model
- [Descriptor Format](ch05_programming/01_descriptor_format.md)
- [Register Map](../rapids_beats_has/ch05_programming/02_register_map.md) (shared with RAPIDS Beats)
- [Initialization Sequence](../rapids_beats_has/ch05_programming/03_initialization.md) (shared with RAPIDS Beats)
- [Error Handling](ch05_programming/04_error_handling.md)

### Chapter 6: Performance
- [Throughput](ch06_performance/01_throughput.md)
- [Latency Characteristics](../rapids_beats_has/ch06_performance/02_latency.md) (shared with RAPIDS Beats)
- [Resource Estimates](ch06_performance/03_resources.md)

---

## Quick Reference

### RAPIDS at a Glance

| Feature | Specification |
|---------|---------------|
| **Architecture** | Network-to-Memory / Memory-to-Network DMA, byte-granular |
| **Channels** | 8 independent DMA channels |
| **Data Width** | 256-bit (configurable; 32-byte beats) |
| **Address Width** | 64-bit, byte-granular |
| **Descriptor Size** | 256-bit; length in BYTES |
| **Byte enables** | WSTRB on the sink write master, TSTRB on both streams |
| **AXI Protocol** | AXI4 (Read/Write Masters), beat-aligned bursts, 4 KB safe |
| **Network Protocol** | AXI-Stream (Sink/Source), packed bytes, partial last beat |
| **Monitoring** | 64-bit MonBus packets |

: RAPIDS Feature Summary

### What is different from RAPIDS Beats

| Aspect | RAPIDS Beats | RAPIDS |
|--------|--------------|--------|
| Descriptor length unit | beats | bytes |
| Address alignment | `DATA_WIDTH/8` | any byte (linear descriptors) |
| Sink write data | all lanes strobed | WSTRB marks the bytes written |
| Source stream | full beats only | packed bytes, contiguous TSTRB on the last beat, TLAST |
| Egress packet framing | one packet per drain block | one packet per descriptor |
| Sink ingress | buffers before the descriptor | waits for the descriptor's packet record |
| TYPE=EXT descriptors | beat rows | beat rows (aligned addresses and lengths, by design) |

: RAPIDS versus RAPIDS Beats
