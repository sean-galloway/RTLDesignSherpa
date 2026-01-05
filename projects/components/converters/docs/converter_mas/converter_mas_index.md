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

# Converters Micro-Architecture Specification Index

**Component:** Converters (Data Width and Protocol Conversion Modules)
**Version:** 1.0
**Date:** 2026-01-03
**Purpose:** Detailed micro-architecture specification for Converters component

---

## Document Organization

This specification covers the Converters component - a collection of configurable data width converters and protocol converters that enable seamless integration between components with different data widths or communication protocols.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Overview](ch01_introduction/01_overview.md)

### Chapter 2: Data Width Converter Blocks

- [Generic Building Blocks](ch02_width_blocks/01_generic_blocks.md)
- [axi_data_upsize Module](ch02_width_blocks/02_axi_data_upsize.md)
- [axi_data_dnsize Module](ch02_width_blocks/03_axi_data_dnsize.md)
- [Dual-Buffer Architecture](ch02_width_blocks/04_dual_buffer.md)
- [axi4_dwidth_converter_wr](ch02_width_blocks/05_dwidth_converter_wr.md)
- [axi4_dwidth_converter_rd](ch02_width_blocks/06_dwidth_converter_rd.md)

### Chapter 3: Protocol Converter Blocks

- [Protocol Conversion Overview](ch03_protocol_blocks/01_overview.md)
- [AXI4 to AXI4-Lite](ch03_protocol_blocks/02_axi4_to_axil4.md)
- [AXI4-Lite to AXI4](ch03_protocol_blocks/03_axil4_to_axi4.md)
- [AXI4 to APB](ch03_protocol_blocks/04_axi4_to_apb.md)
- [PeakRDL Adapter](ch03_protocol_blocks/05_peakrdl_adapter.md)

### Chapter 4: FSM Design

- [Upsize/Downsize FSMs](ch04_fsm_design/01_width_fsms.md)
- [Protocol Converter FSMs](ch04_fsm_design/02_protocol_fsms.md)
- [Burst Decomposition](ch04_fsm_design/03_burst_decomposition.md)

### Chapter 5: Verification

- [Test Strategy](ch05_verification/01_test_strategy.md)
- [Debug Guide](ch05_verification/02_debug_guide.md)

---

## Quick Navigation

### For New Users

1. Start with [Overview](ch01_introduction/01_overview.md) for understanding converter capabilities
2. Read [Generic Building Blocks](ch02_width_blocks/01_generic_blocks.md) to understand the architecture
3. Study [Protocol Conversion Overview](ch03_protocol_blocks/01_overview.md) for protocol handling
4. Reference [Test Strategy](ch05_verification/01_test_strategy.md) for verification approach

### For Integration

- **Width conversion:** See [axi_data_upsize](ch02_width_blocks/02_axi_data_upsize.md) and [axi_data_dnsize](ch02_width_blocks/03_axi_data_dnsize.md)
- **High-performance paths:** See [Dual-Buffer Architecture](ch02_width_blocks/04_dual_buffer.md)
- **Full AXI4 conversion:** See [axi4_dwidth_converter_wr](ch02_width_blocks/05_dwidth_converter_wr.md) and [axi4_dwidth_converter_rd](ch02_width_blocks/06_dwidth_converter_rd.md)
- **Protocol bridges:** See [AXI4 to APB](ch03_protocol_blocks/04_axi4_to_apb.md)

---

## Visual Assets

All diagrams referenced in the documentation are available in:

- **Source Files:**
  - `assets/mermaid/*.mmd` - Mermaid source diagrams

- **Rendered Files:**
  - `assets/mermaid/*.png` - Rendered block diagrams (PNG for PDF compatibility)

### Architecture Diagrams

1. **axi_data_upsize** - [assets/mermaid/axi_data_upsize.png](assets/mermaid/axi_data_upsize.png)
2. **axi_data_dnsize_single** - [assets/mermaid/axi_data_dnsize_single.png](assets/mermaid/axi_data_dnsize_single.png)
3. **axi_data_dnsize_dual** - [assets/mermaid/axi_data_dnsize_dual.png](assets/mermaid/axi_data_dnsize_dual.png)
4. **axi4_dwidth_converter_wr** - [assets/mermaid/dwidth_converter_wr.png](assets/mermaid/dwidth_converter_wr.png)
5. **axi4_dwidth_converter_rd** - [assets/mermaid/dwidth_converter_rd.png](assets/mermaid/dwidth_converter_rd.png)
6. **axi4_to_axil4** - [assets/mermaid/axi4_to_axil4.png](assets/mermaid/axi4_to_axil4.png)
7. **axi4_to_apb** - [assets/mermaid/axi4_to_apb.png](assets/mermaid/axi4_to_apb.png)

### FSM Diagrams

1. **Upsize FSM** - [assets/mermaid/upsize_fsm.png](assets/mermaid/upsize_fsm.png)
2. **Downsize FSM** - [assets/mermaid/dnsize_fsm.png](assets/mermaid/dnsize_fsm.png)
3. **AXI4-to-APB FSM** - [assets/mermaid/axi4_to_apb_fsm.png](assets/mermaid/axi4_to_apb_fsm.png)
4. **Burst Decomposition FSM** - [assets/mermaid/burst_decomp_fsm.png](assets/mermaid/burst_decomp_fsm.png)

---

## Component Overview

### Key Features

- **Generic Building Blocks:** `axi_data_upsize` and `axi_data_dnsize` for any width ratio
- **Full AXI4 Converters:** Complete write path (AW+W+B) and read path (AR+R) modules
- **Protocol Bridges:** AXI4-to-AXI4-Lite, AXI4-Lite-to-AXI4, and AXI4-to-APB conversion
- **Throughput Options:** Single-buffer (80%) or dual-buffer (100%) for downsize
- **Flexible Sideband Handling:** Concatenate, broadcast, or OR modes

### Module Summary

| Module | Purpose | Throughput | Area |
|--------|---------|------------|------|
| axi_data_upsize | Narrow-to-wide accumulator | 100% | 1x |
| axi_data_dnsize | Wide-to-narrow splitter | 80% / 100% | 1x / 2x |
| axi4_dwidth_converter_wr | Full write path | 100% | Standard |
| axi4_dwidth_converter_rd | Full read path | 100% | +100% (dual) |
| axi4_to_axil4 | Burst decomposition | 50-100% | ~450 LUTs |
| axil4_to_axi4 | Protocol upgrade | 100% | ~110 LUTs |
| axi4_to_apb_convert | Full protocol bridge | Sequential | Medium |

: Table 1.1: Converter Module Summary

### Design Philosophy

**Reusable Building Blocks:**
- Generic modules (upsize/dnsize) work with any integer width ratio
- Full converters compose building blocks with AXI4 channel management
- Configurable performance vs. area trade-offs

**Protocol Flexibility:**
- Bidirectional AXI4/AXI4-Lite conversion with zero-overhead upgrade path
- Full AXI4-to-APB protocol translation with state machine control
- PeakRDL adapter for register interface decoupling

---

## Related Documentation

### Companion Specifications

- **[Converters Spec](../converter_spec/converter_index.md)** - Feature specification (high-level)

### Project-Level

- **RTL Source:** `projects/components/converters/rtl/`
- **Test Suite:** `projects/components/converters/dv/tests/`
- **Component PRD:** `projects/components/converters/PRD.md`

---

## Version History

**Version 1.0 (2026-01-03):**
- Initial MAS release
- Migrated from converter_spec format
- Added detailed micro-architecture documentation
- Complete FSM and implementation details

---

**Last Updated:** 2026-01-03
**Maintained By:** RTL Design Sherpa Project
