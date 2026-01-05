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

# Bridge Micro-Architecture Specification Index

**Component:** Bridge (Multi-Protocol Crossbar Generator)
**Version:** 1.0
**Date:** 2026-01-03
**Purpose:** Detailed micro-architecture specification for Bridge component

---

## Document Organization

This specification covers the Bridge component - a CSV-driven generator that creates AXI4 crossbars with automatic width conversion, protocol conversion (AXI4, AXI4-Lite, APB), and channel-specific master support (read-only, write-only, or full).

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Overview](ch01_introduction/01_overview.md)

### Chapter 2: Block Descriptions

- [Master Adapter](ch02_blocks/01_master_adapter.md)
- [Slave Router](ch02_blocks/02_slave_router.md)
- [Crossbar Core](ch02_blocks/03_crossbar_core.md)
- [Arbitration](ch02_blocks/04_arbitration.md)
- [ID Management](ch02_blocks/05_id_management.md)
- [Width Conversion](ch02_blocks/06_width_conversion.md)
- [Protocol Conversion](ch02_blocks/07_protocol_conversion.md)
- [Response Routing](ch02_blocks/08_response_routing.md)
- [Error Handling](ch02_blocks/09_error_handling.md)

### Chapter 3: FSM Design

- [Arbiter FSMs](ch03_fsm_design/01_arbiter_fsms.md)
- [Transaction Tracking](ch03_fsm_design/02_transaction_tracking.md)

### Chapter 4: ID Management

- [CAM Architecture](ch04_id_management/01_cam_architecture.md)
- [ID Tracking Tables](ch04_id_management/02_id_tracking.md)

### Chapter 5: Converters

- [Width Converters](ch05_converters/01_width_converters.md)
- [APB Converters](ch05_converters/02_apb_converters.md)

### Chapter 6: Generated RTL

- [Module Structure](ch06_generated_rtl/01_module_structure.md)
- [Signal Naming](ch06_generated_rtl/02_signal_naming.md)

### Chapter 7: Verification

- [Test Strategy](ch07_verification/01_test_strategy.md)
- [Debug Guide](ch07_verification/02_debug_guide.md)

---

## Quick Navigation

### For New Users

1. Start with [Overview](ch01_introduction/01_overview.md) for understanding Bridge capabilities
2. Read [Block Diagram](ch02_blocks/03_crossbar_core.md) to understand the architecture
3. Study [Arbitration](ch02_blocks/04_arbitration.md) for operational details
4. Reference [Module Structure](ch06_generated_rtl/01_module_structure.md) for generated RTL

### For Integration

- **Protocol support:** See [Protocol Conversion](ch02_blocks/07_protocol_conversion.md) for AXI4/APB/AXI-Lite
- **Width handling:** See [Width Conversion](ch02_blocks/06_width_conversion.md) for data width mismatches
- **ID management:** See [ID Management](ch02_blocks/05_id_management.md) for transaction tracking
- **Error handling:** See [Error Handling](ch02_blocks/09_error_handling.md) for OOR and timeout

---

## Visual Assets

All diagrams referenced in the documentation are available in:

- **Source Files:**
  - `assets/graphviz/*.gv` - Graphviz source diagrams
  - `assets/puml/*.puml` - PlantUML FSM diagrams

- **Rendered Files:**
  - `assets/graphviz/*.png` - Rendered block diagrams
  - `assets/puml/*.png` - Rendered FSM diagrams

### Architecture Diagrams

1. **Master Adapter** - [assets/graphviz/master_adapter.png](assets/graphviz/master_adapter.png)
2. **Slave Router** - [assets/graphviz/slave_router.png](assets/graphviz/slave_router.png)
3. **Crossbar Core** - [assets/graphviz/crossbar_core.png](assets/graphviz/crossbar_core.png)
4. **ID Management** - [assets/graphviz/id_management.png](assets/graphviz/id_management.png)
5. **Width Conversion** - [assets/graphviz/width_conversion.png](assets/graphviz/width_conversion.png)
6. **Protocol Conversion** - [assets/graphviz/protocol_conversion_apb.png](assets/graphviz/protocol_conversion_apb.png)
7. **Response Routing** - [assets/graphviz/response_routing.png](assets/graphviz/response_routing.png)
8. **Error Handling** - [assets/graphviz/error_handling.png](assets/graphviz/error_handling.png)

### FSM Diagrams

1. **AW Arbiter FSM** - [assets/puml/aw_arbiter_fsm.png](assets/puml/aw_arbiter_fsm.png)
2. **AR Arbiter FSM** - [assets/puml/ar_arbiter_fsm.png](assets/puml/ar_arbiter_fsm.png)

---

## Component Overview

### Key Features

- **Multi-Protocol Support:** AXI4, AXI4-Lite, and APB slave conversion
- **CSV-Driven Configuration:** Human-readable port and connectivity definitions
- **Channel-Specific Masters:** Write-only (wr), read-only (rd), or full (rw) support
- **Automatic Width Conversion:** Upsize/downsize for data width mismatches
- **Out-of-Order Support:** ID-based response routing with CAM tracking
- **Custom Signal Prefixes:** Unique prefixes per port for clean integration

### Protocol Conversion Matrix

| Master Protocol | Slave Protocol | Conversion |
|-----------------|----------------|------------|
| AXI4 | AXI4 | Direct or width convert |
| AXI4 | AXI4-Lite | Protocol downgrade |
| AXI4 | APB | Full protocol conversion |

### Design Philosophy

**Efficient Multi-Width Routing:**
- Direct connections where widths match (zero conversion overhead)
- Width converters only where needed
- No fixed internal crossbar width

**Resource Optimization:**
- Channel-specific masters reduce port count by 40-60%
- Per-path width converters instead of global conversion
- Minimal logic for matching-width connections

---

## Related Documentation

### Companion Specifications

- **[Bridge HAS](../bridge_has/bridge_has_index.md)** - Hardware Architecture Specification (high-level)

### Project-Level

- **PRD.md:** [../../PRD.md](../../PRD.md) - Complete product requirements document
- **CLAUDE.md:** [../../CLAUDE.md](../../CLAUDE.md) - AI assistant integration guide

### Generator

- **Generator:** `../../bin/bridge_csv_generator.py` - CSV-based generator script
- **Test Configs:** `../../bin/test_configs/` - Example TOML/CSV configurations

---

## Version History

**Version 1.0 (2026-01-03):**
- Initial specification release
- Restructured from single spec to HAS/MAS format
- Complete block-level documentation
- FSM and ID management details

---

**Last Updated:** 2026-01-03
**Maintained By:** RTL Design Sherpa Project
