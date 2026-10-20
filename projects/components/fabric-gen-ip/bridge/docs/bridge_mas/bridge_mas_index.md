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
**Version:** 0.12
**Date:** 2026-10-20
**Purpose:** Detailed micro-architecture specification for Bridge component

---

## Overview

Bridge is a TOML-driven generator that produces AXI4 crossbars with automatic width conversion, protocol conversion (AXI3, AXI4, AXI5, AXI4-Lite, AXI5-Lite, APB, APB5, Wishbone B4 — per-port, on slave or master sides; ACE coherency is NOT supported), and channel-specific masters (read-only, write-only, or full). This is the internals document — the one you open when you need to know what the generated RTL actually does, block by block, rather than what the brochure says.

### Key Features

- **Multi-Protocol Support:** AXI4, AXI3, AXI5, AXI4-Lite, AXI5-Lite, APB, APB5, and Wishbone B4 conversion, on slave or master ports (ACE coherency NOT supported)
- **CSV-Driven Configuration:** Human-readable port and connectivity definitions
- **Channel-Specific Masters:** Write-only (wr), read-only (rd), or full (rw) support
- **Automatic Width Conversion:** Upsize/downsize for data width mismatches
- **Out-of-Order Support:** per slave. A multi-master AXI3/AXI4/AXI5 slave (or any `enable_ooo` slave) routes responses by the master index in the fabric ID `{BRIDGE_ID, id}` and may complete IDs in any order; single-master bridges and shim slaves use an in-order bridge_id FIFO and must answer in request order (bridge BUG-008, was BRIDGE-010)
- **Custom Signal Prefixes:** Unique prefixes per port for clean integration

That out-of-order bullet is the one people skim past and regret. The bridge never sorts responses back into order: a by-ID slave is routed by ID, but a FIFO-tracked slave is routed by position, so there the trust has to be mutual.

### Protocol Conversion Matrix

What happens to a transaction depends on the master/slave protocol pairing:

| Master Protocol | Slave Protocol | Conversion |
|---|---|---|
| AXI4 | AXI4 | Direct or width convert |
| AXI4 | AXI3 | `axi4_to_axi3` protocol convert; same data width |
| AXI3 | AXI4 | `axi3_to_axi4` protocol convert; same data width |
| AXI4 | AXI4-Lite | Protocol downgrade |
| AXI4 | APB | Full protocol conversion |

: Protocol Conversion Matrix

### Design Philosophy

**Efficient Multi-Width Routing:**
- Direct connections where widths match (zero conversion overhead)
- Width converters only where needed
- No fixed internal crossbar width

**Resource Optimization:**
- Channel-specific masters reduce port count by 40-60%
- Per-path width converters instead of global conversion
- Minimal logic for matching-width connections

## Design Notes

### Version History

**Rev 1.1 (2026-10-15, current):** the bridge document set -- GAS, HAS and
MAS -- is renumbered to one common rev, 1.1; entries below keep the numbers
they were published under. Content: masters may have several slaves in
flight (the one-target-per-master limitation fixed, GitHub #119 L1:
per-ID tracking, `id_track_bits`, B/R response arbiters); configurable
outstanding limits, `max_outstanding` (the fixed 16 removed, GitHub #119 L5);
per-port latency modes (L7); atomic and trace ports on per-ID tracking (L1b).

**Version 1.2 (2026-09-07):** qc round_1/round_2 correctness pass. Retired the
ID-extension architecture from every page that claimed it (IDs are
pass-through; responses route by an in-order `bridge_id` FIFO -- see
bridge BUG-008 (was BRIDGE-010) for the ordering requirement that creates). Corrected the
out-of-range responder against `axi4_subtractive_slave` (RLAST on the final
beat only, DECERR, 0xDEADBEEF), the monbus group instantiation, the transaction
timeout that does not exist, and the strobe-mapping example. Documented the
subtractive catch-all and its status/IRQ path.

**2026-10-13:** the ID-extension retirement above was itself overtaken by
bridge TASK-005: IDs ARE widened to `{BRIDGE_ID, id}` with more than one
master, and multi-master AXI4/AXI5 slaves track responses in `bridge_cam`.
Chapters 2.1, 2.2, 2.5, 2.8, 2.9, 3.2, 4 and 6.1 were corrected to the
generated RTL; figure numbers were made unique.

**2026-10-18:** those slaves no longer keep a CAM. The master index is the
returned ID's prefix bits, so the slave adapter reads it off BID / RID and
bounds its outstanding count with a counter (bridge W12). `bridge_cam`'s
lookup had been the fabric's critical path. Chapters 2.1, 2.3, 2.5, 2.8,
2.9, 3.2, 4 and 6.1 follow.

**2026-10-18 (rev 1.7):** a CDC slave that several masters share is
arbitrated on its own clock from per-master lanes (W9); shim slaves take
request slots (W14). Chapters 2.3, 2.4 and 6.1 follow.

**Version 1.1 (2026-06-04):** content sync to RTL state at that date.

**Version 1.0 (2026-01-03):**
- Initial specification release
- Restructured from single spec to HAS/MAS format
- Complete block-level documentation
- FSM and ID management details

## References

### Visual Assets

Diagram sources and their renders live in two directories:

- **Source Files:**
  - `assets/graphviz/*.dot` - Graphviz source diagrams
  - `assets/puml/*.puml` - PlantUML FSM diagrams

- **Rendered Files:**
  - `assets/graphviz/*.png` - Rendered block diagrams
  - `assets/puml/*.png` - Rendered FSM diagrams

#### Architecture Diagrams

1. **Master Adapter** - [assets/graphviz/master_adapter.png](assets/graphviz/master_adapter.png)
2. **Slave Router** - [assets/graphviz/slave_router.png](assets/graphviz/slave_router.png)
3. **Crossbar Core** - [assets/graphviz/crossbar_core.png](assets/graphviz/crossbar_core.png)
4. **ID Management** - [assets/graphviz/id_management.png](assets/graphviz/id_management.png)
5. **Width Conversion** - [assets/graphviz/width_conversion.png](assets/graphviz/width_conversion.png)
6. **Protocol Conversion** - [assets/graphviz/protocol_conversion_apb.png](assets/graphviz/protocol_conversion_apb.png)
7. **Response Routing** - [assets/graphviz/response_routing.png](assets/graphviz/response_routing.png)
8. **Error Handling** - [assets/graphviz/error_handling.png](assets/graphviz/error_handling.png)

#### FSM Diagrams

1. **AW Arbiter FSM** - [assets/puml/aw_arbiter_fsm.png](assets/puml/aw_arbiter_fsm.png)
2. **AR Arbiter FSM** - [assets/puml/ar_arbiter_fsm.png](assets/puml/ar_arbiter_fsm.png)

### Companion Specifications

- **[Bridge HAS](https://github.com/seang-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/bridge/docs/bridge_has/bridge_has_index.md)** - Hardware Architecture Specification (high-level)

### Project-Level

- **PRD.md:** [../../PRD.md](https://github.com/seang-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/bridge/PRD.md) - Complete product requirements document
- **CLAUDE.md:** [../../CLAUDE.md](https://github.com/seang-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/bridge/CLAUDE.md) - AI assistant integration guide

### Generator

- **Generator:** `../../bin/bridge_generator.py` - CSV/TOML-based generator script (with `../../bin/bridge_pkg/`)
- **Test Configs:** `../../bin/test_configs/` - Example TOML/CSV configurations

## Navigation

### Document Organization

Each chapter below is one source file.

#### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

#### Chapter 1: Introduction

- [Overview](ch01_introduction/01_overview.md)

#### Chapter 2: Block Descriptions

- [Master Adapter](ch02_blocks/01_master_adapter.md)
- [Slave Router](ch02_blocks/02_slave_router.md)
- [Crossbar Core](ch02_blocks/03_crossbar_core.md)
- [Arbitration](ch02_blocks/04_arbitration.md)
- [ID Management](ch02_blocks/05_id_management.md)
- [Width Conversion](ch02_blocks/06_width_conversion.md)
- [Protocol Conversion](ch02_blocks/07_protocol_conversion.md)
- [Response Routing](ch02_blocks/08_response_routing.md)
- [Error Handling](ch02_blocks/09_error_handling.md)
- [AMBA5 Boundary and Native Sideband](ch02_blocks/10_amba5_boundary.md)

#### Chapter 3: FSM Design

- [Arbiter FSMs](ch03_fsm_design/01_arbiter_fsms.md)
- [Transaction Tracking](ch03_fsm_design/02_transaction_tracking.md)

#### Chapter 4: ID Management

- [By-ID Response Routing](ch04_id_management/01_cam_architecture.md) -- routing by the ID's master-index bits in multi-master slave adapters, and why it replaced `bridge_cam`
- [ID Tracking Tables](ch04_id_management/02_id_tracking.md)

#### Chapter 5: Converters

- [Width Converters](ch05_converters/01_width_converters.md)
- [APB Converters](ch05_converters/02_apb_converters.md)

#### Chapter 6: Generated RTL

- [Module Structure](ch06_generated_rtl/01_module_structure.md)
- [Signal Naming](ch06_generated_rtl/02_signal_naming.md)

#### Chapter 7: Verification

- [Test Strategy](ch07_verification/01_test_strategy.md)
- [Debug Guide](ch07_verification/02_debug_guide.md)

### Quick Navigation

#### For New Users

1. Start with [Overview](ch01_introduction/01_overview.md) for a tour of what Bridge can do
2. Read [Block Diagram](ch02_blocks/03_crossbar_core.md) for the architecture
3. Study [Arbitration](ch02_blocks/04_arbitration.md) for operational details
4. Reference [Module Structure](ch06_generated_rtl/01_module_structure.md) for generated RTL

#### For Integration

- **Protocol support:** See [Protocol Conversion](ch02_blocks/07_protocol_conversion.md) for AXI4/AXI3/APB/AXI-Lite
- **Width handling:** See [Width Conversion](ch02_blocks/06_width_conversion.md) for data width mismatches
- **ID management:** See [ID Management](ch02_blocks/05_id_management.md) for transaction tracking
- **Error handling:** See [Error Handling](ch02_blocks/09_error_handling.md) for OOR and timeout

---

**Last Updated:** 2026-10-11
**Maintained By:** RTL Design Sherpa Project
