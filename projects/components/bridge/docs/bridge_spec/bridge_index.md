# Bridge: CSV-Based AXI4 Crossbar Generator - Specification

**Component:** Bridge - CSV-Based AXI4 Crossbar Generator
**Version:** 0.90
**Last Updated:** 2025-11-14
**Status:** Phase 2+ Complete - Bridge ID Tracking Fully Implemented

---

## Document Organization

This specification documents the Bridge CSV-based AXI4 crossbar generator, which creates parameterized SystemVerilog crossbars from human-readable CSV configuration files.

### Chapter 0: Quick Start
**Location:** `ch00_quick_start/`

- [01_installation.md](ch00_quick_start/01_installation.md) - Installation and setup
- [02_first_bridge.md](ch00_quick_start/02_first_bridge.md) - Creating your first bridge
- [03_simulation.md](ch00_quick_start/03_simulation.md) - Simulating the bridge
- [04_integration.md](ch00_quick_start/04_integration.md) - Integration into designs

### Chapter 1: Overview
**Location:** `ch01_overview/`

- [01_overview.md](ch01_overview/01_overview.md) - What is Bridge, key features, and applications
- [02_architecture.md](ch01_overview/02_architecture.md) - System architecture and design philosophy
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clocking and reset strategy
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - References and related documents

### Chapter 2: Internal Block Architecture
**Location:** `ch02_blocks/`

This chapter documents the internal functional blocks that make up the AXI4 bridge crossbar.

- [01_master_adapter.md](ch02_blocks/01_master_adapter.md) - Master interface adaptation and ID extension
- [02_slave_router.md](ch02_blocks/02_slave_router.md) - Address decoding and slave selection
- [03_crossbar_core.md](ch02_blocks/03_crossbar_core.md) - Core switching fabric architecture
- [04_arbitration.md](ch02_blocks/04_arbitration.md) - Multi-master arbitration schemes
- [05_id_management.md](ch02_blocks/05_id_management.md) - Transaction ID tracking (CAM/FIFO)
- [06_width_conversion.md](ch02_blocks/06_width_conversion.md) - Data width conversion logic
- [07_protocol_conversion.md](ch02_blocks/07_protocol_conversion.md) - AXI4-to-APB protocol conversion
- [08_response_routing.md](ch02_blocks/08_response_routing.md) - Response path routing and merging
- [09_error_handling.md](ch02_blocks/09_error_handling.md) - Error detection and handling

### Chapter 3: AXI4 Interface Reference
**Location:** `ch03_interfaces/`

Complete reference for all AXI4 signals, timing, and protocol rules used in the bridge.

- [01_axi4_signals.md](ch03_interfaces/01_axi4_signals.md) - Write Address Channel (AW) detailed reference
- [02_write_data.md](ch03_interfaces/02_write_data.md) - Write Data Channel (W) specification
- [03_write_response.md](ch03_interfaces/03_write_response.md) - Write Response Channel (B) specification
- [04_read_address.md](ch03_interfaces/04_read_address.md) - Read Address Channel (AR) detailed reference
- [05_read_data.md](ch03_interfaces/05_read_data.md) - Read Data and Response Channel (R) specification

### Chapter 4: CSV Generator
**Location:** `ch02_csv_generator/`

- [04_channel_specific.md](ch02_csv_generator/04_channel_specific.md) - Channel-specific masters (wr/rd/rw)

### Chapter 5: Generated RTL
**Location:** `ch03_generated_rtl/`

- [01_module_structure.md](ch03_generated_rtl/01_module_structure.md) - Generated module organization
- [02_arbiter_fsms.md](ch03_generated_rtl/02_arbiter_fsms.md) - AW/AR arbiter finite state machines
- [07_bridge_id_tracking.md](ch03_generated_rtl/07_bridge_id_tracking.md) - Bridge ID tracking for multi-master response routing

**PlantUML Diagrams:** `assets/puml/`
- [aw_arbiter_fsm.puml](assets/puml/aw_arbiter_fsm.puml) - AW channel arbiter FSM
- [ar_arbiter_fsm.puml](assets/puml/ar_arbiter_fsm.puml) - AR channel arbiter FSM

**Graphviz Block Diagrams:** `assets/graphviz/`
- [bridge_2x2.gv](assets/graphviz/bridge_2x2.gv) - 2 master × 2 slave configuration
- [bridge_1x4.gv](assets/graphviz/bridge_1x4.gv) - 1 master × 4 slave configuration

### Chapter 6: Usage Examples
**Location:** `ch04_usage_examples/`

(To be documented - examples of bridge configuration and usage)

---

## Quick Navigation

### For RTL Designers
- Start with [Quick Start Guide](ch00_quick_start/01_installation.md)
- Review [Overview](ch01_overview/01_overview.md)
- Study [Internal Blocks](ch02_blocks/01_master_adapter.md)
- Reference [AXI4 Signals](ch03_interfaces/01_axi4_signals.md)

### For System Architects
- Start with [Architecture Overview](ch01_overview/02_architecture.md)
- Review [Crossbar Core](ch02_blocks/03_crossbar_core.md)
- Study [Arbitration](ch02_blocks/04_arbitration.md)
- Review [ID Management](ch02_blocks/05_id_management.md)

### For Verification Engineers
- Start with [Internal Blocks](ch02_blocks/01_master_adapter.md)
- Review [Error Handling](ch02_blocks/09_error_handling.md)
- Study [AXI4 Protocol](ch03_interfaces/01_axi4_signals.md)
- Review [Generated RTL](ch03_generated_rtl/01_module_structure.md)

### For Protocol Reference
- Complete [AXI4 Signal Reference](ch03_interfaces/01_axi4_signals.md)
- Understand [Channel Interactions](ch03_interfaces/02_write_data.md)
- Study [Out-of-Order Behavior](ch03_interfaces/05_read_data.md)

---

## Key Features Documented

### Phase 1 Features (Complete)
- CSV configuration parsing
- Custom signal prefixes per port
- Mixed AXI4/APB protocol support
- Mixed data widths
- Partial connectivity matrices
- Automatic converter identification
- Port generation with custom prefixes

### Phase 2 Features (Complete)
- **Channel-Specific Masters** - Write-only (wr), read-only (rd), full (rw)
- Conditional AXI4 channel generation
- Optimized width converter instantiation
- Channel-aware direct connections
- Resource optimization for dedicated masters

### Phase 2+ Features (Complete - 2025-11-10)
- **Bridge ID Tracking** - Multi-master response routing with bridge_id
- Per-master unique BRIDGE_ID parameter
- Slave adapter CAM/FIFO transaction tracking
- Configurable out-of-order support per slave (enable_ooo)
- Crossbar bridge_id-based response routing
- Zero-latency FIFO mode for in-order slaves
- 1-cycle CAM mode for out-of-order slaves

### Future Enhancements (Planned)
- **Monitored Interface Versions**: AXI4/AXIL4 master/slave monitor ports for debugging
  - axi4_master_rd_mon.sv / axi4_master_wr_mon.sv
  - axi4_slave_rd_mon.sv / axi4_slave_wr_mon.sv
  - axil4_master_rd_mon.sv / axil4_master_wr_mon.sv
  - axil4_slave_rd_mon.sv / axil4_slave_wr_mon.sv
  - monbus aggregation (similar to stream component monbus_axil_group.sv)
- APB converter placeholder implementation
- Slave-side width converter downsize
- Variable-width crossbar internal data path
- Performance monitoring integration

---

## Document Conventions

### Notation
- **bold** - Important terms, file names
- `code` - CSV fields, signal names, commands
- *italic* - Emphasis, notes

### Signal Naming
- `{prefix}awaddr` - AXI4 Write Address channel address
- `{prefix}araddr` - AXI4 Read Address channel address
- `{prefix}paddr` - APB address
- `aclk` - AXI4 clock
- `aresetn` - AXI4 active-low reset
- `pclk` - APB clock
- `presetn` - APB active-low reset

### CSV Notation
- `port_name` - Unique identifier for port
- `channels` - Channel specification: rw/wr/rd
- `N/A` - Not applicable field value

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-10-19 | Initial specification with Phase 1 features |
| 1.1 | 2025-10-26 | Added channel-specific master support (Phase 2) |
| 1.2 | 2025-11-10 | Added bridge ID tracking for multi-master routing (Phase 2+) |
| 0.90 | 2025-11-14 | Added Chapter 2 (Internal Blocks) and Chapter 3 (AXI4 Interface Reference) - Draft for Review |

---

## Related Documentation

- [../../PRD.md](../../PRD.md) - Product Requirements Document
- [../../CLAUDE.md](../../CLAUDE.md) - AI integration guide
- [../../CSV_BRIDGE_STATUS.md](../../CSV_BRIDGE_STATUS.md) - Implementation status and phase tracking
- [../../TASKS.md](../../TASKS.md) - Development tasks
- [../../bin/bridge_csv_generator.py](../../bin/bridge_csv_generator.py) - Generator source code

---

**Next:** [Chapter 0 - Quick Start](ch00_quick_start/01_installation.md) or [Chapter 1 - Overview](ch01_overview/01_overview.md)
