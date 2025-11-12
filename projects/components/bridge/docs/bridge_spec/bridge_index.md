# Bridge: CSV-Based AXI4 Crossbar Generator - Specification

**Component:** Bridge - CSV-Based AXI4 Crossbar Generator
**Version:** 1.2
**Last Updated:** 2025-11-10
**Status:** Phase 2+ Complete - Bridge ID Tracking Fully Implemented

---

## Document Organization

This specification documents the Bridge CSV-based AXI4 crossbar generator, which creates parameterized SystemVerilog crossbars from human-readable CSV configuration files.

### Chapter 1: Overview
**Location:** `ch01_overview/`

- [01_introduction.md](ch01_overview/01_introduction.md) - What is Bridge, key features, and applications
- [02_architecture.md](ch01_overview/02_architecture.md) - System architecture and design philosophy
- [03_comparison.md](ch01_overview/03_comparison.md) - Comparison with APB and Delta crossbars
- [04_features.md](ch01_overview/04_features.md) - Feature summary and capabilities
- [05_status.md](ch01_overview/05_status.md) - Development status and roadmap

### Chapter 2: CSV Generator
**Location:** `ch02_csv_generator/`

- [01_overview.md](ch02_csv_generator/01_overview.md) - CSV generator workflow and design
- [02_ports_csv.md](ch02_csv_generator/02_ports_csv.md) - Port configuration file format
- [03_connectivity_csv.md](ch02_csv_generator/03_connectivity_csv.md) - Connectivity matrix format
- [04_channel_specific.md](ch02_csv_generator/04_channel_specific.md) - Channel-specific masters (wr/rd/rw)
- [05_converter_insertion.md](ch02_csv_generator/05_converter_insertion.md) - Automatic converter generation
- [06_command_line.md](ch02_csv_generator/06_command_line.md) - Generator command-line interface

### Chapter 3: Generated RTL
**Location:** `ch03_generated_rtl/`

- [01_module_structure.md](ch03_generated_rtl/01_module_structure.md) - Generated module organization
- [02_arbiter_fsms.md](ch03_generated_rtl/02_arbiter_fsms.md) - AW/AR arbiter finite state machines
- [03_crossbar_core.md](ch03_generated_rtl/03_crossbar_core.md) - Internal crossbar instantiation
- [04_width_converters.md](ch03_generated_rtl/04_width_converters.md) - Data width conversion logic
- [05_apb_converters.md](ch03_generated_rtl/05_apb_converters.md) - AXI4-to-APB protocol conversion
- [06_signal_routing.md](ch03_generated_rtl/06_signal_routing.md) - Internal signal connections
- [07_bridge_id_tracking.md](ch03_generated_rtl/07_bridge_id_tracking.md) - Bridge ID tracking for multi-master response routing

**PlantUML Diagrams:** `assets/puml/`
- [aw_arbiter_fsm.puml](assets/puml/aw_arbiter_fsm.puml) - AW channel arbiter FSM
- [ar_arbiter_fsm.puml](assets/puml/ar_arbiter_fsm.puml) - AR channel arbiter FSM

**Graphviz Block Diagrams:** `assets/graphviz/`
- [bridge_2x2.gv](assets/graphviz/bridge_2x2.gv) - 2 master × 2 slave configuration
- [bridge_1x4.gv](assets/graphviz/bridge_1x4.gv) - 1 master × 4 slave configuration

### Chapter 4: Usage Examples
**Location:** `ch04_usage_examples/`

- [01_simple_2x2.md](ch04_usage_examples/01_simple_2x2.md) - Simple 2 master x 2 slave example
- [02_rapids_config.md](ch04_usage_examples/02_rapids_config.md) - RAPIDS-style channel-specific configuration
- [03_mixed_protocols.md](ch04_usage_examples/03_mixed_protocols.md) - AXI4 + APB mixed protocol example
- [04_partial_connectivity.md](ch04_usage_examples/04_partial_connectivity.md) - Partial connectivity matrix
- [05_integration.md](ch04_usage_examples/05_integration.md) - Integration into larger designs

---

## Quick Navigation

### For RTL Designers
- Start with [Chapter 1: Overview](ch01_overview/01_introduction.md)
- Review [CSV Generator Workflow](ch02_csv_generator/01_overview.md)
- Study [Usage Examples](ch04_usage_examples/01_simple_2x2.md)

### For System Architects
- Start with [Architecture Overview](ch01_overview/02_architecture.md)
- Compare with [APB and Delta](ch01_overview/03_comparison.md)
- Review [Converter Insertion](ch02_csv_generator/05_converter_insertion.md)

### For Verification Engineers
- Start with [Generated RTL Structure](ch03_generated_rtl/01_module_structure.md)
- Review [Signal Routing](ch03_generated_rtl/05_signal_routing.md)

### For Software Integration
- Start with [CSV Format](ch02_csv_generator/02_ports_csv.md)
- Review [Command-Line Interface](ch02_csv_generator/06_command_line.md)
- Study [Integration Examples](ch04_usage_examples/05_integration.md)

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

---

## Related Documentation

- [../../PRD.md](../../PRD.md) - Product Requirements Document
- [../../CLAUDE.md](../../CLAUDE.md) - AI integration guide
- [../../CSV_BRIDGE_STATUS.md](../../CSV_BRIDGE_STATUS.md) - Implementation status and phase tracking
- [../../TASKS.md](../../TASKS.md) - Development tasks
- [../../bin/bridge_csv_generator.py](../../bin/bridge_csv_generator.py) - Generator source code

---

**Next:** [Chapter 1 - Overview](ch01_overview/01_introduction.md)
