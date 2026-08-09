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

# APB IOAPIC Specification - Table of Contents

**Component:** APB I/O Advanced Programmable Interrupt Controller (IOAPIC)  
**Version:** 1.0  
**Last Updated:** 2025-11-16  
**Status:** Production Ready - MVP Complete

---

## Document Organization

This specification is organized into five chapters covering all aspects of the APB IOAPIC component:

> Status (2026-07-22): Only Chapter 1 (all sections), the Chapter 2 overview and FSM
> summary, and the Chapter 5 register map exist in this tree today. The remaining
> sections listed below are planned but not yet written; they are shown without links.

### Chapter 1: Overview
**Location:** `ch01_overview/`

- [01_overview.md](ch01_overview/01_overview.md) - Component overview, features, applications
- [02_architecture.md](ch01_overview/02_architecture.md) - High-level architecture and block hierarchy
-  [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock domains and reset behavior
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External references and standards

### Chapter 2: Blocks
**Location:** `ch02_blocks/`

- [00_overview.md](ch02_blocks/00_overview.md) - Block hierarchy overview
- 01_ioapic_core.md - Core interrupt routing logic *(planned, not yet written)*
- 02_ioapic_config_regs.md - Configuration register wrapper with indirect access *(planned, not yet written)*
- 03_ioapic_regs.md - PeakRDL generated register file *(planned, not yet written)*
- 04_apb4_ioapic_top.md - Top-level integration *(planned, not yet written)*
- [05_fsm_summary.md](ch02_blocks/05_fsm_summary.md) - FSM state summary table

### Chapter 3: Interfaces
**Location:** `ch03_interfaces/` *(planned, not yet written)*

- 01_top_level.md - Top-level signal list
- 02_apb_interface_spec.md - APB protocol specification
- 03_indirect_access.md - IOREGSEL/IOWIN indirect register access
- 04_irq_interface.md - IRQ input and output interfaces
- 05_eoi_interface.md - End-of-Interrupt handling

### Chapter 4: Programming Model
**Location:** `ch04_programming/` *(planned, not yet written)*

- 01_initialization.md - Software initialization sequence
- 02_redirection_table.md - Configuring redirection table entries
- 03_edge_triggered_irq.md - Edge-triggered interrupt handling
- 04_level_triggered_irq.md - Level-triggered interrupt handling with EOI
- 05_use_cases.md - Common use case examples

### Chapter 5: Registers
**Location:** `ch05_registers/`

- [01_register_map.md](ch05_registers/01_register_map.md) - Complete register address map
- 02_indirect_access.md - IOREGSEL/IOWIN access method *(planned, not yet written)*
- 03_redirection_table.md - Redirection table field descriptions *(planned, not yet written)*

---

## Quick Navigation

### For Software Developers
- Reference [Chapter 5: Registers](ch05_registers/01_register_map.md)
- **Critical:** Understand the IOREGSEL/IOWIN indirect access method (see the register map; a dedicated indirect-access section is planned)

### For Hardware Integrators
- Start with [Chapter 1: Overview](ch01_overview/01_overview.md)
- Chapter 3 (interfaces/signal list) is planned but not yet written; see `../../rtl/ioapic/apb4_ioapic.sv` for the current port list

### For Verification Engineers
- Start with [Chapter 2: Blocks](ch02_blocks/00_overview.md)
- Reference [FSM Summary](ch02_blocks/05_fsm_summary.md)

### For System Architects
- Start with [Architecture Overview](ch01_overview/02_architecture.md)
- Programming-model chapters (initialization, redirection table, use cases) are planned but not yet written

---

## Key Features

### Intel 82093AA Compatibility
- Indirect register access via IOREGSEL/IOWIN
- 24 interrupt input sources (IRQ0-IRQ23)
- Programmable redirection table
- Edge and level trigger modes
- Active high/low polarity per IRQ
- Priority-based arbitration
- Remote IRR for level-triggered interrupts

### Modern RLB Architecture
- APB4 slave interface with optional CDC
- PeakRDL register generation
- Clean SystemVerilog implementation
- Comprehensive validation support
- FPGA-optimized design

---

## Document Conventions

### Notation
- **bold** - Important terms, signal names
- `code` - Register names, field names, code examples
- *italic* - Emphasis, notes

### Signal Naming
- `pclk` - APB clock
- `ioapic_clk` - IOAPIC controller clock
- `irq_in[23:0]` - Interrupt inputs
- `irq_out_*` - Interrupt output signals

### Register Notation
- `IOREGSEL` - Direct APB register at 0x00
- `IOWIN` - Direct APB register at 0x04
- `IOAPICID` - Internal register at offset 0x00 (via IOREGSEL/IOWIN)
- `IOREDTBL[n]` - Redirection table entry n (n=0-23)

### Address Notation
- **APB addresses:** Direct access from CPU (0x00, 0x04)
- **Internal offsets:** Accessed via IOREGSEL/IOWIN (0x00, 0x01, 0x10-0x3F)

---

## Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-11-16 | RTL Design Sherpa | Initial specification based on Intel 82093AA with RLB methodology |

---

## Related Documentation

**RLB Module Documentation:**
- [TODO.md](../../rtl/ioapic/TODO.md) - Implementation roadmap and next steps
- [PeakRDL README](../../rtl/ioapic/peakrdl/README.md) - Register generation guide

**RLB System Documentation:**
- [RLB_STATUS_AND_ROADMAP.md](../../rtl/RLB_STATUS_AND_ROADMAP.md) - System-wide status and planning
- [RLB_FPGA_IMPLEMENTATION_GUIDE.md](../../rtl/RLB_FPGA_IMPLEMENTATION_GUIDE.md) - FPGA deployment guide
- [RLB_MODULE_AUDIT.md](../../rtl/RLB_MODULE_AUDIT.md) - Architecture compliance audit

**Reference Specifications:**
- [HPET Specification](../hpet_mas/hpet_mas_index.md) - Reference RLB module spec
- Intel 82093AA I/O Advanced Programmable Interrupt Controller Datasheet

---

## Document Status

| Chapter | Status | Completion |
|---------|--------|------------|
| Chapter 1: Overview | ✅ Complete | 100% |
| Chapter 2: Blocks | 🟡 Partial (overview + FSM summary only) | 33% |
| Chapter 3: Interfaces | 📋 Planned | 0% |
| Chapter 4: Programming | 📋 Planned | 0% |
| Chapter 5: Registers | 🟡 Partial (register map only) | 33% |

**Specification Status:** Production Ready - MVP Implementation Complete

---

**Next Steps:**
1. Review specification for completeness
2. Add timing diagrams as needed
3. Expand use cases based on validation results
4. Update with any implementation discoveries
