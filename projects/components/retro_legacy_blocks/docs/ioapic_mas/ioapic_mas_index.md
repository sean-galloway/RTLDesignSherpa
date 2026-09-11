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

# ioapic

## Overview

**Component:** APB I/O Advanced Programmable Interrupt Controller (IOAPIC)  
**Version:** 1.3  
**Last Updated:** 2026-09-11  
**Status:** RTL Functional - 36/36 in all six DV configurations; issue #48
delivery, IOREGSEL and address-decode defects fixed 2026-09-09 (spec partial;
see Document Status below)

This is the micro-architecture specification for the APB IOAPIC, laid out as five chapters. Before you start clicking links, know that only part of it exists today — the status note below is the honest map.

### Document Organization

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

### Key Features

**Intel 82093AA Compatibility:**
- Indirect register access via IOREGSEL/IOWIN
- 24 interrupt input sources (IRQ0-IRQ23)
- Programmable redirection table
- Edge and level trigger modes
- Active high/low polarity per IRQ
- Priority-based arbitration
- Remote IRR for level-triggered interrupts

**Modern RLB Architecture:**
- APB4 slave interface with optional CDC
- PeakRDL register generation
- Clean SystemVerilog implementation
- Comprehensive validation support
- FPGA-optimized design

## Design Notes

### Document Conventions

**Notation:**
- **bold** - Important terms, signal names
- `code` - Register names, field names, code examples
- *italic* - Emphasis, notes

**Signal Naming:**
- `pclk` - APB clock
- `ioapic_clk` - IOAPIC controller clock
- `irq_in[23:0]` - Interrupt inputs
- `irq_out_*` - Interrupt output signals

**Register Notation:**
- `IOREGSEL` - Direct APB register at 0x00
- `IOWIN` - Direct APB register at 0x04
- `IOAPICID` - Internal register at offset 0x00 (via IOREGSEL/IOWIN)
- `IOREDTBL[n]` - Redirection table entry n (n=0-23)

**Address Notation:**
- **APB addresses:** Direct access from CPU (0x00, 0x04)
- **Internal offsets:** Accessed via IOREGSEL/IOWIN (0x00, 0x01, 0x10-0x3F)

## Testing

### Document Status

| Chapter | Status | Completion |
| --- | --- | --- |
| Chapter 1: Overview | Complete | 100% |
| Chapter 2: Blocks | Partial (overview + FSM summary only) | 33% |
| Chapter 3: Interfaces | Planned | 0% |
| Chapter 4: Programming | Planned | 0% |
| Chapter 5: Registers | Partial (register map only) | 33% |

**Specification Status:** MVP RTL implemented and validated (36/36, CDC
off/on x gate/func/full). The issue #48 defects - edge double-delivery,
global EOI block, live-vector Remote IRR clear, IOREGSEL shadow divergence,
address aliasing above 0x0FF, unsynchronized EOI - were fixed 2026-09-09 and
this revision of the spec describes the fixed hardware. Logical destination
mode and round-robin arbitration landed 2026-09-10, and delegated
LowestPriority delivery on 2026-09-11. What is still deferred (multi-IOAPIC
routing, boot-interrupt delivery, MSI) is tracked as RLB-008 in
`vault/Tasks/RLB/open.md`.

**Next Steps:**
1. Review specification for completeness
2. Add timing diagrams as needed
3. Expand use cases based on validation results
4. Update with any implementation discoveries

## References

### Related Documentation

**RLB Module Documentation:**
- [README.md](../../rtl/ioapic/README.md) - Block summary and verification entry point
- `vault/Tasks/RLB/open.md` (RLB-008) - Deferred IOAPIC features
- [PeakRDL README](../../rdl/ioapic/README.md) - Register generation guide

**RLB System Documentation:**
- [RLB_STATUS_AND_ROADMAP.md](../../rtl/RLB_STATUS_AND_ROADMAP.md) - System-wide status and planning
- [RLB_FPGA_IMPLEMENTATION_GUIDE.md](../../rtl/RLB_FPGA_IMPLEMENTATION_GUIDE.md) - FPGA deployment guide
- [RLB_MODULE_AUDIT.md](../../rtl/RLB_MODULE_AUDIT.md) - Architecture compliance audit

**Reference Specifications:**
- [HPET Specification](../hpet_mas/hpet_mas_index.md) - Reference RLB module spec
- Intel 82093AA I/O Advanced Programmable Interrupt Controller Datasheet

### Version History

| Version | Date | Author | Changes |
| --- | --- | --- | --- |
| 1.0 | 2025-11-16 | RTL Design Sherpa | Initial specification based on Intel 82093AA with RLB methodology |
| 1.1 | 2026-09-09 | RTL Design Sherpa | Issue #48 fixes: delivery FSM replaced by a one-entry valid/ready stage (one delivery per edge, no parked valid), per-pin Remote IRR blocking with EOI matched against the delivered vector, single IOREGSEL copy with unmapped selectors and 0x100+ accesses dropped, IOWIN tie-off, LAPIC interface presented in pclk and crossed with matched-latency synchronizers when CDC_ENABLE=1 |
| 1.2 | 2026-09-10 | RTL Design Sherpa | RLB-008, two items. Logical destination mode: `irq_out_dest_mode` carries the RTE's mode alongside the destination, because an IOAPIC does not decode logical destinations itself -- it forwards the field and the mode and the local APICs match, so forwarding the mode is the whole of this block's responsibility. Round-robin arbitration behind `IOAPICARBCFG.rr_enable` at IOWIN selector 0x03, which is reserved on the real 82093AA so a driver written for the part never writes it and gets static priority: the scan starts just above the pin last ACCEPTED and wraps, making priority a position in the rotation rather than an IRQ number, and the pointer moves only on an accept so a stalled consumer cannot walk it round the ring |
| 1.3 | 2026-09-11 | RTL Design Sherpa | LowestPriority delivery, DELEGATED. An IOAPIC does not track CPU priority and never did: on the APIC bus it broadcast the message and the local APICs arbitrated among themselves on their Arbitration Priority Registers, and whichever was lowest accepted. The destination, destination mode and delivery mode were therefore already forwarded unmodified, and the half this block lacked was never the choosing -- it was being told the choice FAILED. `irq_out_retry`, qualified by the delivery handshake, is that half. The core now separates two events that used to be one: a completed handshake frees the output stage and moves the rotation, while an ACCEPTED one (completed and not retried) is what retires an edge latch, sets Remote IRR and latches the delivered vector, so a refused interrupt is re-offered rather than lost. Tie the pin low and the channel is bit-identical to before. In the CDC build the refusal is captured in pclk on the same edge as the acknowledge and crosses back inside that bundle rather than through a synchronizer of its own, so it cannot land a cycle away from the strobe that qualifies it (handbook CDC rule 7). Under STATIC priority a refused pin wins the next arbitration immediately and a persistent refusal monopolises the channel; round robin is the fix, as it is for static priority's starvation everywhere else here |

## Navigation

### Quick Navigation

**For Software Developers:**
- Reference [Chapter 5: Registers](ch05_registers/01_register_map.md)
- **Critical:** Understand the IOREGSEL/IOWIN indirect access method (see the register map; a dedicated indirect-access section is planned)

**For Hardware Integrators:**
- Start with [Chapter 1: Overview](ch01_overview/01_overview.md)
- Chapter 3 (interfaces/signal list) is planned but not yet written; see `../../rtl/ioapic/apb4_ioapic.sv` for the current port list

**For Verification Engineers:**
- Start with [Chapter 2: Blocks](ch02_blocks/00_overview.md)
- Reference [FSM Summary](ch02_blocks/05_fsm_summary.md)

**For System Architects:**
- Start with [Architecture Overview](ch01_overview/02_architecture.md)
- Programming-model chapters (initialization, redirection table, use cases) are planned but not yet written
