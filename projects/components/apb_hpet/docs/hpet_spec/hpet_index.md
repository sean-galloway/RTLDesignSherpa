# APB HPET Specification - Table of Contents

**Component:** APB High Precision Event Timer (HPET)
**Version:** 1.0
**Last Updated:** 2025-10-18
**Status:** Production Ready (5/6 configurations 100% passing)

---

## Document Organization

This specification is organized into five chapters covering all aspects of the APB HPET component:

### Chapter 1: Overview
**Location:** `ch01_overview/`

- [01_overview.md](ch01_overview/01_overview.md) - Component overview, features, applications
- [02_architecture.md](ch01_overview/02_architecture.md) - High-level architecture and block hierarchy
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock domains and reset behavior
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External references and standards

### Chapter 2: Blocks
**Location:** `ch02_blocks/`

- [00_overview.md](ch02_blocks/00_overview.md) - Block hierarchy overview
- [01_hpet_core.md](ch02_blocks/01_hpet_core.md) - Core timer logic (counter, comparators, FSM)
- [02_hpet_config_regs.md](ch02_blocks/02_hpet_config_regs.md) - Configuration register wrapper
- [03_hpet_regs.md](ch02_blocks/03_hpet_regs.md) - PeakRDL generated register file
- [04_apb_hpet_top.md](ch02_blocks/04_apb_hpet_top.md) - Top-level integration
- [05_fsm_summary.md](ch02_blocks/05_fsm_summary.md) - FSM state summary table

**PlantUML Diagrams:** `puml/`
- [hpet_core_fsm.puml](puml/hpet_core_fsm.puml) - HPET core timer FSM
- [timer_config_fsm.puml](puml/timer_config_fsm.puml) - Timer configuration FSM

### Chapter 3: Interfaces
**Location:** `ch03_interfaces/`

- [01_top_level.md](ch03_interfaces/01_top_level.md) - Top-level signal list
- [02_apb_interface_spec.md](ch03_interfaces/02_apb_interface_spec.md) - APB protocol specification
- [03_hpet_clock_interface.md](ch03_interfaces/03_hpet_clock_interface.md) - HPET clock domain interface
- [04_interrupt_interface.md](ch03_interfaces/04_interrupt_interface.md) - Timer interrupt outputs

### Chapter 4: Programming Model
**Location:** `ch04_programming/`

- [01_initialization.md](ch04_programming/01_initialization.md) - Software initialization sequence
- [02_timer_configuration.md](ch04_programming/02_timer_configuration.md) - Configuring timers (one-shot, periodic)
- [03_interrupt_handling.md](ch04_programming/03_interrupt_handling.md) - Interrupt service routines
- [04_use_cases.md](ch04_programming/04_use_cases.md) - Common use case examples

### Chapter 5: Registers
**Location:** `ch05_registers/`

- [01_register_map.md](ch05_registers/01_register_map.md) - Complete register address map and field descriptions

---

## Quick Navigation

### For Software Developers
- Start with [Chapter 4: Programming Model](ch04_programming/01_initialization.md)
- Reference [Chapter 5: Registers](ch05_registers/01_register_map.md)

### For Hardware Integrators
- Start with [Chapter 1: Overview](ch01_overview/01_overview.md)
- Reference [Chapter 3: Interfaces](ch03_interfaces/01_top_level.md)

### For Verification Engineers
- Start with [Chapter 2: Blocks](ch02_blocks/00_overview.md)
- Reference [FSM Summary](ch02_blocks/05_fsm_summary.md)

### For System Architects
- Start with [Architecture Overview](ch01_overview/02_architecture.md)
- Reference [Use Cases](ch04_programming/04_use_cases.md)

---

## Document Conventions

### Notation
- **bold** - Important terms, signal names
- `code` - Register names, field names, code examples
- *italic* - Emphasis, notes

### Signal Naming
- `pclk` - APB clock
- `hpet_clk` - HPET timer clock
- `timer_irq[N]` - Timer interrupt outputs

### Register Notation
- `HPET_CONFIG` - Register name
- `HPET_CONFIG[0]` - Specific bit field
- `0x000` - Register address (hexadecimal)

---

## Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-10-18 | RTL Design Sherpa | Initial specification based on production-ready implementation |

---

**Related Documentation:**
- [PRD.md](../../PRD.md) - Product Requirements Document
- [CLAUDE.md](../../CLAUDE.md) - AI integration guide
- [TASKS.md](../../TASKS.md) - Development tasks and status
- [IMPLEMENTATION_STATUS.md](../IMPLEMENTATION_STATUS.md) - Test results and validation status
