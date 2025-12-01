# APB RTC Specification - Table of Contents

**Component:** APB Real-Time Clock (RTC) Controller
**Version:** 1.0
**Last Updated:** 2025-12-01
**Status:** Production Ready

---

## Document Organization

This specification is organized into five chapters covering all aspects of the APB RTC component:

### Chapter 1: Overview
**Location:** `ch01_overview/`

- [01_overview.md](ch01_overview/01_overview.md) - Component overview, features, applications
- [02_architecture.md](ch01_overview/02_architecture.md) - High-level architecture
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock domains and reset
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External references

### Chapter 2: Blocks
**Location:** `ch02_blocks/`

- [00_overview.md](ch02_blocks/00_overview.md) - Block hierarchy overview
- [01_apb_interface.md](ch02_blocks/01_apb_interface.md) - APB interface block
- [02_time_counter.md](ch02_blocks/02_time_counter.md) - Time keeping logic
- [03_alarm.md](ch02_blocks/03_alarm.md) - Alarm comparison
- [04_interrupt.md](ch02_blocks/04_interrupt.md) - Interrupt generation

### Chapter 3: Interfaces
**Location:** `ch03_interfaces/`

- [00_overview.md](ch03_interfaces/00_overview.md) - Interface summary
- [01_apb_slave.md](ch03_interfaces/01_apb_slave.md) - APB protocol specification
- [02_interrupt.md](ch03_interfaces/02_interrupt.md) - Interrupt output
- [03_system.md](ch03_interfaces/03_system.md) - Clock and reset interface

### Chapter 4: Programming Model
**Location:** `ch04_programming/`

- [00_overview.md](ch04_programming/00_overview.md) - Programming overview
- [01_initialization.md](ch04_programming/01_initialization.md) - RTC initialization
- [02_time_operations.md](ch04_programming/02_time_operations.md) - Reading/setting time
- [03_alarm.md](ch04_programming/03_alarm.md) - Alarm configuration
- [04_examples.md](ch04_programming/04_examples.md) - Programming examples

### Chapter 5: Registers
**Location:** `ch05_registers/`

- [01_register_map.md](ch05_registers/01_register_map.md) - Complete register map

---

## Block Diagram

![APB RTC Block Diagram](assets/svg/rtc_top.svg)

---

## Quick Navigation

### For Software Developers
- Start with [Chapter 4: Programming Model](ch04_programming/00_overview.md)
- Reference [Chapter 5: Registers](ch05_registers/01_register_map.md)

### For Hardware Integrators
- Start with [Chapter 1: Overview](ch01_overview/01_overview.md)
- Reference [Chapter 3: Interfaces](ch03_interfaces/00_overview.md)

---

## Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-12-01 | RTL Design Sherpa | Initial specification |

---

**Related Documentation:**
- [PRD.md](../../PRD.md) - Product Requirements Document
