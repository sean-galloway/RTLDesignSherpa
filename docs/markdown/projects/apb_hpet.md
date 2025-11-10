# APB HPET - High Precision Event Timer

**NOTICE: This component has been relocated!**

---

## Component Location Update

The APB HPET is now part of the **Retro Legacy Blocks** collection, which consolidates legacy and retro-computing peripherals for historical SoC designs.

**New Location:** `projects/components/retro_legacy_blocks/`

---

## Documentation Location

The complete APB HPET documentation is now maintained in the retro_legacy_blocks project directory:

📖 **[HPET Complete Specification](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md)**

---

## Quick Links

### Component Documentation
- **Specification Index:** [hpet_spec/hpet_index.md](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md)
- **Overview:** [ch01_overview/01_overview.md](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/ch01_overview/01_overview.md)
- **Architecture:** [ch01_overview/02_architecture.md](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/ch01_overview/02_architecture.md)
- **Block Descriptions:** [ch02_blocks/](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/ch02_blocks/)
- **Register Map:** [ch05_registers/01_register_map.md](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/ch05_registers/01_register_map.md)

### Project Files
- **Product Requirements:** [PRD.md](../../../projects/components/retro_legacy_blocks/PRD.md)
- **AI Guide:** [CLAUDE.md](../../../projects/components/retro_legacy_blocks/CLAUDE.md)
- **Implementation Status:** [docs/IMPLEMENTATION_STATUS.md](../../../projects/components/retro_legacy_blocks/docs/IMPLEMENTATION_STATUS.md)
- **Source Code:** [rtl/hpet/](../../../projects/components/retro_legacy_blocks/rtl/hpet/)
- **Tests:** [dv/tests/hpet/](../../../projects/components/retro_legacy_blocks/dv/tests/hpet/)

---

## Retro Legacy Blocks Collection

The HPET is now part of a collection that includes:

- **HPET** - High Precision Event Timer (APB interface)
- **8259 PIC** - Programmable Interrupt Controller
- **8254 PIT** - Programmable Interval Timer
- **RTC** - Real-Time Clock
- **SMBUS** - System Management Bus controller
- **PM/ACPI** - Power Management / Advanced Configuration and Power Interface
- **IOAPIC** - I/O Advanced Programmable Interrupt Controller

📋 **[View Complete Collection](../../../projects/components/retro_legacy_blocks/README.md)**

---

## Quick Summary

**Status:** ✅ Stable (Part of Retro Legacy Blocks collection)

Multi-timer peripheral with 64-bit counter, one-shot/periodic modes, and optional clock domain crossing.

**Key Features:**
- Configurable 2, 3, or 8 independent timers
- 64-bit main counter and comparators
- APB4 interface with optional CDC
- PeakRDL-based register generation
- Comprehensive CocoTB verification

**Applications:**
- System tick generation
- Real-time OS scheduling
- Precise event timing
- Performance profiling
- Watchdog timers

---

**For complete documentation, please visit:**
**[projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md)**

---

**Return to:** [Component Projects Index](index.md)

**Last Updated:** 2025-11-05
