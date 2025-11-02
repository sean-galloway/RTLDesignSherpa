# APB HPET - High Precision Event Timer

**This documentation has moved!**

---

## Documentation Location

The complete APB HPET documentation is now maintained in the project directory:

📖 **[APB HPET Complete Specification](../../../projects/components/apb_hpet/docs/hpet_spec/hpet_index.md)**

---

## Quick Links

### Component Documentation
- **Specification Index:** [hpet_spec/hpet_index.md](../../../projects/components/apb_hpet/docs/hpet_spec/hpet_index.md)
- **Overview:** [ch01_overview/01_overview.md](../../../projects/components/apb_hpet/docs/hpet_spec/ch01_overview/01_overview.md)
- **Architecture:** [ch01_overview/02_architecture.md](../../../projects/components/apb_hpet/docs/hpet_spec/ch01_overview/02_architecture.md)
- **Block Descriptions:** [ch02_blocks/](../../../projects/components/apb_hpet/docs/hpet_spec/ch02_blocks/)
- **Register Map:** [ch05_registers/01_register_map.md](../../../projects/components/apb_hpet/docs/hpet_spec/ch05_registers/01_register_map.md)

### Project Files
- **Product Requirements:** [PRD.md](../../../projects/components/apb_hpet/PRD.md)
- **AI Guide:** [CLAUDE.md](../../../projects/components/apb_hpet/CLAUDE.md)
- **Implementation Status:** [docs/IMPLEMENTATION_STATUS.md](../../../projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md)
- **Source Code:** [rtl/](../../../projects/components/apb_hpet/rtl/)
- **Tests:** [dv/tests/](../../../projects/components/apb_hpet/dv/tests/)

---

## Quick Summary

**Status:** ✅ Production Ready (5/6 configurations passing at 100%)

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
**[projects/components/apb_hpet/docs/hpet_spec/hpet_index.md](../../../projects/components/apb_hpet/docs/hpet_spec/hpet_index.md)**

---

**Return to:** [Component Projects Index](index.md)

**Last Updated:** 2025-10-20
