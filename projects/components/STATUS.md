# Components Status Overview

**Last Updated:** 2025-10-19

## Component Status Summary

| Component | Status | Current Phase | Next Milestone |
|-----------|--------|---------------|----------------|
| **RAPIDS** | 🟡 Active | Validation (80% coverage) | Complete descriptor engine stress testing |
| **Delta** | 🟡 Active | Early specification (v0.3) | Router RTL implementation |
| **HIVE** | 🟢 New | Specification (Ch1 complete) | Complete Ch2-5 specifications |
| **HPET** | 🟢 Complete | Integration testing | Add wavedrom timing diagrams |
| **STREAM** | 🟢 Complete | Reference implementation | Documentation improvements |
| **Bridge** | 🟢 Complete | Reference implementation | Documentation improvements |

## Legend

- 🟢 **Complete/Stable** - Implementation done, documentation complete
- 🟡 **Active Development** - Implementation in progress or validation ongoing
- 🔴 **Blocked** - Waiting on dependencies or resources
- ⚪ **Not Started** - Planned but not yet initiated

## Quick Links

- **RAPIDS:** [STATUS](rapids/STATUS.md) | [PRD](rapids/PRD.md) | [CLAUDE](rapids/CLAUDE.md)
- **Delta:** [STATUS](delta/STATUS.md) | [PRD](delta/PRD.md) | [CLAUDE](delta/CLAUDE.md)
- **HIVE:** [STATUS](hive/STATUS.md) | [PRD](hive/PRD.md) | [CLAUDE](hive/CLAUDE.md)
- **HPET:** [STATUS](apb_hpet/STATUS.md) | [PRD](apb_hpet/PRD.md) | [CLAUDE](apb_hpet/CLAUDE.md)
- **STREAM:** [STATUS](stream/STATUS.md) | [PRD](stream/PRD.md) | [CLAUDE](stream/CLAUDE.md)
- **Bridge:** [STATUS](bridge/STATUS.md) | [PRD](bridge/PRD.md) | [CLAUDE](bridge/CLAUDE.md)

## Component Descriptions

### RAPIDS (Rapid AXI Programmable In-band Descriptor System)
Custom DMA engine with network interfaces and descriptor-based operation.
- **RTL:** 17 SystemVerilog modules
- **Pending:** Credit management test verification, stress testing

### Delta (Network-on-Chip)
4×4 mesh Network-on-Chip with intelligent packet routing.
- **RTL:** Specification phase
- **Pending:** Router implementation, crossbar logic

### HIVE (Hierarchical Intelligent Vector Environment)
Distributed control and monitoring subsystem (VexRiscv + 16 SERV monitors).
- **RTL:** Specification phase
- **Pending:** Complete specification chapters, RTL implementation

### HPET (High Precision Event Timer)
APB-based timer with multiple comparators and interrupt generation.
- **RTL:** Complete
- **Pending:** Wavedrom timing diagrams

### STREAM (Simplified Tutorial REference Accelerator Module)
Educational DMA tutorial project demonstrating basic accelerator patterns.
- **RTL:** Complete
- **Pending:** Documentation improvements

### Bridge (APB/AXI Bridge)
Protocol conversion bridge for APB ↔ AXI communication.
- **RTL:** Complete
- **Pending:** Documentation improvements

---

**For detailed status, see individual component STATUS.md files.**
