### APB IOAPIC - Overview

#### Introduction

The APB I/O Advanced Programmable Interrupt Controller (IOAPIC) is a sophisticated interrupt routing peripheral designed for advanced system interrupt management. It provides 24 programmable interrupt inputs with flexible redirection to multiple CPUs, supporting both edge and level-triggered modes. The design implements Intel 82093AA-compatible indirect register access while integrating seamlessly with the RLB architecture via AMBA APB4 interface.

#### Key Features

- **24 Independent IRQ Inputs**: IRQ0-IRQ23 with individual configuration per interrupt source
- **Programmable Redirection Table**: 64-bit entry per IRQ defining vector, mode, destination, trigger, polarity
- **Indirect Register Access**: Intel-compatible IOREGSEL/IOWIN mechanism for register access
- **Dual Trigger Modes**: 
  - **Edge-triggered**: Latches interrupt on signal edge, fires once
  - **Level-triggered**: Tracks signal level, uses Remote IRR, requires EOI
- **Configurable Polarity**: Active-high or active-low per IRQ input
- **Priority Arbitration**: Static priority (lowest IRQ number wins for MVP)
- **Delivery Modes**: Fixed mode (MVP), with support for LowestPri, SMI, NMI, INIT, ExtINT (future)
- **Remote IRR**: Level-triggered interrupt tracking with End-of-Interrupt (EOI) handling
- **APB Interface**: Standard AMBA APB4 compliant with 12-bit addressing
- **Clock Domain Crossing**: Optional CDC support via CDC_ENABLE parameter 
- **PeakRDL Integration**: Register map generated from SystemRDL specification
- **Intel 82093AA Compatible**: Register layout and behavior match Intel specification

#### Applications

**Multi-Processor Systems:**
- Flexible interrupt routing to multiple CPUs
- Per-IRQ destination configuration
- Delivery mode selection per interrupt
- Scalable interrupt distribution

**PC-Compatible Systems:**
- x86 PC interrupt architecture
- ISA bus interrupt routing
- PCI interrupt support (INTA-INTD mapping)
- Legacy IRQ redirection (IRQ0-15)

**Embedded Systems:**
- Complex interrupt topologies
- Priority-based interrupt handling
- Mixed edge/level interrupt sources
- Polarity-agnostic interrupt inputs

**System Management:**
- Interrupt masking per source
- Delivery status monitoring
- Remote IRR tracking
- Flexible interrupt mapping

#### Design Philosophy

**Intel Compatibility:**
The IOAPIC implements the Intel 82093AA indirect register access method (IOREGSEL/IOWIN) for compatibility with existing software. This allows software written for Intel chipsets to work with minimal modifications.

**Flexibility:**
Each of the 24 IRQ inputs can be independently configured for trigger mode (edge/level), polarity (active-high/low), delivery mode, destination CPU, and interrupt vector. This flexibility supports diverse system architectures.

**Reliability:**
- 3-stage input synchronization prevents metastability
- Edge detection with glitch immunity
- Remote IRR prevents level interrupt re-triggering until EOI
- Delivery status tracking ensures reliable interrupt delivery

**Standards Compliance:**
- **APB Protocol**: Full AMBA APB4 specification compliance
- **PeakRDL**: Industry-standard SystemRDL for register generation
- **Intel 82093AA**: Register layout and access method compatibility
- **Reset Convention**: Consistent active-low asynchronous reset

**Modularity:**
Clean separation between interrupt routing logic (ioapic_core), register interface (ioapic_config_regs), and bus interface (apb_ioapic) enables easy customization and integration.

#### Comparison with Intel 82093AA IOAPIC

The APB IOAPIC draws directly from the Intel 82093AA I/O APIC specification with RLB architecture enhancements:

| Feature | Intel 82093AA | APB IOAPIC |
|---------|---------------|------------|
| **Interface** | Memory-mapped | AMBA APB4 |
| **Register Access** | Indirect (IOREGSEL/IOWIN) | Indirect (IOREGSEL/IOWIN) ✅ Same |
| **IRQ Inputs** | 24 (IRQ0-23) | 24 (IRQ0-23) ✅ Same |
| **Redirection Table** | 24 entries × 64-bit | 24 entries × 64-bit ✅ Same |
| **Delivery Modes** | Fixed, LowestPri, SMI, NMI, INIT, ExtINT | Fixed (MVP), others future |
| **Destination Modes** | Physical, Logical | Physical (MVP), Logical future |
| **Trigger Modes** | Edge, Level | Edge, Level ✅ Same |
| **Polarity** | High, Low | High, Low ✅ Same |
| **Version Register** | 0x11, Max Entry 0x17 | 0x11, Max Entry 0x17 ✅ Same |
| **Remote IRR** | Level interrupts | Level interrupts ✅ Same |
| **Priority** | Implementation-defined | Static (lowest IRQ) |
| **Multi-APIC** | Supported | Future enhancement |
| **Clock Domains** | Single | Optional CDC support |

**Retained Features:**
- Indirect register access method
- Redirection table structure
- Edge/level trigger modes
- Polarity configuration
- Remote IRR mechanism
- Delivery/destination fields

**MVP Simplifications:**
- Fixed delivery mode only (LowestPri, SMI, NMI, INIT, ExtINT future)
- Physical destination only (Logical mode future)
- Static priority only (dynamic/round-robin future)
- Single IOAPIC (multi-IOAPIC arbitration future)

**RLB Enhancements:**
-  APB4 bus interface (instead of direct memory-map)
- Optional CDC for clock domain flexibility
- PeakRDL register generation
- Modern SystemVerilog coding practices
- Comprehensive validation framework

#### Performance Characteristics

**Interrupt Latency:**
- IRQ detection: 3 clock cycles (synchronization)
- Edge detection: 1 clock cycle
- Arbitration: Combinational (<1 cycle)
- Delivery initiation: 1 clock cycle
- **Total:** ~5 clock cycles from IRQ assertion to delivery request

**Register Access Performance:**
- Direct APB access (IOREGSEL): 2 APB clock cycles
- Indirect access (IOWIN): 2 APB clock cycles per register
- Full redirection entry (LO+HI): 4 APB clock cycles total
- With CDC: Add 2-4 cycles for synchronization

**Resource Utilization (Post-Synthesis Estimates):**
- No CDC: ~800-1000 LUTs, ~600-800 flip-flops
- With CDC: ~1000-1200 LUTs, ~800-1000 flip-flops
- BRAM: None (all logic-based)

**Scalability:**
Fixed 24 IRQ inputs per Intel specification. For more IRQs, use multiple IOAPIC instances with different APIC IDs.

#### Verification Status

**Implementation Status:** ✅ RTL Complete - Validation Pending

**Completed Implementation:**
- ✅ PeakRDL register specification with indirect access
- ✅ Core interrupt routing logic (edge/level/polarity)
- ✅ Priority arbitration (static)
- ✅ Delivery state machine with EOI handling
- ✅ Remote IRR management
- ✅ Configuration register wrapper
- ✅ APB top-level with CDC support
- ✅ Complete filelist and documentation

**Validation Plan (Per TODO.md):**
- ⏳ APB indirect register access tests
- ⏳ Edge-triggered IRQ tests (all 24 inputs)
- ⏳ Level-triggered IRQ tests with Remote IRR
- ⏳ Polarity tests (active-high/low)
- ⏳ Priority arbitration tests
- ⏳ Delivery status tests
- ⏳ EOI handling with level interrupts
- ⏳ Redirection table configuration tests
- ⏳ CDC mode validation

**Test Infrastructure Needed:**
- Python helper script (ioapic_helper.py)
- Cocotb testbench (ioapic_tb.py)
- Test suite (test_apb_ioapic.py)

**Estimated Validation Time:** 5-7 days (per RLB_STATUS_AND_ROADMAP.md)

#### Development Status

**Status:** ✅ MVP Complete - Ready for Validation

**MVP Scope Delivered:**
- ✅ 24 IRQ inputs with synchronization
- ✅ Edge and level trigger detection
- ✅ Active high/low polarity support
- ✅ Fixed delivery mode
- ✅ Physical destination mode
- ✅ Static priority arbitration
- ✅ Remote IRR for level interrupts
- ✅ EOI handling
- ✅ Indirect register access (IOREGSEL/IOWIN)
- ✅ Complete redirection table
- ✅ Delivery status per IRQ

**Future Enhancements (Planned in TODO.md):**
- ⏳ Logical destination mode
- ⏳ LowestPriority delivery mode
- ⏳ Additional delivery modes (SMI, NMI, INIT, ExtINT)
- ⏳ Dynamic priority rotation
- ⏳ Multi-IOAPIC support
- ⏳ Boot interrupt delivery

#### Intel 82093AA Register Compatibility

**Direct APB Registers:**
- `0x00`: IOREGSEL - Register offset selector
- `0x04`: IOWIN - Data window for selected register

**Internal Registers (via IOREGSEL/IOWIN):**
- **0x00**: IOAPICID - I/O APIC identification
- **0x01**: IOAPICVER - Version (0x11) and Max Entry (0x17 for 24 IRQs)
- **0x02**: IOAPICARB - Arbitration priority (read-only)
- **0x10-0x3F**: IOREDTBL - Redirection table (24 entries × 2 registers)

Each redirection entry is 64 bits:
- **LO register**: Vector, delivery mode, dest mode, polarity, trigger, mask, status fields
- **HI register**: Destination CPU APIC ID

This matches Intel's specification exactly for software compatibility.

#### Documentation Organization

This specification document is organized as follows:

- **Chapter 1 (this chapter)**: Overview, features, applications, Intel compatibility
- **Chapter 2**: Detailed block specifications (ioapic_core, config_regs, PeakRDL integration)
- **Chapter 3**: Interface specifications (APB, indirect access, IRQ, EOI)
- **Chapter 4**: Programming model (initialization, redirection table, edge/level handling)
- **Chapter 5**: Register definitions (address map, indirect access, field descriptions)

**Related Documentation:**
- `../../rtl/ioapic/TODO.md` - Implementation roadmap
- `../../rtl/ioapic/peakrdl/README.md` - Register generation guide
- `../../rtl/RLB_STATUS_AND_ROADMAP.md` - System-wide planning
- Intel 82093AA I/O APIC Datasheet

---

**Next:** [Chapter 1.2 - Architecture](02_architecture.md)
