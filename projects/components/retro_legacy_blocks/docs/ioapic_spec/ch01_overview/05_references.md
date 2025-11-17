### APB IOAPIC - References

#### Primary Standards

1. **Intel 82093AA I/O Advanced Programmable Interrupt Controller (IOAPIC)**
   - Intel Corporation
   - May 1996
   - Document Order Number: 290566-001
   - **Purpose:** Defines IOAPIC register layout, indirect access method, and behavior
   - **Relevance:** APB IOAPIC implements this specification with APB interface

2. **AMBA APB Protocol Specification**
   - ARM Limited
   - AMBA 4 APB Protocol Specification v2.0
   - **Purpose:** Defines APB4 bus protocol
   - **Relevance:** APB interface implementation

3. **SystemRDL 2.0 Specification**
   - Accellera Systems Initiative
   - **Purpose:** Register description language
   - **Relevance:** PeakRDL register generation from .rdl specifications

#### Related RLB Documentation

**Module-Specific:**
- `../../rtl/ioapic/TODO.md` - Implementation tasks and enhancements
- `../../rtl/ioapic/peakrdl/README.md` - PeakRDL register generation guide
- `../../rtl/ioapic/peakrdl/ioapic_regs.rdl` - SystemRDL source specification

**RLB System:**
- `../../rtl/RLB_MODULE_AUDIT.md` - Architecture compliance verification
- `../../rtl/RLB_STATUS_AND_ROADMAP.md` - System-wide status and planning
- `../../rtl/RLB_FPGA_IMPLEMENTATION_GUIDE.md` - FPGA deployment guide
- `../../PRD.md` - Product Requirements Document
- `../../CLAUDE.md` - AI integration guide

**Reference RLB Modules:**
- `../hpet_spec/hpet_index.md` - HPET specification (architectural reference)
- `../../rtl/pic_8259/README.md` - Legacy PIC implementation
- `../../rtl/pm_acpi/README.md` - Power management and ACPI

#### External Resources

**Intel APIC Architecture:**
- Intel MultiProcessor Specification Version 1.4
- Intel Architecture Software Developer's Manual (Volume 3: System Programming)
- **Relevance:** APIC system architecture, LAPIC integration, interrupt delivery

**AMBA Specifications:**
- AMBA APB Protocol Specification v2.0 (ARM IHI 0024)
- AMBA AXI and ACE Protocol Specification (for AXI-APB bridges)
- **Relevance:** Bus protocol compliance

**SystemRDL Tools:**
- PeakRDL-regblock Documentation
- PeakRDL-html Documentation
- SystemRDL 2.0 Language Reference Manual
- **Relevance:** Register generator usage

#### Design Methodology References

**RLB Architecture Pattern:**
```
APB → apb_slave[_cdc] → CMD/RSP → peakrdl_to_cmdrsp → 
  → <module>_regs (PeakRDL) → hwif → <module>_core
```

**Reference Implementations:**
- HPET: Complete reference with CDC, PeakRDL, documentation
- PM_ACPI: Recent implementation, similar complexity
- SMBus: Protocol controller with FIFOs

**Converter Components:**
- `../../converters/rtl/apb_slave.sv` - APB slave without CDC
- `../../converters/rtl/apb_slave_cdc.sv` - APB slave with CDC
- `../../converters/rtl/peakrdl_to_cmdrsp.sv` - PeakRDL adapter

#### Historical Context

**Evolution of PC Interrupt Controllers:**

1. **Intel 8259A PIC (1976-1990s)**
   - 8 IRQ inputs, cascadable to 15
   - Fixed priority
   - Edge-triggered only
   - Direct memory-mapped access

2. **Intel 82093AA IOAPIC (1996-present)**
   - 24 IRQ inputs
   - Programmable priority
   - Edge and level-triggered
   - Indirect register access
   - Multi-processor support
   - **This implementation**

3. **MSI/MSI-X (2000s-present)**
   - Message-based interrupts
   - No dedicated IRQ lines
   - Scalable to thousands of interrupts
   - PCIe standard

**APB IOAPIC Position:**
Modern implementation of 82093AA specification using RLB methodology, suitable for soft-core SoCs, FPGA systems, and PC-compatible designs.

#### Software Examples and Drivers

**Linux Kernel:**
- `arch/x86/kernel/apic/io_apic.c` - Linux IOAPIC driver
- Shows real-world usage patterns
- Demonstrates edge/level handling, EOI, redirection table setup

**xv6 Operating System:**
- `ioapic.c` - Simple IOAPIC driver for educational OS
- Clean example of indirect access
- Good reference for basic initialization

**SeaBIOS / Coreboot:**
- BIOS-level IOAPIC initialization
- Shows boot-time configuration
- Demonstrates hardware discovery

#### Verification References

**Cocotb (Python-based Verification):**
- Cocotb documentation: https://docs.cocotb.org/
- Used for RLB module validation
- Tests in `../../dv/tests/` directories

**Verification Strategy:**
- Similar to HPET: Basic → Medium → Full test hierarchy
- Test levels defined in RLB_STATUS_AND_ROADMAP.md
- Estimated 5-7 days for complete validation

---

**Document Navigation:**
- [Back to Index](../ioapic_index.md)
- [Overview](01_overview.md)
- [Architecture](02_architecture.md)
- [Acronyms](04_acronyms.md)
