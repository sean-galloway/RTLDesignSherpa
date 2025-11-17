# IOAPIC (I/O Advanced Programmable Interrupt Controller) TODO List

## Status: Foundation Complete - Ready for Core Implementation

### Completed ✅
- [x] PeakRDL register specification (ioapic_regs.rdl)
  - Indirect register access (IOREGSEL/IOWIN)
  - 24 IRQ redirection table entries
  - Edge/level trigger support
  - Polarity configuration
  - Delivery modes defined
  - Destination routing
- [x] PeakRDL register generation (ioapic_regs.sv, ioapic_regs_pkg.sv)

### High Priority 🔴

#### Core Implementation
- [ ] **ioapic_core.sv** - Core interrupt controller logic
  - IRQ input synchronization (24 inputs)
  - Edge detection logic
  - Level sensing logic  
  - Polarity inversion (active high/low)
  - Priority arbitration (lowest IRQ number wins for MVP)
  - Interrupt delivery FSM
  - Remote IRR management for level-triggered
  - Delivery status tracking

#### Configuration Registers with Indirect Access
- [ ] **ioapic_config_regs.sv** - Special wrapper for indirect access
  - **IOREGSEL/IOWIN mechanism:**
    - Decode IOREGSEL to select internal register
    - Route IOWIN reads/writes based on IOREGSEL
    - Handle 64-bit redirection entries (2×32-bit access)
  - **Instantiate peakrdl_to_cmdrsp adapter**
  - **Instantiate generated ioapic_regs**
  - **Map hwif to ioapic_core:**
    - IOAPICID, IOAPICVER, IOAPICARB
    - Redirection table array [24] with LO/HI registers
    - Vector, delivery_mode, dest_mode, polarity, trigger, mask, destination
    - Read-only fields: delivery_status, remote_irr
  - **Handle indirect register access correctly**

#### APB Wrapper
- [ ] **apb_ioapic.sv** - APB top-level with CDC support
  - CDC_ENABLE parameter (0=single, 1=dual clock)
  - Conditional apb_slave vs apb_slave_cdc
  - Instantiate ioapic_config_regs
  - Instantiate ioapic_core
  - Wire 24 IRQ inputs to core
  - Wire interrupt output from core

#### Support Files
- [ ] **filelists/apb_ioapic.f** - Build filelist
- [ ] **peakrdl/README.md** - Register access documentation
- [ ] **README.md** - Update with implementation details
- [ ] **IMPLEMENTATION_STATUS.md** - Status tracking

### Medium Priority 🟡

#### Enhanced Features
- [ ] **Logical Destination Mode**
  - Logical destination decoding
  - Multi-CPU logical addressing

- [ ] **LowestPriority Delivery Mode**
  - CPU priority tracking
  - Dynamic arbitration to lowest priority CPU

- [ ] **Additional Delivery Modes**
  - SMI (System Management Interrupt)
  - NMI (Non-Maskable Interrupt)
  - INIT (Initialization)
  - ExtINT (External Interrupt)

- [ ] **Dynamic Priority Rotation**
  - Round-robin among equal priority IRQs
  - Prevent starvation

- [ ] **Enhanced Arbitration**
  - User-programmable priorities
  - Priority grouping
  - Fairness algorithms

### Low Priority 🟢

#### Advanced Features
- [ ] **Multi-IOAPIC Support**
  - APIC ID routing
  - Inter-APIC communication
  - Global arbitration

- [ ] **Boot Interrupt Delivery**
  - Boot processor detection
  - INIT-SIPI-SIPI sequence

- [ ] **Message Signaled Interrupts (MSI)**
  - MSI capability
  - MSI-X support

### Implementation Notes

**Indirect Register Access (Critical):**
The IOAPIC uses Intel's indirect access method which differs from other RLB modules:

```systemverilog
// Software access pattern:
// 1. Write to IOREGSEL (0x00): Select internal register offset
// 2. Access IOWIN (0x04): Read/write selected register data

// Implementation in ioapic_config_regs.sv:
always_comb begin
    case (ioregsel)
        8'h00: iowin_data = ioapicid;
        8'h01: iowin_data = ioapicver;
        8'h02: iowin_data = ioapicarb;
        8'h10: iowin_data = ioredtbl[0].lo;
        8'h11: iowin_data = ioredtbl[0].hi;
        8'h12: iowin_data = ioredtbl[1].lo;
        ...
    endcase
end
```

**Redirection Table Array Handling:**
- 24 entries × 2 registers (LO/HI) = 48 internal registers
- Internal offsets 0x10-0x3F
- Need array indexing: `entry_num = (regsel - 8'h10) >> 1`
- LO/HI select: `is_hi = regsel[0]`

**Priority Arbitration (MVP):**
Simple static priority:
```systemverilog
// Find lowest numbered unmasked, pending IRQ
for (int i = 0; i < 24; i++) begin
    if (irq_pending[i] && !irq_masked[i]) begin
        selected_irq = i;
        break;
    end
end
```

**Edge vs Level Handling:**
- **Edge:** Latch on rising/falling edge, clear on EOI
- **Level:** Track input level, Remote IRR=1 when accepted, clear on EOI
- **Polarity:** Invert input if active-low configured

### Testing Checklist

- [ ] APB register access to IOREGSEL
- [ ] APB register access to IOWIN
- [ ] Indirect read of IOAPICID
- [ ] Indirect read of IOAPICVER (check 0x11 and 0x17)
- [ ] Indirect read of IOAPICARB
- [ ] Indirect write/read of redirection table entries
- [ ] Configure IRQ0 for edge-triggered, active-high
- [ ] Assert IRQ0, verify interrupt delivery
- [ ] Configure IRQ1 for level-triggered, active-low
- [ ] Assert IRQ1, verify Remote IRR set
- [ ] Test interrupt masking per IRQ
- [ ] Test multiple pending IRQs (priority)
- [ ] Test delivery status flag
- [ ] Test all 24 IRQ inputs
- [ ] Test polarity inversion (active high/low)
- [ ] Test trigger mode (edge/level)
- [ ] Verify EOI clears Remote IRR
- [ ] CDC mode functional test

### Key Design Decisions

**MVP Scope:**
- Fixed delivery mode only (000)
- Physical destination mode only
- Single CPU target
- Static priority (lowest IRQ number)
- Edge and level trigger supported
- Active high/low polarity supported

**Deferred to Future:**
- Logical destination mode
- LowestPriority delivery mode
- SMI, NMI, INIT, ExtINT modes
- Multi-CPU arbitration
- Dynamic priority
- Boot interrupt support

**RLB Compliance:**
- ✅ Use existing peakrdl_to_cmdrsp
- ✅ Follow HPET/PM_ACPI APB wrapper pattern
- ✅ CDC_ENABLE parameter
- ✅ 12-bit addressing
- ⚠️ Special indirect access in config_regs

### Reference Files

**Pattern References:**
- `projects/components/retro_legacy_blocks/rtl/pm_acpi/` - Most recent complete example
- `projects/components/retro_legacy_blocks/rtl/hpet/` - Solid reference pattern
- `projects/components/retro_legacy_blocks/rtl/pic_8259/` - Simple interrupt controller

**Key Patterns:**
- APB wrapper: `apb_pm_acpi.sv`, `apb_hpet.sv`
- Config regs: `pm_acpi_config_regs.sv`, `hpet_config_regs.sv`
- Core logic: `pm_acpi_core.sv`, `pic_8259_core.sv`

### Integration Requirements

**System Connections:**
- Connect 24 `irq_in[23:0]` signals from system interrupt sources
- Connect `irq_out` to CPU interrupt controller (e.g., LAPIC)
- Configure redirection table entries for each IRQ:
  - Vector: Interrupt number to deliver
  - Delivery mode: Fixed (000) for MVP
  - Destination: Target CPU ID
  - Trigger: Edge (0) or Level (1)
  - Polarity: Active high (0) or low (1)
  - Mask: 0=enable, 1=disable

**Typical Configuration:**
```
IRQ0  (Timer)     -> Vector 0x20, Edge, Active High
IRQ1  (Keyboard)  -> Vector 0x21, Edge, Active High
IRQ8  (RTC)       -> Vector 0x28, Edge, Active High
IRQ14 (IDE)       -> Vector 0x2E, Edge, Active High
IRQ15 (IDE)       -> Vector 0x2F, Edge, Active High
```

---

**Last Updated:** 2025-11-16  
**Status:** Foundation Complete - Core Implementation Needed
