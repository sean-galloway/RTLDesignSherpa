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

# IOAPIC PeakRDL Register Specification

This directory contains the SystemRDL specification for IOAPIC (I/O Advanced Programmable Interrupt Controller) registers.

## Register Generation

To generate the SystemVerilog register files from the RDL specification:

```bash
cd projects/components/retro_legacy_blocks/rtl/ioapic/peakrdl
python ../../../../../../../bin/peakrdl_generate.py ioapic_regs.rdl
```

This will generate:
- `../ioapic_regs.sv` - Register block implementation
- `../ioapic_regs_pkg.sv` - Package with type definitions and structs

## Register Map Overview

The IOAPIC uses **indirect register access** following Intel 82093AA specification:

### Direct APB Access (0x00-0x0F)
- **IOREGSEL** (0x00): Register select - write internal register offset here
- **IOWIN** (0x04): Register window - read/write data for selected register

### Internal Registers (accessed via IOREGSEL/IOWIN)

**System Registers:**
- **IOAPICID** (offset 0x00): IOAPIC ID register
  - Bits [27:24]: 4-bit APIC ID for multi-IOAPIC systems
- **IOAPICVER** (offset 0x01): Version and capabilities
  - Bits [7:0]: Version (0x11 for 82093AA compatibility)
  - Bits [23:16]: Maximum redirection entry (0x17 = 23 for 24 IRQs)
- **IOAPICARB** (offset 0x02): Arbitration priority
  - Bits [27:24]: Arbitration ID (read-only, mirrors APIC ID)

**Redirection Table (offset 0x10-0x3F):**
Each of the 24 IRQs has a 64-bit redirection entry (2 × 32-bit registers):

- **IOREDTBL[n]_LO** (offset 0x10+2n): Lower 32 bits
  - Bits [7:0]: Vector - Interrupt vector to deliver (0x00-0xFF)
  - Bits [10:8]: Delivery Mode - 000=Fixed, 001=LowestPri, 010=SMI, etc.
  - Bit [11]: Destination Mode - 0=Physical, 1=Logical
  - Bit [12]: Delivery Status - 0=Idle, 1=Pending (read-only)
  - Bit [13]: Polarity - 0=Active High, 1=Active Low
  - Bit [14]: Remote IRR - Level interrupt state (read-only)
  - Bit [15]: Trigger Mode - 0=Edge, 1=Level
  - Bit [16]: Mask - 0=Enabled, 1=Masked

- **IOREDTBL[n]_HI** (offset 0x11+2n): Upper 32 bits
  - Bits [31:24]: Destination - Target CPU APIC ID

**Example redirection table offsets:**
```
IRQ0:  LO=0x10, HI=0x11
IRQ1:  LO=0x12, HI=0x13
IRQ2:  LO=0x14, HI=0x15
...
IRQ23: LO=0x3E, HI=0x3F
```

## Indirect Access Example

To configure IRQ0 for edge-triggered, active-high, unmask, vector 0x20:

```c
// 1. Select IOREDTBL0_LO (offset 0x10)
write_apb(IOREGSEL, 0x10);

// 2. Write configuration via IOWIN
//    Vector=0x20, Deliv=Fixed, DestMode=Phys, Trigger=Edge, Polarity=High, Unmask
write_apb(IOWIN, 0x00000020);  // Vector 0x20, all defaults

// 3. Select IOREDTBL0_HI (offset 0x11)
write_apb(IOREGSEL, 0x11);

// 4. Write destination CPU via IOWIN
write_apb(IOWIN, 0x01000000);  // Destination APIC ID = 1
```

## Key Features

- **Intel 82093AA Compatible**: Matches Intel IOAPIC register interface
- **Indirect Access Method**: IOREGSEL/IOWIN register window
- **24 IRQ Sources**: IRQ0-IRQ23 with individual configuration
- **Programmable Redirection**: Per-IRQ vector, mode, destination, trigger, polarity
- **Edge/Level Triggering**: Configurable per IRQ
- **Active High/Low**: Polarity selection per IRQ
- **Remote IRR**: Level-triggered interrupt tracking
- **Delivery Status**:Interrupt delivery state
- **12-bit Address Space**: Matches RLB standard

## Delivery Modes

The IOAPIC supports multiple delivery modes (bits [10:8] of REDIR_LO):
- **000 - Fixed**: Deliver to destination specified in REDIR_HI
- **001 - Lowest Priority**: Deliver to lowest priority CPU
- **010 - SMI**: System Management Interrupt
- **100 - NMI**: Non-Maskable Interrupt
- **101 - INIT**: Initialization
- **111 - ExtINT**: External Interrupt (8259 compatible)

**Note**: MVP implementation supports Fixed mode only. Other modes are future enhancements.

## Integration

The generated register files are used by:
- `ioapic_config_regs.sv` - Maps hwif to ioapic_core interface with indirect access
- `apb_ioapic.sv` - Top-level APB wrapper

See parent directory README.md for complete integration details.

## Address Mapping Summary

```
APB Address | Register  | Internal Offset | Description
------------|-----------|-----------------|---------------------------
0x000       | IOREGSEL  | N/A             | Register offset selector
0x004       | IOWIN     | N/A             | Data window for selected reg
0x008-0xFFF | Reserved  | N/A             | Future expansion

Via IOREGSEL/IOWIN:
  0x00      | IOAPICID  | Bits[27:24]     | APIC ID
  0x01      | IOAPICVER | Ver + MaxEntry  | Version info
  0x02      | IOAPICARB | Bits[27:24]     | Arbitration ID
  0x10-0x3F | IOREDTBL  | 24 entries × 2  | Redirection table
```
