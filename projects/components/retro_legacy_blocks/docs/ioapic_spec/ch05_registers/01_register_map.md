### APB IOAPIC - Complete Register Map

#### Register Access Method

The IOAPIC uses **indirect register access** following Intel 82093AA specification:

1. **Write to IOREGSEL** (APB address 0x00): Select internal register offset
2. **Access IOWIN** (APB address 0x04): Read or write selected register data

#### Direct APB Registers

| APB Address | Register | Type | Reset | Description |
|-------------|----------|------|-------|-------------|
| 0x000 | IOREGSEL | RW | 0x00 | Register offset selector (0x00-0x3F) |
| 0x004 | IOWIN | RW | 0x00000000 | Data window for selected internal register |
| 0x008-0xFFF | Reserved | - | - | Reserved for future expansion |

#### IOREGSEL Register (APB 0x000)

| Bits | Name | Type | Reset | Description |
|------|------|------|-------|-------------|
| [7:0] | regsel | RW | 0x00 | Internal register offset for indirect access |
| [31:8] | Reserved | RO | 0x000000 | Reserved, read as 0 |

**Valid offset values:**
- 0x00: IOAPICID
- 0x01: IOAPICVER
- 0x02: IOAPICARB
- 0x10-0x3F: IOREDTBL entries (even=LO, odd=HI)

#### IOWIN Register (APB 0x004)

| Bits | Name | Type | Reset | Description |
|------|------|------|-------|-------------|
| [31:0] | data | RW | 0x00000000 | Read/Write data for register selected by IOREGSEL |

**Behavior:**
- Reading IOWIN returns data from register selected by current IOREGSEL value
- Writing IOWIN updates register selected by current IOREGSEL value
- IOREGSEL must be written before each IOWIN access
- IOREGSEL value persists until explicitly changed

---

## Internal Registers (Accessed via IOREGSEL/IOWIN)

#### IOAPICID Register (Internal Offset 0x00)

**Access via IOREGSEL/IOWIN:**
```c
*IOREGSEL = 0x00;  // Select IOAPICID
*IOWIN = 0x0F000000;  // Set APIC ID = 0xF
```

| Bits | Name | Type | Reset | Description |
|------|------|------|-------|-------------|
| [23:0] | Reserved | RO | 0x000000 | Reserved, read as 0 |
| [27:24] | APIC ID | RW | 0x0 | 4-bit IOAPIC identifier for multi-IOAPIC systems |
| [31:28] | Reserved | RO | 0x0 | Reserved, read as 0 |

**Purpose:** Identifies this IOAPIC in systems with multiple I/O APICs.

#### IOAPICVER Register (Internal Offset 0x01)

**Access via IOREGSEL/IOWIN:**
```c
*IOREGSEL = 0x01;  // Select IOAPICVER
uint32_t ver = *IOWIN;  // Read version
```

| Bits | Name | Type | Reset | Description |
|------|------|------|-------|-------------|
| [7:0] | Version | RO | 0x11 | IOAPIC version (0x11 for 82093AA compatibility) |
| [15:8] | Reserved | RO | 0x00 | Reserved, read as 0 |
| [23:16] | Max Redir Entry | RO | 0x17 | Maximum redirection entry (0x17 = 23 for 24 IRQs) |
| [31:24] | Reserved | RO | 0x00 | Reserved, read as 0 |

**Purpose:** Reports IOAPIC capabilities to software.

#### IOAPICARB Register (Internal Offset 0x02)

**Access via IOREGSEL/IOWIN:**
```c
*IOREGSEL = 0x02;  // Select IOAPICARB
uint32_t arb = *IOWIN;  // Read arbitration ID
```

| Bits | Name | Type | Reset | Description |
|------|------|------|-------|-------------|
| [23:0] | Reserved | RO | 0x000000 | Reserved, read as 0 |
| [27:24] | Arbitration ID | RO | 0x0 | Bus arbitration priority (mirrors APIC ID) |
| [31:28] | Reserved | RO | 0x0 | Reserved, read as 0 |

**Purpose:** Multi-IOAPIC bus arbitration (read-only, matches APIC ID).

---

## Redirection Table (Internal Offsets 0x10-0x3F)

Each of the 24 IRQ inputs has a 64-bit redirection entry consisting of two 32-bit registers (LO and HI).

**Internal Offset Calculation:**
```c
// For IRQ n (0-23):
uint8_t offset_lo = 0x10 + (n * 2);      // Even offset
uint8_t offset_hi = 0x10 + (n * 2) + 1;  // Odd offset

// Examples:
// IRQ0:  LO=0x10, HI=0x11
// IRQ1:  LO=0x12, HI=0x13
// IRQ23: LO=0x3E, HI=0x3F
```

#### IOREDTBL[n]_LO Register (Lower 32 Bits)

**Access via IOREGSEL/IOWIN:**
```c
*IOREGSEL = 0x10 + (irq_num * 2);  // Select LO register for IRQ n
*IOWIN = config_value;              // Write config
```

| Bits | Name | Type | Reset | Description |
|------|------|------|-------|-------------|
| [7:0] | Vector | RW | 0x00 | Interrupt vector to deliver to CPU (0x00-0xFF) |
| [10:8] | Delivery Mode | RW | 0b000 | 000=Fixed, 001=LowestPri, 010=SMI, 100=NMI, 101=INIT, 111=ExtINT |
| [11] | Dest Mode | RW | 0 | Destination mode: 0=Physical, 1=Logical |
| [12] | Delivery Status | RO | 0 | 0=Idle, 1=Send Pending (read-only) |
| [13] | Polarity | RW | 0 | Interrupt polarity: 0=Active High, 1=Active Low |
| [14] | Remote IRR | RO | 0 | Remote IRR: 0=No IRQ, 1=IRQ accepted (read-only, level mode only) |
| [15] | Trigger Mode | RW | 0 | Trigger mode: 0=Edge, 1=Level |
| [16] | Mask | RW | 1 | Interrupt mask: 0=Not Masked (enabled), 1=Masked (disabled) |
| [31:17] | Reserved | RO | 0x0000 | Reserved, read as 0 |

**Field Descriptions:**

**Vector [7:0]:**
- Interrupt vector number delivered to CPU
- Typically 0x20-0xFF for x86 systems (0x00-0x1F reserved)
- Software chooses unique vector per IRQ or shares vectors

**Delivery Mode [10:8]:**
- **000 (Fixed):** Deliver to CPU specified in Destination field (MVP)
- **001 (Lowest Priority):** Deliver to lowest priority CPU (future)
- **010 (SMI):** System Management Interrupt (future)
- **100 (NMI):** Non-Maskable Interrupt (future)
- **101 (INIT):** Initialization sequence (future)
- **111 (ExtINT):** External Interrupt, 8259-compatible (future)

**Destination Mode [11]:**
- **0 (Physical):** Use Destination field as physical APIC ID (MVP)
- **1 (Logical):** Use Destination field as logical destination (future)

**Delivery Status [12] (Read-Only):**
- **0 (Idle):** No delivery in progress for this IRQ
- **1 (Send Pending):** Interrupt being delivered or waiting for EOI
- Hardware-controlled, indicates interrupt delivery state

**Polarity [13]:**
- **0 (Active High):** IRQ asserted when input is high
- **1 (Active Low):** IRQ asserted when input is low
- Allows direct connection to active-low interrupt sources

**Remote IRR [14] (Read-Only, Level Mode Only):**
- **0:** No interrupt or interrupt serviced
- **1:** Level interrupt accepted by CPU, waiting for EOI
- Only meaningful for level-triggered interrupts
- Prevents re-triggering until EOI received
- Cleared by EOI, set when interrupt delivered

**Trigger Mode [15]:**
- **0 (Edge):** Interrupt on rising edge of active signal
- **1 (Level):** Interrupt on active level, uses Remote IRR, needs EOI

**Mask [16]:**
- **0 (Not Masked):** IRQ enabled, can generate interrupts
- **1 (Masked):** IRQ disabled, no interrupts generated
- Default is masked (1) for safety
- Software must unmask to enable IRQ

#### IOREDTBL[n]_HI Register (Upper 32 Bits)

**Access via IOREGSEL/IOWIN:**
```c
*IOREGSEL = 0x10 + (irq_num * 2) + 1;  // Select HI register for IRQ n
*IOWIN = dest_value;                    // Write destination
```

| Bits | Name | Type | Reset | Description |
|------|------|------|-------|-------------|
| [23:0] | Reserved | RO | 0x000000 | Reserved, read as 0 |
| [31:24] | Destination | RW | 0x00 | Destination: Physical APIC ID or Logical destination |

**Field Descriptions:**

**Destination [31:24]:**
- **Physical Mode (Dest Mode=0):** 8-bit physical APIC ID of target CPU
- **Logical Mode (Dest Mode=1):** Logical destination for multi-cast (future)
- For single-CPU systems, typically set to CPU's APIC ID (often 0x00 or 0x01)

---

## Complete Register Address Map

### Internal Register Offsets (via IOREGSEL)

| Offset | Register | Type | Description |
|--------|----------|------|-------------|
| **System Registers** ||||
| 0x00 | IOAPICID | RW | I/O APIC identification |
| 0x01 | IOAPICVER | RO | Version and max entry |
| 0x02 | IOAPICARB | RO | Arbitration priority |
| 0x03-0x0F | Reserved | - | Reserved |
| **Redirection Table** ||||
| 0x10 | IOREDTBL[0]_LO | RW | IRQ0 redirection entry low |
| 0x11 | IOREDTBL[0]_HI | RW | IRQ0 redirection entry high |
| 0x12 | IOREDTBL[1]_LO | RW | IRQ1 redirection entry low |
| 0x13 | IOREDTBL[1]_HI | RW | IRQ1 redirection entry high |
| 0x14 | IOREDTBL[2]_LO | RW | IRQ2 redirection entry low |
| 0x15 | IOREDTBL[2]_HI | RW | IRQ2 redirection entry high |
| ... | ... | ... | (continues for all 24 IRQs) |
| 0x3E | IOREDTBL[23]_LO | RW | IRQ23 redirection entry low |
| 0x3F | IOREDTBL[23]_HI | RW | IRQ23 redirection entry high |

### Typical IRQ Assignments (PC-Compatible Systems)

| IRQ # | Offset (LO/HI) | Traditional Use | Typical Vector |
|-------|----------------|-----------------|----------------|
| IRQ0 | 0x10/0x11 | System Timer | 0x20 |
| IRQ1 | 0x12/0x13 | Keyboard | 0x21 |
| IRQ2 | 0x14/0x15 | Cascade (PIC) | - |
| IRQ3 | 0x16/0x17 | COM2 | 0x23 |
| IRQ4 | 0x18/0x19 | COM1 | 0x24 |
| IRQ5 | 0x1A/0x1B | LPT2 / Sound | 0x25 |
| IRQ6 | 0x1C/0x1D | Floppy | 0x26 |
| IRQ7 | 0x1E/0x1F | LPT1 | 0x27 |
| IRQ8 | 0x20/0x21 | RTC Alarm | 0x28 |
| IRQ9 | 0x22/0x23 | ACPI / SCSI | 0x29 |
| IRQ10 | 0x24/0x25 | Available | 0x2A |
| IRQ11 | 0x26/0x27 | Available | 0x2B |
| IRQ12 | 0x28/0x29 | PS/2 Mouse | 0x2C |
| IRQ13 | 0x2A/0x2B | FPU | 0x2D |
| IRQ14 | 0x2C/0x2D | Primary IDE | 0x2E |
| IRQ15 | 0x2E/0x2F | Secondary IDE | 0x2F |
| IRQ16-23 | 0x30-0x3F | PCI Interrupts, Additional devices | 0x30-0x37 |

---

## Programming Examples

### Example 1: Configure IRQ14 (IDE) - Edge-Triggered

```c
// Configure IRQ14 for primary IDE controller
// Vector 0x2E, Edge-triggered, Active High, Fixed delivery, Unmask

// Step 1: Select IOREDTBL[14]_LO (offset 0x2C)
*IOREGSEL = 0x2C;

// Step 2: Write LO configuration
//   Bits[7:0]   = 0x2E       (Vector)
//   Bits[10:8]  = 0b000      (Fixed delivery)
//   Bit[11]     = 0          (Physical dest)
//   Bit[13]     = 0          (Active high)
//   Bit[15]     = 0          (Edge trigger)
//   Bit[16]     = 0          (Not masked)
*IOWIN = 0x0000002E;

// Step 3: Select IOREDTBL[14]_HI (offset 0x2D)
*IOREGSEL = 0x2D;

// Step 4: Write destination (CPU 0)
*IOWIN = 0x00000000;  // Destination APIC ID = 0
```

### Example 2: Configure IRQ9 (ACPI) - Level-Triggered

```c
// Configure IRQ9 for ACPI SCI (System Control Interrupt)
// Vector 0x29, Level-triggered, Active Low, Fixed delivery, Unmask

// Step 1: Select IOREDTBL[9]_LO (offset 0x22)
*IOREGSEL = 0x22;

// Step 2: Write LO configuration
//   Bits[7:0]   = 0x29       (Vector)
//   Bits[10:8]  = 0b000      (Fixed delivery)
//   Bit[11]     = 0          (Physical dest)
//   Bit[13]     = 1          (Active LOW)
//   Bit[15]     = 1          (LEVEL trigger)
//   Bit[16]     = 0          (Not masked)
*IOWIN = 0x0000A029;  // Bits 15,13 set for level, active-low

// Step 3: Select IOREDTBL[9]_HI (offset 0x23)
*IOREGSEL = 0x23;

// Step 4: Write destination (CPU 0)
*IOWIN = 0x00000000;
```

### Example 3: Mask/Unmask an IRQ

```c
// Mask IRQ5 (disable)
*IOREGSEL = 0x1A;           // Select IOREDTBL[5]_LO
uint32_t config = *IOWIN;    // Read current config
config |= (1 << 16);         // Set mask bit
*IOWIN = config;             // Write back

// Unmask IRQ5 (enable)
*IOREGSEL = 0x1A;           // Select IOREDTBL[5]_LO
config = *IOWIN;             // Read current config
config &= ~(1 << 16);        // Clear mask bit
*IOWIN = config;             // Write back
```

### Example 4: Check Delivery Status and Remote IRR

```c
// Check if IRQ12 (PS/2 mouse) is being delivered
*IOREGSEL = 0x28;           // Select IOREDTBL[12]_LO
uint32_t status = *IOWIN;
bool is_pending = (status & (1 << 12)) != 0;      // Delivery Status
bool remote_irr = (status & (1 << 14)) != 0;      // Remote IRR

if (is_pending) {
    printf("IRQ12 delivery in progress\n");
}

if (remote_irr) {
    printf("IRQ12 waiting for EOI (level-triggered)\n");
}
```

### Example 5: Read IOAPIC Version and Capabilities

```c
// Discover IOAPIC capabilities
*IOREGSEL = 0x01;           // Select IOAPICVER
uint32_t ver_reg = *IOWIN;

uint8_t version = ver_reg & 0xFF;
uint8_t max_entry = (ver_reg >> 16) & 0xFF;
uint8_t num_irqs = max_entry + 1;

printf("IOAPIC Version: 0x%02X\n", version);
printf("Number of IRQs: %d\n", num_irqs);
```

---

## Register Field Summary

### Control Fields (Software Writable)

| Field | Register | Purpose |
|-------|----------|---------|
| Vector[7:0] | REDIR_LO | Interrupt vector number |
| Delivery Mode[10:8] | REDIR_LO | How to deliver (Fixed, LowestPri, etc.) |
| Dest Mode[11] | REDIR_LO | Physical vs Logical addressing |
| Polarity[13] | REDIR_LO | Active High vs Active Low |
| Trigger Mode[15] | REDIR_LO | Edge vs Level |
| Mask[16] | REDIR_LO | Enable/Disable this IRQ |
| Destination[31:24] | REDIR_HI | Target CPU APIC ID |
| APIC ID[27:24] | IOAPICID | This IOAPIC's identifier |

### Status Fields (Read-Only)

| Field | Register | Purpose |
|-------|----------|---------|
| Delivery Status[12] | REDIR_LO | Interrupt delivery in progress |
| Remote IRR[14] | REDIR_LO | Level interrupt waiting for EOI |
| Version[7:0] | IOAPICVER | IOAPIC version (0x11) |
| Max Redir Entry[23:16] | IOAPICVER | Number of IRQs - 1 (0x17) |
| Arbitration ID[27:24] | IOAPICARB | Bus arbitration priority |

---

## Reset Values

**After Reset:**
- IOREGSEL = 0x00
- IOAPICID = 0x00000000 (ID = 0)
- All IOREDTBL entries:
  - Vector = 0x00
  - Delivery Mode = 0b000 (Fixed)
  - Dest Mode = 0 (Physical)
  - Delivery Status = 0 (Idle)
  - Polarity = 0 (Active High)
  - Remote IRR = 0
  - Trigger Mode = 0 (Edge)
  - **Mask = 1 (MASKED)** ← Important! All IRQs disabled by default
  - Destination = 0x00

**Software must unmask IRQs to enable interrupts.**

---

**See Also:**
- [Chapter 4: Programming Model](../ch04_programming/01_initialization.md) - Detailed init sequences
- [Indirect Access Guide](02_indirect_access.md) - IOREGSEL/IOWIN usage details
- [Redirection Table Guide](03_redirection_table.md) - Field descriptions and examples
