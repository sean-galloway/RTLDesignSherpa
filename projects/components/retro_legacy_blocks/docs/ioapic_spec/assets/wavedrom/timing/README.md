# IOAPIC Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for IOAPIC (I/O Advanced Programmable Interrupt Controller) operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `ioapic_interrupt_delivery.json` | Int Delivery | Edge-triggered IRQ to LAPIC message |
| `ioapic_rte_write.json` | RTE Write | Indirect register access to RTE |
| `ioapic_level_triggered.json` | Level Trigger | Level mode with Remote IRR and EOI |
| `ioapic_mask_interrupt.json` | Int Masking | Masked interrupt latches, unmask delivers |

## Signal Hierarchy

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### IRQ Inputs (External)
- `irq_in[23:0]` - Interrupt request inputs (directly or inverted)

### Message Interface (External)
- `msg_valid` - Message valid to system bus
- `msg_dest` - Destination APIC ID
- `msg_vector` - Interrupt vector
- `msg_type` - Delivery mode (Fixed, LowPri, SMI, NMI, etc.)

### EOI Interface (External)
- `eoi_write` - EOI broadcast received
- `eoi_vector` - Vector being acknowledged

### IOAPIC Core (Internal)
- **Index Register:** `r_ioregsel`
- **Redirection Table:** `rte[n].vector`, `rte[n].dest`, `rte[n].mask`, `rte[n].trigger`
- **IRQ State:** `irr[n]`, `remote_irr[n]`, `delivery_pending`

## Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## Scenarios Explained

### 1. Interrupt Delivery
Shows edge-triggered interrupt flow:
1. IRQ pin asserts (edge detected)
2. IRR bit set for input
3. RTE consulted for vector, destination, delivery mode
4. Interrupt message sent on system bus
5. Destination LAPIC receives and asserts CPU interrupt

### 2. RTE Write (Indirect Access)
Shows two-step indirect register access:
1. Write index to IOREGSEL (selects RTE low or high word)
2. Write data to IOWIN (updates selected RTE)
3. Index 0x10-0x3F map to RTE[0-23] low/high words

### 3. Level-Triggered Interrupt
Shows level mode with EOI requirement:
1. IRQ asserts, IRR set
2. Interrupt delivered, Remote IRR set
3. Remote IRR blocks re-delivery while set
4. CPU sends EOI broadcast when handler completes
5. IOAPIC clears Remote IRR
6. If IRQ still asserted, re-delivers

### 4. Interrupt Masking
Shows masked interrupt behavior:
1. IRQ arrives while masked
2. IRR latched but delivery blocked
3. Software unmasks RTE
4. IOAPIC checks pending IRR
5. Delivers latched interrupt

## Register Reference

### IOAPIC Registers (Indirect Access)
| Index | Register | Description |
|-------|----------|-------------|
| 0x00 | IOAPICID | APIC ID |
| 0x01 | IOAPICVER | Version and max RTE |
| 0x02 | IOAPICARB | Arbitration ID |
| 0x10-0x3F | IOREDTBL | Redirection Table (64-bit entries) |

### Direct Access Registers
| Offset | Register | Description |
|--------|----------|-------------|
| 0x00 | IOREGSEL | Index register |
| 0x10 | IOWIN | Data window |
| 0x40 | IOEOI | EOI register (some implementations) |

### Redirection Table Entry (64-bit)
| Bits | Field | Description |
|------|-------|-------------|
| 7:0 | Vector | Interrupt vector (0x10-0xFE) |
| 10:8 | Delivery Mode | Fixed, LowPri, SMI, NMI, INIT, ExtINT |
| 11 | Dest Mode | Physical (0) or Logical (1) |
| 12 | Delivery Status | Idle (0) or Send Pending (1) |
| 13 | Pin Polarity | Active High (0) or Active Low (1) |
| 14 | Remote IRR | Level-triggered: set on delivery, cleared on EOI |
| 15 | Trigger Mode | Edge (0) or Level (1) |
| 16 | Mask | Masked (1) or Not Masked (0) |
| 55:56 | Destination | APIC ID (physical) or set (logical) |

### Delivery Modes
| Mode | Value | Description |
|------|-------|-------------|
| Fixed | 000 | Deliver to listed processors |
| Lowest | 001 | Deliver to lowest priority processor |
| SMI | 010 | System Management Interrupt |
| NMI | 100 | Non-Maskable Interrupt |
| INIT | 101 | INIT signal |
| ExtINT | 111 | External interrupt (8259 compatible) |

## References

- **IOAPIC RTL:** `rtl/ioapic/apb_ioapic.sv`
- **IOAPIC Testbench:** `dv/tbclasses/ioapic/ioapic_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/ioapic.py`
- **Intel IOAPIC Spec:** 82093AA I/O APIC Datasheet
