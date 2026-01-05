# PIC 8259 Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for PIC 8259 (Programmable Interrupt Controller) operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `pic_interrupt_request.json` | IRQ Request | IR pin sets IRR, priority resolved, INT asserts |
| `pic_interrupt_acknowledge.json` | INTA Sequence | Two INTA pulses, IRR->ISR transfer, vector output |
| `pic_eoi.json` | End of Interrupt | Non-specific EOI clears highest ISR bit |
| `pic_cascade.json` | Cascade Mode | Master-slave interrupt routing via CAS lines |
| `pic_priority_rotation.json` | Priority Rotate | Rotate-on-EOI for round-robin scheduling |

## Signal Hierarchy

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### PIC Pins (External)
- `ir[7:0]` - Interrupt request inputs (directly or edge triggered)
- `int` - Interrupt output to CPU
- `inta_n` - Interrupt acknowledge from CPU (active low)
- `cas[2:0]` - Cascade lines (master output, slave input)
- `sp_n/en_n` - Slave program / enable buffer

### PIC Core (Internal)
- **IRR (Interrupt Request Register):** `r_irr[7:0]` - Pending interrupts
- **ISR (In-Service Register):** `r_isr[7:0]` - Currently servicing
- **IMR (Interrupt Mask Register):** `imr[7:0]` - Masked interrupts
- **Priority:** `w_pending`, `w_highest_pri`, `lowest_priority`, `priority_order`
- **INTA:** `inta_cycle`, `vector_out`, `data_out`
- **EOI:** `eoi_cmd`, `specific_eoi`, `highest_isr`
- **Cascade:** `slave_int`, `slave_selected`, `master_ir[2]`

## Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## Scenarios Explained

### 1. Interrupt Request
Shows IR pin assertion triggering IRR bit set. IMR checked for masking. Priority resolver selects highest priority pending interrupt. INT output asserts to CPU.

### 2. Interrupt Acknowledge
Shows two-pulse INTA sequence from CPU:
- 1st INTA: Freezes priority, transfers IRR bit to ISR, clears IRR
- 2nd INTA: PIC outputs vector (base + IR number) on data bus

### 3. End of Interrupt
Shows non-specific EOI (OCW2 = 0x20). PIC finds highest priority bit in ISR and clears it. Allows lower priority pending interrupts to be serviced.

### 4. Cascade Mode
Shows master-slave cascade configuration:
- Slave INT connects to master IR[2] (typical PC configuration)
- During INTA, master outputs CAS[2:0] = slave ID
- Slave with matching ID responds with its vector

### 5. Priority Rotation
Shows automatic priority rotation (OCW2 = 0xA0). After EOI, serviced IR becomes lowest priority. Enables round-robin scheduling among same-priority devices.

## Register Reference

### Initialization Command Words (ICW)
| ICW | A0 | Description |
|-----|----|----|
| ICW1 | 0 | Edge/level, single/cascade, ICW4 needed |
| ICW2 | 1 | Vector base address (upper 5 bits) |
| ICW3 | 1 | Cascade configuration (master/slave) |
| ICW4 | 1 | 8086 mode, auto EOI, buffered, nested |

### Operation Command Words (OCW)
| OCW | A0 | Description |
|-----|----|----|
| OCW1 | 1 | IMR - Interrupt Mask Register |
| OCW2 | 0 | EOI commands, rotation |
| OCW3 | 0 | Read IRR/ISR, special mask mode |

### OCW2 Commands
| Value | Command |
|-------|---------|
| 0x20 | Non-specific EOI |
| 0x60-0x67 | Specific EOI (IR0-IR7) |
| 0xA0 | Rotate on non-specific EOI |
| 0xE0-0xE7 | Rotate on specific EOI |
| 0xC0-0xC7 | Set priority (IR# becomes lowest) |

## References

- **PIC RTL:** `rtl/pic/apb_pic_8259.sv`
- **PIC Testbench:** `dv/tbclasses/pic/pic_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/pic.py`
