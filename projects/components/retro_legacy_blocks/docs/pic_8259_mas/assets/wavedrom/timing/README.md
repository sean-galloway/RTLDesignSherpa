# pic_8259 -- Timing Diagrams

This directory contains WaveDrom timing diagrams for PIC 8259 (Programmable Interrupt Controller) operational scenarios.

## Overview

| File | Scenario | Description |
|------|----------|-------------|
| `pic_interrupt_request.json` | IRQ Request | IR pin sets IRR, priority resolved, INT asserts |
| `pic_interrupt_acknowledge.json` | Acknowledge by read | APB read of PIC_INTA: vector returned, IRR->ISR transfer |
| `pic_eoi.json` | End of Interrupt | Non-specific EOI clears highest ISR bit |
| `pic_cascade.json` | Cascade Mode | Master-slave interrupt routing via CAS lines |
| `pic_priority_rotation.json` | Priority Rotate | Rotate-on-EOI for round-robin scheduling |

## Ports

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### PIC Pins (External)
- `irq_in[7:0]` - Interrupt request inputs (edge or level triggered; may be
  asynchronous, synchronized through `SYNC_STAGES` flops on entry)
- `int_out` - Interrupt output to CPU

> Note: there is no INTA pin. The acknowledge is an APB read of PIC_INTA
> (0x2C), which is what the acknowledge diagram shows. The cascade diagram
> still depicts classic-8259A `cas[2:0]` and `sp_n/en_n` signals that this
> RTL does **not** have - cascade is storage only. See the Chapter 5 register
> map design notes.

## Functional Description

### PIC Core (Internal)
- **IRR (Interrupt Request Register):** `r_irr[7:0]` - Pending interrupts
- **ISR (In-Service Register):** `r_isr[7:0]` - Currently servicing
- **IMR (Interrupt Mask Register):** `cfg_imr[7:0]` - the register-block
  field, read directly (no core copy)
- **Priority:** `r_priority_base` (lowest level), `w_ack_irq`/`w_ack_valid`
  (eligible request: unmasked and outranking every in-service level),
  `w_top_isr_irq` (level a non-specific EOI retires)
- **Acknowledge:** `inta_ack` strobe from a PIC_INTA read; `inta_vector`,
  `inta_valid` are the pre-acknowledge readback

### Register Reference

This block uses a fully-decoded 32-bit APB register file, not the legacy A0
two-port model. Offsets below are the actual RTL decode; see
[Chapter 5: Register Map](../../../ch05_registers/01_register_map.md) for full
field definitions.

#### Initialization Command Words (ICW)
| ICW | Offset | Description |
|-----|--------|-------------|
| ICW1 | 0x04 | Edge/level, single/cascade, ICW4 needed |
| ICW2 | 0x08 | Vector base address |
| ICW3 | 0x0C | Cascade configuration (master/slave; storage only) |
| ICW4 | 0x10 | 8086 mode, auto EOI, buffered, nested |

#### Operation Command Words (OCW)
| OCW | Offset | Description |
|-----|--------|-------------|
| OCW1 | 0x14 | IMR - Interrupt Mask Register |
| OCW2 | 0x18 | EOI commands, rotation |
| OCW3 | 0x1C | Special mask mode (read-select and poll are storage only) |

Global control (PIC_CONFIG) is at 0x00 and gates all operation via `pic_enable`;
IRR/ISR/STATUS are dedicated read-only registers at 0x20/0x24/0x28, and
PIC_INTA at 0x2C is the read-to-acknowledge register. Nothing else in the 4 KB
window decodes (PSLVERR).

#### OCW2 Commands
| Value | Command |
|-------|---------|
| 0x00 | Rotate on auto EOI (clear) |
| 0x20 | Non-specific EOI |
| 0x60-0x67 | Specific EOI (IR0-IR7) |
| 0x80 | Rotate on auto EOI (set) -- one rotation per acknowledge in AEOI mode |
| 0xA0 | Rotate on non-specific EOI |
| 0xE0-0xE7 | Rotate on specific EOI |
| 0xC0-0xC7 | Set priority (IR# becomes lowest) |

## Waveforms

### 1. Interrupt Request
Shows IR pin assertion triggering IRR bit set. IMR checked for masking. Priority resolver selects highest priority pending interrupt. INT output asserts to CPU.

### 2. Interrupt Acknowledge
Shows the acknowledge as an APB read of PIC_INTA (0x2C), which replaces the
two INTA pulses:
- Read data: vector (base + IR number) in [7:0], valid in bit 8 - the
  pre-acknowledge state
- End of the access cycle: IRR bit transfers to ISR (edge mode clears IRR;
  level mode leaves it following the pin); INT drops unless a higher-priority
  request is waiting

### 3. End of Interrupt
Shows non-specific EOI (OCW2 = 0x20). PIC finds highest priority bit in ISR and clears it (a no-op if none is set). Allows lower priority pending interrupts to be serviced.

### 4. Cascade Mode
Classic-8259A context only - this block has no cascade. Shows master-slave cascade configuration:
- Slave INT connects to master IR[2] (typical PC configuration)
- During INTA, master outputs CAS[2:0] = slave ID
- Slave with matching ID responds with its vector

### 5. Priority Rotation
Shows automatic priority rotation (OCW2 = 0xA0). After EOI, serviced IR becomes lowest priority. Enables round-robin scheduling among same-priority devices.

## Usage Example

Render every JSON file in this directory to SVG with `wavedrom-cli`:

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## References

- **PIC RTL:** `rtl/pic_8259/apb4_pic_8259.sv`
- **PIC Testbench:** `dv/tbclasses/pic_8259/pic_8259_tb.py`
- **Constraint Class:** none yet for the PIC (see `bin/TBClasses/wavedrom_user/hpet.py` and `apb.py` for examples)
