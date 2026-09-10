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

# APB UART 16550 — Interrupt Interface

## Overview

Before you write a line of ISR code, read the notes below. This RTL's interrupt path does not behave like the 16550 your driver author probably had in mind — the enables don't enable, the timeout doesn't exist, and the pin is gated by a modem output bit.

> Implementation notes for this RTL:
> - **Each of the four sources is gated by its own IER bit.** A disabled source
>   still sets its status bit; it simply is not an interrupt, does not raise
>   `irq`, and is not reported by IIR.
> - **The `irq` pin is gated by MCR.OUT2** (`irq = pending & MCR.OUT2`). With the
>   reset MCR = 0x00 the pin is masked; software must set OUT2 to route interrupts.
> - **Character timeout is not implemented** (IIR never reads 0x0C). Tracked as
>   RLB-013 in `vault/Tasks/RLB/open.md`.
> - **Reading IIR clears the THR-empty interrupt** when THR empty is the source
>   it reported, as a standard 16550 does.
> - LSR[4:1] clear on a read of LSR, and MSR[3:0] on a read of MSR.

## Ports

### Signal Description

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| irq | 1 | O | Interrupt request (active high, gated by MCR.OUT2) |

## Functional Description

### Interrupt Sources

#### Priority Order (Highest to Lowest)

| Priority | IIR[3:0] | Source | Clear Method |
|----------|----------|--------|--------------|
| 1 | 0110 | Receiver Line Status | Read LSR |
| 2 | 0100 | Received Data Available | Read RBR until DR clears |
| 3 | 0010 | THR Empty | Write THR (fill TX FIFO) |
| 4 | 0000 | Modem Status | Read MSR |

Character Timeout (IIR = 1100 / 0x0C) is not implemented and is omitted.

#### IIR Encoding

| IIR[3:0] | IIR[0] | Meaning |
|----------|--------|---------|
| xxx0 | 0 | Interrupt pending |
| xxx1 | 1 | No interrupt |

### Interrupt Enable Register (IER)

These bits are stored and read back but are **not connected** to the interrupt
logic in this RTL - they do not enable or mask any interrupt.

| Bit | Name | Nominal Source (not enforced) |
|-----|------|-------------------------------|
| 0 | ERBFI | Received data available |
| 1 | ETBEI | THR empty |
| 2 | ELSI | Receiver line status |
| 3 | EDSSI | Modem status |

### Interrupt Identification Register (IIR)

#### Read Format

| Bits | Name | Description |
|------|------|-------------|
| 0 | IPEND | 0=interrupt pending, 1=none |
| 3:1 | IID | Interrupt ID |
| 5:4 | Reserved | |
| 7:6 | FIFOEN | 11 if FIFOs enabled |

### Interrupt Conditions

#### Receiver Line Status (Priority 1)

Triggered by:
- Overrun Error (OE)
- Parity Error (PE)
- Framing Error (FE)
- Break Indicator (BI)

Cleared by reading LSR.

#### Received Data Available (Priority 2)

- FCR.FE=1: triggered when RX FIFO >= trigger level
- FCR.FE=0: triggered when data present (DR=1)
- Cleared by reading RBR until the level falls below the trigger / DR clears

#### Character Timeout - not implemented

`int_timeout` is tied to 0 in this RTL; the timeout interrupt never occurs and
IIR never reads 0x0C.

#### THR Empty (Priority 3)

Triggered when the TX FIFO is empty (this is a level, THRE = TX FIFO empty).

Cleared by writing THR to refill the TX FIFO. Reading IIR does **not** clear it.

#### Modem Status (Priority 4)

Triggered by any MSR delta bit:
- DCTS (Delta CTS)
- DDSR (Delta DSR)
- TERI (Trailing Edge RI)
- DDCD (Delta DCD)

Cleared by reading MSR.

## Timing

### Interrupt Timing

IIR and `irq` are purely COMBINATIONAL from the core status flags: the
cycle a condition's flag sets, IIR reflects it and `irq` asserts (gated by
MCR.OUT2); the cycle the condition clears, both deassert. There are no
pipeline stages in the interrupt path.

```
Event --> flag sets --> IIR + IRQ reflect it (same cycle, combinational)
Clear --> flag clears --> IIR + IRQ deassert (same cycle)
```

## Usage Example

### Software Handling

#### ISR Flow

```c
void uart_isr(void) {
    uint8_t iir = IIR;

    while ((iir & 0x01) == 0) {  // While interrupt pending
        switch (iir & 0x0E) {
            case 0x06:  // Line status
                handle_line_status(LSR);
                break;
            case 0x04:  // RX data available
            case 0x0C:  // Character timeout
                handle_rx_data();
                break;
            case 0x02:  // THR empty
                handle_tx_empty();
                break;
            case 0x00:  // Modem status
                handle_modem_status(MSR);
                break;
        }
        iir = IIR;  // Re-read for next pending
    }
}
```

---

## Navigation

**Next:** [05_system.md](05_system.md) - System Interface
