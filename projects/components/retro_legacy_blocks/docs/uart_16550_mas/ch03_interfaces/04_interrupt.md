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

# APB UART 16550 - Interrupt Interface

## Signal Description

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| irq | 1 | O | Interrupt request (active high) |

## Interrupt Sources

### Priority Order (Highest to Lowest)

| Priority | IIR[3:0] | Source | Clear Method |
|----------|----------|--------|--------------|
| 1 | 0110 | Receiver Line Status | Read LSR |
| 2 | 0100 | Received Data Available | Read RBR |
| 2 | 1100 | Character Timeout | Read RBR |
| 3 | 0010 | THR Empty | Write THR or read IIR |
| 4 | 0000 | Modem Status | Read MSR |

### IIR Encoding

| IIR[3:0] | IIR[0] | Meaning |
|----------|--------|---------|
| xxx0 | 0 | Interrupt pending |
| xxx1 | 1 | No interrupt |

## Interrupt Enable Register (IER)

| Bit | Name | Interrupt Source |
|-----|------|------------------|
| 0 | ERBFI | Received data available / timeout |
| 1 | ETBEI | THR empty |
| 2 | ELSI | Receiver line status |
| 3 | EDSSI | Modem status |

## Interrupt Identification Register (IIR)

### Read Format

| Bits | Name | Description |
|------|------|-------------|
| 0 | IPEND | 0=interrupt pending, 1=none |
| 3:1 | IID | Interrupt ID |
| 5:4 | Reserved | |
| 7:6 | FIFOEN | 11 if FIFOs enabled |

## Interrupt Conditions

### Receiver Line Status (Priority 1)

Triggered by:
- Overrun Error (OE)
- Parity Error (PE)
- Framing Error (FE)
- Break Indicator (BI)

Cleared by reading LSR.

### Received Data Available (Priority 2)

**FIFO Mode (FCR.FE=1):**
- Triggered when RX FIFO >= trigger level
- Cleared when FIFO below trigger level

**Non-FIFO Mode:**
- Triggered when data in RBR
- Cleared by reading RBR

### Character Timeout (Priority 2)

FIFO mode only:
- Triggered when no new data for 4 character times
- And RX FIFO not empty
- Cleared by reading RBR

### THR Empty (Priority 3)

Triggered when:
- THR (or TX FIFO) becomes empty
- After data transmitted

Cleared by:
- Writing to THR
- Reading IIR (if THRE was source)

### Modem Status (Priority 4)

Triggered by:
- DCTS (Delta CTS)
- DDSR (Delta DSR)
- TERI (Trailing Edge RI)
- DDCD (Delta DCD)

Cleared by reading MSR.

## Interrupt Timing

### Assertion

```
Event --> Condition Met --> IIR Updated --> IRQ Asserted
              |                  |              |
              +--- 1 clock ------+-- 1 clock ---+
```

### Clearing

```
Clear Action --> Condition Cleared --> IIR Updated --> IRQ Deasserted
                        |                    |               |
                        +--- 1 clock --------+-- 1 clock ----+
```

## Software Handling

### ISR Flow

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

**Next:** [05_system.md](05_system.md) - System Interface
