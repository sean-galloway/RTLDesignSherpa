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

# APB UART 16550 - Interrupt Handling

> Implementation note: In this RTL the IER enables are **unimplemented** -
> writing IER is stored/read back but does not mask interrupts. Pending sources
> drive the `irq` pin regardless of IER, and `irq` is gated by MCR.OUT2 (set
> OUT2 = 1 to enable the pin). The character-timeout interrupt is not
> implemented. LSR/MSR sticky bits are W1C, not clear-on-read.

## Interrupt Enable Register (IER)

```c
// Enable specific interrupts
#define IER_RDA     0x01    // Received Data Available
#define IER_THRE    0x02    // THR Empty
#define IER_RLS     0x04    // Receiver Line Status
#define IER_MS      0x08    // Modem Status

void uart_enable_rx_interrupt(void) {
    IER |= IER_RDA;
}

void uart_enable_tx_interrupt(void) {
    IER |= IER_THRE;
}

void uart_disable_tx_interrupt(void) {
    IER &= ~IER_THRE;
}
```

## Interrupt Identification Register (IIR)

### IIR Values

| Value | Priority | Interrupt Source | Clear Method |
|-------|----------|------------------|--------------|
| 0x01 | - | No interrupt | - |
| 0x06 | 1 | Line status error | Clear LSR error bits (W1C) |
| 0x04 | 2 | RX data available | Read RBR until DR clears |
| 0x02 | 3 | THR empty | Write THR (fills TX FIFO) |
| 0x00 | 4 | Modem status | Clear MSR delta bits (W1C) |

Note: Character timeout (IIR = 0x0C) is **not implemented** and never occurs. Reading IIR has no side effect (it does not clear the THR-empty condition).

## Complete ISR Example

```c
void uart_isr(void) {
    uint8_t iir;

    // Loop while interrupts pending
    while (((iir = IIR) & 0x01) == 0) {
        switch (iir & 0x0E) {
            case 0x06:  // Receiver Line Status (highest priority)
                uart_handle_line_status();
                break;

            case 0x04:  // Received Data Available
                uart_handle_rx_data();
                break;

            case 0x0C:  // Character Timeout
                uart_handle_timeout();
                break;

            case 0x02:  // THR Empty
                uart_handle_tx_empty();
                break;

            case 0x00:  // Modem Status (lowest priority)
                uart_handle_modem_status();
                break;
        }
    }
}
```

## Individual Interrupt Handlers

### Line Status Handler

```c
void uart_handle_line_status(void) {
    uint8_t lsr = LSR;  // Read status; then W1C the error bits below

    if (lsr & 0x02) {
        // Overrun Error - FIFO overflow
        stats.overrun++;
    }
    if (lsr & 0x04) {
        // Parity Error
        stats.parity_err++;
    }
    if (lsr & 0x08) {
        // Framing Error
        stats.framing_err++;
    }
    if (lsr & 0x10) {
        // Break Indicator
        handle_break();
    }

    // W1C: write back the bits just read to clear them (LSR error bits [4:1]).
    // (Known RTL issue: the core currently never asserts the clear strobes,
    //  so these bits persist until reset.)
    LSR = lsr & 0x1E;
}
```

### RX Data Handler

```c
void uart_handle_rx_data(void) {
    // Read all available data from FIFO
    while (LSR & 0x01) {
        uint8_t data = RBR;
        rx_buffer[rx_head++] = data;

        if (rx_head >= RX_BUFFER_SIZE) {
            rx_head = 0;
        }
    }

    // Signal waiting thread/task
    signal_rx_available();
}
```

### Character Timeout Handler

```c
// NOTE: Character timeout is NOT implemented in this RTL; this handler is
// never invoked (IIR never reads 0x0C). Retained for reference only.
void uart_handle_timeout(void) {
    // Same as RX data - flush remaining FIFO data
    uart_handle_rx_data();

    // May want to signal "end of packet" condition
    signal_rx_timeout();
}
```

### TX Empty Handler

```c
void uart_handle_tx_empty(void) {
    // Fill TX FIFO from buffer
    while ((LSR & 0x20) && (tx_tail != tx_head)) {
        THR = tx_buffer[tx_tail++];

        if (tx_tail >= TX_BUFFER_SIZE) {
            tx_tail = 0;
        }
    }

    // If buffer empty, disable TX interrupt
    if (tx_tail == tx_head) {
        IER &= ~IER_THRE;
        signal_tx_complete();
    }
}
```

### Modem Status Handler

```c
void uart_handle_modem_status(void) {
    uint8_t msr = MSR;  // Read status; delta bits are W1C (see note below)

    if (msr & 0x01) {   // Delta CTS
        // CTS changed - update flow control
    }
    if (msr & 0x02) {   // Delta DSR
        // DSR changed - device status
    }
    if (msr & 0x04) {   // Trailing Edge RI
        // Ring detected
    }
    if (msr & 0x08) {   // Delta DCD
        // Carrier changed - connection status
    }

    // W1C: write back the delta bits to clear them (MSR[3:0]).
    // (Known RTL issue: clear strobes are not asserted, so bits persist.)
    MSR = msr & 0x0F;
}
```

## Interrupt Latency Considerations

### Trigger Level Selection

| Trigger | Bytes in FIFO | Latency Budget | Best For |
|---------|---------------|----------------|----------|
| 1 | 1 | 1 char time | Low latency |
| 4 | 4 | 4 char times | Balanced |
| 8 | 8 | 8 char times | Higher rates |
| 14 | 14 | 2 char times* | Maximum efficiency |

*Only 2 characters before overflow at 16-byte FIFO

### Character Timeout

- **Not implemented in this RTL** (`int_timeout` is tied to 0). IIR never reads 0x0C.
- For variable-length packets, poll LSR.DR and apply a software inactivity timeout instead.

## Disabling/Enabling Interrupts

IER masking is unimplemented, so `IER = 0x00` does **not** actually disable
interrupts in this RTL. To mask the irq pin, clear MCR.OUT2 (the pin gate):

```c
// Mask the irq pin via the OUT2 gate
uint8_t saved_mcr = MCR;
MCR = saved_mcr & ~0x08;   // OUT2 = 0 -> irq pin held deasserted

// ... critical section ...

// Restore
MCR = saved_mcr;
```

---

**Next:** [04_examples.md](04_examples.md) - Examples
