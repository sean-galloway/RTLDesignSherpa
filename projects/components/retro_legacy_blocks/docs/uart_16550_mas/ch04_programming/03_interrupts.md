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
| 0x06 | 1 | Line status error | Read LSR |
| 0x04 | 2 | RX data available | Read RBR |
| 0x0C | 2 | Character timeout | Read RBR |
| 0x02 | 3 | THR empty | Read IIR or write THR |
| 0x00 | 4 | Modem status | Read MSR |

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
    uint8_t lsr = LSR;  // Read clears errors

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
    uint8_t msr = MSR;  // Read clears delta bits

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

- Triggers after 4 character times of inactivity
- Ensures partial data is delivered
- Critical for variable-length packets

## Disabling/Enabling Interrupts

```c
// Save and disable
uint8_t saved_ier = IER;
IER = 0x00;

// ... critical section ...

// Restore
IER = saved_ier;
```

---

**Next:** [04_examples.md](04_examples.md) - Examples
