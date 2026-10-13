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

# APB UART 16550 — Interrupt Handling

## Overview

Interrupt handling follows the 16550 datasheet, with one gap. The note below is the contract; everything else on this page follows from it.

> Implementation note: each of the four sources is gated by its own IER bit,
> and `irq` is additionally gated by MCR.OUT2 (set OUT2 = 1 to route the pin).
> LSR[4:1] clear on a read of LSR and MSR[3:0] on a read of MSR; reading IIR
> clears the THR-empty interrupt when that is the source it reported. The
> character timeout shares the received-data slot, reads IIR = 0x0C and is
> gated by IER[0].

## Functional Description

### Interrupt Identification Register (IIR)

#### IIR Values

| Value | Priority | Interrupt Source | Clear Method |
|-------|----------|------------------|--------------|
| 0x01 | - | No interrupt | - |
| 0x06 | 1 | Line status error | Read LSR to clear the error bits |
| 0x04 | 2 | RX data available | Read RBR until DR clears |
| 0x02 | 3 | THR empty | Write THR (fills TX FIFO) |
| 0x00 | 4 | Modem status | Read MSR to clear the delta bits |

Note: Character timeout (IIR = 0x0C) fires after four character times of inactivity with a non-empty RX FIFO. Reading IIR has no side effect (it does not clear the THR-empty condition).

## Usage Example

### Interrupt Enable Register (IER)

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

### Complete ISR Example

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

### Individual Interrupt Handlers

#### Line Status Handler

```c
void uart_handle_line_status(void) {
    uint8_t lsr = LSR;  // Read status; this read also clears the error bits

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

    // Nothing to write back: LSR[4:1] were cleared by the read above.
    // That is also why this handler must work from `lsr`, the value the
    // read returned, and must not read LSR again.
}
```

#### RX Data Handler

```c
void uart_handle_rx_data(void) {
    // Read all available data from FIFO
    while (LSR & 0x01) {
        uint8_t data = RBR & 0xFF;  // received byte is at [7:0]
        rx_buffer[rx_head++] = data;

        if (rx_head >= RX_BUFFER_SIZE) {
            rx_head = 0;
        }
    }

    // Signal waiting thread/task
    signal_rx_available();
}
```

#### Character Timeout Handler

```c
// Called when IIR reads 0x0C: four character times with data sitting in
// the RX FIFO below the trigger level.
void uart_handle_timeout(void) {
    // Same as RX data - flush remaining FIFO data
    uart_handle_rx_data();

    // May want to signal "end of packet" condition
    signal_rx_timeout();
}
```

#### TX Empty Handler

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

#### Modem Status Handler

```c
void uart_handle_modem_status(void) {
    uint8_t msr = MSR;  // Read status; this read also clears the delta bits

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

    // Nothing to write back: MSR[3:0] were cleared by the read above,
    // which is why this handler works from `msr` and does not re-read.
}
```

### Disabling/Enabling Interrupts

`IER = 0x00` disables all four sources. MCR.OUT2 gates the pin as well, so
clearing it masks the pin whatever IER says:

```c
// Mask the irq pin via the OUT2 gate
uint8_t saved_mcr = MCR;
MCR = saved_mcr & ~0x08;   // OUT2 = 0 -> irq pin held deasserted

// ... critical section ...

// Restore
MCR = saved_mcr;
```

## Design Notes

### Interrupt Latency Considerations

#### Trigger Level Selection

| Trigger | Bytes in FIFO | Latency Budget | Best For |
|---------|---------------|----------------|----------|
| 1 | 1 | 1 char time | Low latency |
| 4 | 4 | 4 char times | Balanced |
| 8 | 8 | 8 char times | Higher rates |
| 14 | 14 | 2 char times* | Maximum efficiency |

*Only 2 characters before overflow at 16-byte FIFO

#### Character Timeout

- Implemented: four character times with a non-empty RX FIFO and no activity, IIR reads 0x0C.
- For variable-length packets, poll LSR.DR and apply a software inactivity timeout instead.

---

## Navigation

**Next:** [04_examples.md](04_examples.md) - Examples
