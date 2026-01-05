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

# APB UART 16550 - Data Transfer

## Transmitting Data

### Polling Mode

```c
void uart_putchar(uint8_t c) {
    // Wait for THR empty
    while ((LSR & 0x20) == 0);

    // Write data
    THR = c;
}

void uart_puts(const char *s) {
    while (*s) {
        uart_putchar(*s++);
    }
}
```

### Interrupt-Driven TX

```c
volatile uint8_t tx_buffer[256];
volatile uint8_t tx_head = 0;
volatile uint8_t tx_tail = 0;

void uart_send(const uint8_t *data, size_t len) {
    for (size_t i = 0; i < len; i++) {
        // Add to buffer
        tx_buffer[tx_head++] = data[i];
    }

    // Enable TX interrupt
    IER |= 0x02;
}

// In ISR when THRE interrupt:
void uart_tx_isr(void) {
    while ((LSR & 0x20) && (tx_head != tx_tail)) {
        THR = tx_buffer[tx_tail++];
    }

    if (tx_head == tx_tail) {
        IER &= ~0x02;  // Disable TX interrupt
    }
}
```

### Waiting for TX Complete

```c
void uart_flush(void) {
    // Wait for TEMT (both FIFO and shift register empty)
    while ((LSR & 0x40) == 0);
}
```

## Receiving Data

### Polling Mode

```c
int uart_getchar(void) {
    // Check for data available
    if ((LSR & 0x01) == 0) {
        return -1;  // No data
    }

    // Read data
    return RBR;
}

int uart_getchar_blocking(void) {
    // Wait for data
    while ((LSR & 0x01) == 0);

    return RBR;
}
```

### Interrupt-Driven RX

```c
volatile uint8_t rx_buffer[256];
volatile uint8_t rx_head = 0;
volatile uint8_t rx_tail = 0;

// In ISR when RX data available:
void uart_rx_isr(void) {
    while (LSR & 0x01) {
        rx_buffer[rx_head++] = RBR;
    }
}

int uart_read(uint8_t *data, size_t max_len) {
    size_t count = 0;
    while ((rx_head != rx_tail) && (count < max_len)) {
        data[count++] = rx_buffer[rx_tail++];
    }
    return count;
}
```

## Error Handling

### Checking Line Status

```c
uint8_t uart_check_errors(void) {
    uint8_t lsr = LSR;
    uint8_t errors = 0;

    if (lsr & 0x02) errors |= ERR_OVERRUN;
    if (lsr & 0x04) errors |= ERR_PARITY;
    if (lsr & 0x08) errors |= ERR_FRAMING;
    if (lsr & 0x10) errors |= ERR_BREAK;

    return errors;
}
```

### Handling Errors in RX ISR

```c
void uart_rx_error_isr(void) {
    uint8_t lsr = LSR;  // Reading clears errors

    if (lsr & 0x02) {
        // Overrun - data lost
        stats.overrun_count++;
    }
    if (lsr & 0x04) {
        // Parity error
        stats.parity_count++;
    }
    if (lsr & 0x08) {
        // Framing error
        stats.framing_count++;
    }
    if (lsr & 0x10) {
        // Break received
        handle_break_condition();
    }
}
```

## FIFO Management

### FIFO Status

```c
bool uart_tx_fifo_empty(void) {
    return (LSR & 0x20) != 0;  // THRE
}

bool uart_tx_complete(void) {
    return (LSR & 0x40) != 0;  // TEMT
}

bool uart_rx_data_ready(void) {
    return (LSR & 0x01) != 0;  // DR
}

bool uart_rx_fifo_error(void) {
    return (LSR & 0x80) != 0;  // FIFO error
}
```

### FIFO Reset

```c
void uart_reset_fifos(void) {
    // Reset both FIFOs while keeping enabled
    uint8_t fcr = FCR;
    FCR = fcr | 0x06;  // RFR + TFR
}
```

## Bulk Transfer

### Efficient TX (FIFO-aware)

```c
size_t uart_write(const uint8_t *data, size_t len) {
    size_t sent = 0;

    while (sent < len) {
        // Wait for FIFO space
        if (LSR & 0x20) {
            // Fill FIFO (up to 16 bytes)
            size_t chunk = (len - sent < 16) ? (len - sent) : 16;
            for (size_t i = 0; i < chunk; i++) {
                THR = data[sent++];
            }
        }
    }

    return sent;
}
```

### Efficient RX (FIFO-aware)

```c
size_t uart_read_available(uint8_t *data, size_t max_len) {
    size_t count = 0;

    while ((LSR & 0x01) && (count < max_len)) {
        data[count++] = RBR;
    }

    return count;
}
```

---

**Next:** [03_interrupts.md](03_interrupts.md) - Interrupts
