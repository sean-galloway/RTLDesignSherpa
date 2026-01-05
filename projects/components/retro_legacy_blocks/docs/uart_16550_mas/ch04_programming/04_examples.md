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

# APB UART 16550 - Programming Examples

## Debug Console

### Simple Polling Implementation

```c
#define UART_BASE   0xFEC08000

#define RBR  (*(volatile uint8_t *)(UART_BASE + 0x00))
#define THR  (*(volatile uint8_t *)(UART_BASE + 0x00))
#define IER  (*(volatile uint8_t *)(UART_BASE + 0x04))
#define IIR  (*(volatile uint8_t *)(UART_BASE + 0x08))
#define FCR  (*(volatile uint8_t *)(UART_BASE + 0x08))
#define LCR  (*(volatile uint8_t *)(UART_BASE + 0x0C))
#define MCR  (*(volatile uint8_t *)(UART_BASE + 0x10))
#define LSR  (*(volatile uint8_t *)(UART_BASE + 0x14))
#define MSR  (*(volatile uint8_t *)(UART_BASE + 0x18))
#define SCR  (*(volatile uint8_t *)(UART_BASE + 0x1C))
#define DLL  (*(volatile uint8_t *)(UART_BASE + 0x00))
#define DLM  (*(volatile uint8_t *)(UART_BASE + 0x04))

void debug_uart_init(void) {
    // 115200 baud, 8N1
    LCR = 0x80;           // DLAB = 1
    DLL = 26;             // 48MHz / (16 * 115200)
    DLM = 0;
    LCR = 0x03;           // 8N1, DLAB = 0
    FCR = 0x07;           // Enable FIFOs, reset
    IER = 0x00;           // Polling mode
}

void debug_putchar(char c) {
    while ((LSR & 0x20) == 0);
    THR = c;
}

void debug_puts(const char *s) {
    while (*s) {
        if (*s == '\n')
            debug_putchar('\r');
        debug_putchar(*s++);
    }
}

int debug_getchar(void) {
    if (LSR & 0x01)
        return RBR;
    return -1;
}
```

## Ring Buffer Implementation

```c
#define RX_BUF_SIZE 256
#define TX_BUF_SIZE 256

typedef struct {
    volatile uint8_t buffer[RX_BUF_SIZE];
    volatile uint16_t head;
    volatile uint16_t tail;
} ring_buffer_t;

static ring_buffer_t rx_buf;
static ring_buffer_t tx_buf;

void uart_isr(void) {
    uint8_t iir;

    while (((iir = IIR) & 0x01) == 0) {
        switch (iir & 0x0E) {
            case 0x04:  // RX data
            case 0x0C:  // Timeout
                while (LSR & 0x01) {
                    uint16_t next = (rx_buf.head + 1) % RX_BUF_SIZE;
                    if (next != rx_buf.tail) {
                        rx_buf.buffer[rx_buf.head] = RBR;
                        rx_buf.head = next;
                    } else {
                        (void)RBR;  // Discard if full
                    }
                }
                break;

            case 0x02:  // TX empty
                while ((LSR & 0x20) && (tx_buf.tail != tx_buf.head)) {
                    THR = tx_buf.buffer[tx_buf.tail];
                    tx_buf.tail = (tx_buf.tail + 1) % TX_BUF_SIZE;
                }
                if (tx_buf.tail == tx_buf.head) {
                    IER &= ~0x02;  // Disable TX int
                }
                break;
        }
    }
}

size_t uart_write(const uint8_t *data, size_t len) {
    size_t written = 0;

    while (written < len) {
        uint16_t next = (tx_buf.head + 1) % TX_BUF_SIZE;
        if (next == tx_buf.tail) break;  // Buffer full

        tx_buf.buffer[tx_buf.head] = data[written++];
        tx_buf.head = next;
    }

    IER |= 0x02;  // Enable TX interrupt
    return written;
}

size_t uart_read(uint8_t *data, size_t max) {
    size_t count = 0;

    while ((rx_buf.tail != rx_buf.head) && (count < max)) {
        data[count++] = rx_buf.buffer[rx_buf.tail];
        rx_buf.tail = (rx_buf.tail + 1) % RX_BUF_SIZE;
    }

    return count;
}
```

## Command Line Interface

```c
#define CMD_BUF_SIZE 128

static char cmd_buf[CMD_BUF_SIZE];
static uint8_t cmd_pos = 0;

void cli_process_char(char c) {
    switch (c) {
        case '\r':
        case '\n':
            debug_puts("\r\n");
            cmd_buf[cmd_pos] = '\0';
            cli_execute(cmd_buf);
            cmd_pos = 0;
            debug_puts("> ");
            break;

        case '\b':
        case 0x7F:  // DEL
            if (cmd_pos > 0) {
                cmd_pos--;
                debug_puts("\b \b");
            }
            break;

        default:
            if (cmd_pos < CMD_BUF_SIZE - 1) {
                cmd_buf[cmd_pos++] = c;
                debug_putchar(c);
            }
            break;
    }
}

void cli_execute(const char *cmd) {
    if (strcmp(cmd, "help") == 0) {
        debug_puts("Available commands:\r\n");
        debug_puts("  help   - Show this help\r\n");
        debug_puts("  status - Show UART status\r\n");
    }
    else if (strcmp(cmd, "status") == 0) {
        char buf[64];
        sprintf(buf, "LSR: 0x%02X  MSR: 0x%02X\r\n", LSR, MSR);
        debug_puts(buf);
    }
    else if (cmd[0] != '\0') {
        debug_puts("Unknown command: ");
        debug_puts(cmd);
        debug_puts("\r\n");
    }
}
```

## Loopback Test

```c
bool uart_loopback_test(void) {
    uint8_t test_data[] = {0x00, 0x55, 0xAA, 0xFF};

    // Enable loopback mode
    MCR |= 0x10;

    // Clear FIFOs
    FCR = 0x07;

    // Send test data
    for (int i = 0; i < sizeof(test_data); i++) {
        THR = test_data[i];
    }

    // Wait for transmission
    while ((LSR & 0x40) == 0);

    // Short delay for internal loopback
    for (volatile int i = 0; i < 100; i++);

    // Read back and verify
    for (int i = 0; i < sizeof(test_data); i++) {
        if (!(LSR & 0x01)) {
            MCR &= ~0x10;
            return false;  // No data received
        }

        uint8_t received = RBR;
        if (received != test_data[i]) {
            MCR &= ~0x10;
            return false;  // Data mismatch
        }
    }

    // Disable loopback
    MCR &= ~0x10;

    return true;
}
```

## Hardware Flow Control

```c
void uart_init_with_flow_control(void) {
    // Standard init
    LCR = 0x80; DLL = 26; DLM = 0; LCR = 0x03;
    FCR = 0xC7;  // Enable FIFOs, trigger=14

    // Enable auto flow control
    MCR = 0x22;  // RTS + AFE

    // Enable RX interrupt
    IER = 0x01;
}

// With AFE enabled:
// - RTS automatically deasserts when RX FIFO nearly full
// - TX automatically pauses when CTS deasserts
// No software intervention needed for flow control
```

---

**Back to:** [00_overview.md](00_overview.md) - Programming Model Overview

**Next Chapter:** [Chapter 5: Registers](../ch05_registers/01_register_map.md)
