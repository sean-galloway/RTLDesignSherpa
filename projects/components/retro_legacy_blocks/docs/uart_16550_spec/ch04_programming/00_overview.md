# APB UART 16550 - Programming Model Overview

## Register Summary

| Offset | DLAB=0 | DLAB=1 | Access | Description |
|--------|--------|--------|--------|-------------|
| 0x00 | RBR/THR | DLL | RO/WO/RW | Data / Divisor LSB |
| 0x04 | IER | DLM | RW | Interrupt Enable / Divisor MSB |
| 0x08 | IIR/FCR | IIR/FCR | RO/WO | Interrupt ID / FIFO Control |
| 0x0C | LCR | LCR | RW | Line Control |
| 0x10 | MCR | MCR | RW | Modem Control |
| 0x14 | LSR | LSR | RO | Line Status |
| 0x18 | MSR | MSR | RO | Modem Status |
| 0x1C | SCR | SCR | RW | Scratch |

## Chapter Contents

### Initialization
Complete UART initialization sequence.

**See:** [01_initialization.md](01_initialization.md)

### Data Transfer
Sending and receiving data.

**See:** [02_data_transfer.md](02_data_transfer.md)

### Interrupts
Interrupt configuration and handling.

**See:** [03_interrupts.md](03_interrupts.md)

### Examples
Complete programming examples.

**See:** [04_examples.md](04_examples.md)

## Quick Start

### Minimal Setup (115200 8N1)

```c
// Assuming 48 MHz clock
#define DIVISOR 26  // 48MHz / (16 * 115200) = 26

void uart_init(void) {
    // Set DLAB to access divisor
    LCR = 0x80;

    // Set baud rate divisor
    DLL = DIVISOR & 0xFF;
    DLM = DIVISOR >> 8;

    // 8N1, clear DLAB
    LCR = 0x03;

    // Enable FIFOs, reset, trigger=14
    FCR = 0xC7;

    // Enable interrupts
    IER = 0x01;  // RX data available
}
```

---

**Next:** [01_initialization.md](01_initialization.md) - Initialization
