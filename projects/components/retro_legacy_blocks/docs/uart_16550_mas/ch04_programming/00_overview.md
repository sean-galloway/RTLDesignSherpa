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

# APB UART 16550 - Programming Model Overview

## Register Summary

Flat, DLAB-independent map - each register has a unique offset (DLAB does not remap).

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x00 | RBR / THR | R / W | Receive Buffer (read) / Transmit Holding (write) |
| 0x04 | IER | RW | Interrupt Enable (stored; unimplemented) |
| 0x08 | IIR | RO | Interrupt Identification |
| 0x0C | FCR | RW | FIFO Control |
| 0x10 | LCR | RW | Line Control |
| 0x14 | MCR | RW | Modem Control |
| 0x18 | LSR | RO/W1C | Line Status |
| 0x1C | MSR | RO/W1C | Modem Status |
| 0x20 | SCR | RW | Scratch |
| 0x24 | DLL | RW | Divisor Latch LSB |
| 0x28 | DLM | RW | Divisor Latch MSB |

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
    // Set baud rate divisor directly - no DLAB toggle (DLL=0x24, DLM=0x28)
    DLL = DIVISOR & 0xFF;
    DLM = DIVISOR >> 8;

    // 8N1
    LCR = 0x03;

    // Enable FIFOs, reset, trigger=14
    FCR = 0xC7;

    // Set MCR.OUT2 to ungate the irq pin (IER enables are unimplemented;
    // poll LSR/IIR rather than relying on IER masking).
    MCR = 0x08;
}
```

---

**Next:** [01_initialization.md](01_initialization.md) - Initialization
