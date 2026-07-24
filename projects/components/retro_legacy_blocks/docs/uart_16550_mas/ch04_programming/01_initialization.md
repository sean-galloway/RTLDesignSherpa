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

# APB UART 16550 - Initialization

## Basic Initialization Sequence

### Step 1: Set Baud Rate

```c
void uart_set_baud(uint16_t divisor) {
    // DLL (0x24) and DLM (0x28) have dedicated offsets - no DLAB toggle needed.
    DLL = divisor & 0xFF;
    DLM = (divisor >> 8) & 0xFF;
}
```

### Step 2: Configure Line Format

```c
void uart_set_format(uint8_t data_bits, uint8_t parity, uint8_t stop_bits) {
    uint8_t lcr = 0;

    // Data bits: 5=0, 6=1, 7=2, 8=3
    lcr |= (data_bits - 5) & 0x03;

    // Stop bits: 1=0, 2=1. STB=1 gives 2 stop bits for 6/7/8-bit words.
    // 1.5 stop bits (5-bit word) is NOT implemented - it produces 1 stop bit.
    if (stop_bits == 2) lcr |= 0x04;

    // Parity: 0=none, 1=odd, 2=even, 3=mark, 4=space
    switch (parity) {
        case 1: lcr |= 0x08; break;        // Odd
        case 2: lcr |= 0x18; break;        // Even
        case 3: lcr |= 0x28; break;        // Mark
        case 4: lcr |= 0x38; break;        // Space
    }

    LCR = lcr;
}
```

### Step 3: Configure FIFOs

```c
void uart_configure_fifo(uint8_t trigger_level) {
    uint8_t fcr = 0x01;  // Enable FIFOs

    // Trigger level: 0=1, 1=4, 2=8, 3=14
    fcr |= (trigger_level & 0x03) << 6;

    // Reset both FIFOs
    fcr |= 0x06;

    FCR = fcr;
}
```

### Step 4: Enable Interrupts

```c
void uart_enable_interrupts(uint8_t mask) {
    // Bits: 0=RX, 1=TX, 2=Line, 3=Modem
    // NOTE: In this RTL the IER enables are unimplemented - this write is
    // stored and read back but does not mask interrupts. Pending sources
    // drive the irq pin (gated by MCR.OUT2) regardless of IER.
    IER = mask & 0x0F;
}
```

## Complete Initialization Example

```c
// Common baud rate divisors for 48 MHz clock
#define BAUD_9600    312
#define BAUD_19200   156
#define BAUD_38400   78
#define BAUD_57600   52
#define BAUD_115200  26

void uart_init_115200_8n1(void) {
    // 1. Set baud rate (DLL=0x24, DLM=0x28 - no DLAB toggle)
    DLL = BAUD_115200;       // Low byte
    DLM = 0x00;              // High byte

    // 2. Line format: 8 data bits, no parity, 1 stop bit
    LCR = 0x03;

    // 3. Enable and reset FIFOs, trigger at 14 bytes
    FCR = 0xC7;              // 11000111b

    // 4. Modem control: set OUT2 (bit 3) to ungate the irq pin
    MCR = 0x08;

    // 5. Drain any pending RX data (received byte is in RBR bits [15:8])
    while (LSR & 0x01)
        (void)RBR;

    // NOTE: IER (interrupt enables) is unimplemented in this RTL - writing it
    // has no effect. Poll LSR/IIR, or note that pending sources drive irq
    // (gated by MCR.OUT2) regardless of IER. LSR/MSR sticky bits are W1C,
    // not clear-on-read.
}
```

## Baud Rate Calculation

### Formula

```
Divisor = Clock_Frequency / (16 * Baud_Rate)
```

### Divisor Calculator Function

```c
uint16_t uart_calculate_divisor(uint32_t clock_hz, uint32_t baud) {
    // Round to nearest
    return (clock_hz + (8 * baud)) / (16 * baud);
}
```

### Common Clock Frequencies

| Clock | 9600 | 19200 | 38400 | 57600 | 115200 |
|-------|------|-------|-------|-------|--------|
| 48 MHz | 312 | 156 | 78 | 52 | 26 |
| 50 MHz | 326 | 163 | 81 | 54 | 27 |
| 100 MHz | 651 | 326 | 163 | 109 | 54 |

## Flow Control Setup (manual)

Auto Flow Control (AFE, MCR[5]) is NOT implemented in this RTL. Assert RTS in
software and monitor MSR.CTS to gate transmission manually.

```c
void uart_assert_rts(void) {
    uint8_t mcr = MCR;
    mcr |= 0x02;             // RTS (bit 1) only - MCR[5]/AFE does not exist
    MCR = mcr;
}
```

## Loopback Mode Setup

```c
void uart_enable_loopback(void) {
    uint8_t mcr = MCR;
    mcr |= 0x10;             // LOOP bit
    MCR = mcr;
}
```

---

**Next:** [02_data_transfer.md](02_data_transfer.md) - Data Transfer
