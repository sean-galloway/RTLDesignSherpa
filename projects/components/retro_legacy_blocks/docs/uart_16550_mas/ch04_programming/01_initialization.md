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
    uint8_t lcr_save = LCR;

    // Enable DLAB to access divisor latches
    LCR = lcr_save | 0x80;

    // Write divisor
    DLL = divisor & 0xFF;
    DLM = (divisor >> 8) & 0xFF;

    // Restore LCR (clears DLAB)
    LCR = lcr_save;
}
```

### Step 2: Configure Line Format

```c
void uart_set_format(uint8_t data_bits, uint8_t parity, uint8_t stop_bits) {
    uint8_t lcr = 0;

    // Data bits: 5=0, 6=1, 7=2, 8=3
    lcr |= (data_bits - 5) & 0x03;

    // Stop bits: 1=0, 2=1 (1.5 for 5-bit)
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
    // 1. Disable interrupts during setup
    IER = 0x00;

    // 2. Set baud rate
    LCR = 0x80;              // DLAB = 1
    DLL = BAUD_115200;       // Low byte
    DLM = 0x00;              // High byte
    LCR = 0x03;              // 8 data bits, clear DLAB

    // 3. No parity, 1 stop bit already set by LCR = 0x03

    // 4. Enable and reset FIFOs, trigger at 14 bytes
    FCR = 0xC7;              // 11000111b

    // 5. Initialize modem control
    MCR = 0x00;              // All outputs deasserted

    // 6. Clear any pending data/errors
    (void)LSR;               // Clear line status
    (void)MSR;               // Clear modem status
    while (LSR & 0x01)       // Clear RX FIFO
        (void)RBR;

    // 7. Enable desired interrupts
    IER = 0x05;              // RX data + line status
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

## Hardware Flow Control Setup

```c
void uart_enable_hw_flow_control(void) {
    // Enable auto flow control
    uint8_t mcr = MCR;
    mcr |= 0x22;             // RTS + AFE
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
