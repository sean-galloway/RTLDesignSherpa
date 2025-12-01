# APB UART 16550 - Clocks and Reset

## Clock Signals

### pclk (APB Clock)
- **Purpose:** Primary APB bus clock
- **Usage:** APB protocol, register access
- **Typical Frequency:** 50-200 MHz

### uart_clk (Optional)
- **Purpose:** UART baud rate reference clock
- **Usage:** Only when CDC_ENABLE=1
- **Typical Frequency:** 1.8432 MHz, 14.7456 MHz, or higher

## Reset Signals

### presetn (APB Reset)
- **Type:** Active-low asynchronous reset
- **Scope:** APB interface logic
- **Behavior:** Resets APB state machine, clears pending transactions

### uart_rstn (Optional)
- **Type:** Active-low asynchronous reset
- **Scope:** UART core logic
- **Usage:** Only when CDC_ENABLE=1
- **Behavior:** Resets TX/RX engines, FIFOs, baud generator

## Reset Behavior

### Register Reset Values

| Register | Reset Value | Notes |
|----------|-------------|-------|
| RBR | Undefined | Read-only, FIFO content |
| THR | N/A | Write-only |
| IER | 0x00 | All interrupts disabled |
| IIR | 0x01 | No interrupt pending |
| FCR | 0x00 | FIFOs disabled |
| LCR | 0x00 | 5 data bits, 1 stop, no parity |
| MCR | 0x00 | All outputs deasserted |
| LSR | 0x60 | THRE=1, TEMT=1 (TX empty) |
| MSR | 0x00 | No delta, inputs low |
| SCR | 0x00 | Scratch cleared |
| DLL | 0x00 | Divisor LSB = 0 |
| DLM | 0x00 | Divisor MSB = 0 |

### Serial Line State During Reset

During reset:
- `txd` = 1 (idle/mark state)
- Receiver disabled
- Transmitter disabled
- FIFOs cleared

## Clock Domain Crossing

### When CDC_ENABLE = 0
- All logic runs on `pclk`
- Baud generator derives timing from `pclk`
- Best for systems where pclk is stable

### When CDC_ENABLE = 1
- APB interface uses `pclk`
- UART core uses `uart_clk`
- Skid buffers handle CDC
- Allows dedicated baud reference clock

## Baud Rate Considerations

### Clock Accuracy

For reliable communication:
- Baud rate error should be < 2%
- Combined TX+RX error < 4%

### Common Clock Frequencies

| Clock | Exact Baud Rates | Notes |
|-------|-----------------|-------|
| 1.8432 MHz | 115200, 57600, 38400, 19200, 9600 | Classic UART clock |
| 14.7456 MHz | 921600, 460800, ... 9600 | 8x above, higher rates |
| 48 MHz | Most rates with small error | System clock compatible |
| 50 MHz | Most rates with small error | Common FPGA clock |

### Example: 48 MHz Clock

| Baud Rate | Divisor | Actual Rate | Error |
|-----------|---------|-------------|-------|
| 9600 | 312 | 9615.4 | +0.16% |
| 19200 | 156 | 19230.8 | +0.16% |
| 38400 | 78 | 38461.5 | +0.16% |
| 57600 | 52 | 57692.3 | +0.16% |
| 115200 | 26 | 115384.6 | +0.16% |
| 230400 | 13 | 230769.2 | +0.16% |
| 460800 | 7 | 428571.4 | -6.99% |
| 921600 | 3 | 1000000 | +8.51% |

## Timing Constraints

### Synchronous Mode
- Standard single-clock timing
- All paths constrained to pclk

### Asynchronous Mode
- Set false_path between pclk and uart_clk domains
- Set max_delay for CDC paths
- RXD input should have IOB register

### External Interface Timing

| Signal | Timing | Notes |
|--------|--------|-------|
| txd | Output register | Clean edges |
| rxd | Input synchronizer | 2-stage FF |
| Modem signals | Input synchronizer | 2-stage FF |

---

**Next:** [04_acronyms.md](04_acronyms.md) - Acronyms and terminology
