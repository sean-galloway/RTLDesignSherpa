# APB UART 16550 - Acronyms and Terminology

## Protocol Acronyms

| Acronym | Full Name | Description |
|---------|-----------|-------------|
| APB | Advanced Peripheral Bus | Low-power AMBA bus protocol |
| UART | Universal Asynchronous Receiver/Transmitter | Serial communication interface |
| RS-232 | Recommended Standard 232 | Serial communication standard |
| TTL | Transistor-Transistor Logic | Logic voltage levels |

## Register Acronyms

| Acronym | Full Name | Description |
|---------|-----------|-------------|
| RBR | Receiver Buffer Register | Read received data |
| THR | Transmitter Holding Register | Write data to transmit |
| IER | Interrupt Enable Register | Enable interrupt sources |
| IIR | Interrupt Identification Register | Identify pending interrupt |
| FCR | FIFO Control Register | Configure FIFOs |
| LCR | Line Control Register | Configure data format |
| MCR | Modem Control Register | Control modem outputs |
| LSR | Line Status Register | TX/RX status and errors |
| MSR | Modem Status Register | Modem input status |
| SCR | Scratch Register | General-purpose storage |
| DLL | Divisor Latch LSB | Baud rate low byte |
| DLM | Divisor Latch MSB | Baud rate high byte |

## Signal Acronyms

| Acronym | Full Name | Description |
|---------|-----------|-------------|
| TXD | Transmit Data | Serial output |
| RXD | Receive Data | Serial input |
| CTS | Clear To Send | Flow control input |
| RTS | Request To Send | Flow control output |
| DTR | Data Terminal Ready | Modem control output |
| DSR | Data Set Ready | Modem status input |
| DCD | Data Carrier Detect | Modem status input |
| RI | Ring Indicator | Modem status input |

## FIFO Terms

| Term | Description |
|------|-------------|
| FIFO | First-In First-Out buffer |
| Trigger Level | FIFO depth at which interrupt occurs |
| Overflow | Receive FIFO full, data lost |
| Underflow | Transmit FIFO empty |
| THRE | Transmitter Holding Register Empty |
| TEMT | Transmitter Empty (shift register too) |

## Data Format Terms

| Term | Description |
|------|-------------|
| Start Bit | Logic 0, signals start of character |
| Data Bits | 5-8 bits of payload data |
| Parity Bit | Optional error detection bit |
| Stop Bit | Logic 1, signals end of character |
| Mark | Logic 1 / idle state |
| Space | Logic 0 |
| Break | Extended space condition |

## Error Terms

| Term | Description |
|------|-------------|
| Parity Error | Received parity doesn't match expected |
| Framing Error | Stop bit not detected |
| Overrun Error | New data arrived before previous read |
| Break Interrupt | Extended low condition detected |

## Timing Terms

| Term | Description |
|------|-------------|
| Baud Rate | Bits per second |
| Bit Time | 1 / Baud Rate |
| Divisor | Clock divider for baud generation |
| 16x Clock | Internal oversample clock (16x baud) |

---

**Next:** [05_references.md](05_references.md) - Reference documents
