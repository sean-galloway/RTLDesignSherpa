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

# APB UART 16550 - Overview

## Introduction

The APB UART 16550 is a 16550-compatible Universal Asynchronous Receiver/Transmitter with an APB slave interface. It provides standard serial communication with configurable baud rates, data formats, and FIFO buffering.

## Key Features

### Serial Communication
- Full-duplex asynchronous serial operation
- Configurable baud rates (up to 3 Mbps at 48 MHz clock)
- 5, 6, 7, or 8 data bits
- 1 or 2 stop bits (2 stop bits only for 6/7/8-bit words; 1.5 stop bits is not implemented)
- Even, odd, mark, space, or no parity

### FIFO Buffering
- 16-byte transmit FIFO
- 16-byte receive FIFO
- Configurable trigger levels (1, 4, 8, 14 bytes)
- FIFOs are always 16 deep; FCR.FE only changes IIR[7:6] and the RX-data interrupt condition (there is no true FIFO-disable / single-byte 8250 mode)

### Interrupt System
- Prioritized interrupts
- Receive data available
- Transmitter holding register empty
- Receiver line status (errors)
- Modem status changes

### Modem Control
- Hardware flow control (CTS/RTS)
- Full modem signals (DTR, DSR, DCD, RI)
- Programmable outputs (OUT1, OUT2)
- Loopback mode for testing

## Applications

- Debug consoles
- System management interfaces
- Legacy device communication
- Embedded system UART
- Modem interfaces

## Block Diagram

### Figure 1.1: UART 16550 Block Diagram

![UART 16550 Block Diagram](../assets/svg/uart_top.svg)

## Compatibility

The design is register-compatible with:
- National Semiconductor PC16550D
- TI TL16C550C
- Standard 16550 UART cores

### Differences from Original 16550
- APB interface instead of ISA/parallel bus
- Configurable clock domain crossing support
- PeakRDL-generated register file

## Register Summary

This implementation uses a flat, DLAB-independent address map - each register has a unique offset and LCR[7] (DLAB) does not remap any address. See [Chapter 5](../ch05_registers/01_register_map.md) for full field detail.

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x00 | RBR / THR | R / W | Receive Buffer (read) / Transmit Holding (write) |
| 0x04 | IER | RW | Interrupt Enable |
| 0x08 | IIR | RO | Interrupt Identification |
| 0x0C | FCR | RW | FIFO Control |
| 0x10 | LCR | RW | Line Control |
| 0x14 | MCR | RW | Modem Control |
| 0x18 | LSR | RO/W1C | Line Status |
| 0x1C | MSR | RO/W1C | Modem Status |
| 0x20 | SCR | RW | Scratch Register |
| 0x24 | DLL | RW | Divisor Latch LSB |
| 0x28 | DLM | RW | Divisor Latch MSB |

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| FIFO_DEPTH | 16 | TX/RX FIFO depth |
| CDC_ENABLE | 0 | Clock domain crossing |
| SYNC_STAGES | 2 | Synchronizer stages for CDC |
| SKID_DEPTH | - | Skid-buffer depth for CDC path |

---

**Next:** [02_architecture.md](02_architecture.md) - Architecture details
