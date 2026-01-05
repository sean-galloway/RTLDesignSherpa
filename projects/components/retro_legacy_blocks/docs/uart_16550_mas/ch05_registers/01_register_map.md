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

# APB UART 16550 - Register Map

## Register Summary

| Offset | DLAB=0 Read | DLAB=0 Write | DLAB=1 | Description |
|--------|-------------|--------------|--------|-------------|
| 0x00 | RBR | THR | DLL | Receive Buffer / Transmit Hold / Divisor LSB |
| 0x04 | IER | IER | DLM | Interrupt Enable / Divisor MSB |
| 0x08 | IIR | FCR | IIR/FCR | Interrupt ID / FIFO Control |
| 0x0C | LCR | LCR | LCR | Line Control |
| 0x10 | MCR | MCR | MCR | Modem Control |
| 0x14 | LSR | - | LSR | Line Status |
| 0x18 | MSR | - | MSR | Modem Status |
| 0x1C | SCR | SCR | SCR | Scratch |

---

## RBR - Receiver Buffer Register (0x00, DLAB=0, Read Only)

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| 7:0 | DATA | RO | Received data byte |

**Note:** Reading RBR pops data from the RX FIFO.

---

## THR - Transmitter Holding Register (0x00, DLAB=0, Write Only)

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| 7:0 | DATA | WO | Data to transmit |

**Note:** Writing THR pushes data to the TX FIFO.

---

## DLL - Divisor Latch LSB (0x00, DLAB=1, R/W)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | DLL | RW | 0x00 | Baud rate divisor low byte |

---

## DLM - Divisor Latch MSB (0x04, DLAB=1, R/W)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | DLM | RW | 0x00 | Baud rate divisor high byte |

---

## IER - Interrupt Enable Register (0x04, DLAB=0, R/W)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | ERBFI | RW | 0 | Enable Received Data Available Interrupt |
| 1 | ETBEI | RW | 0 | Enable Transmitter Holding Register Empty |
| 2 | ELSI | RW | 0 | Enable Receiver Line Status Interrupt |
| 3 | EDSSI | RW | 0 | Enable Modem Status Interrupt |
| 7:4 | Reserved | RO | 0 | Reserved |

---

## IIR - Interrupt Identification Register (0x08, Read Only)

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| 0 | IPEND | RO | 0=Interrupt pending, 1=No interrupt |
| 3:1 | IID | RO | Interrupt ID (see table below) |
| 5:4 | Reserved | RO | Reserved |
| 7:6 | FIFOEN | RO | 11=FIFOs enabled, 00=disabled |

### Interrupt ID Encoding

| IID[2:0] | IIR[3:0] | Priority | Source | Clear Method |
|----------|----------|----------|--------|--------------|
| 011 | 0110 | 1 | Line Status | Read LSR |
| 010 | 0100 | 2 | RX Data Available | Read RBR |
| 110 | 1100 | 2 | Character Timeout | Read RBR |
| 001 | 0010 | 3 | THR Empty | Read IIR or Write THR |
| 000 | 0000 | 4 | Modem Status | Read MSR |

---

## FCR - FIFO Control Register (0x08, Write Only)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | FE | WO | FIFO Enable |
| 1 | RFR | WO | RX FIFO Reset (self-clearing) |
| 2 | TFR | WO | TX FIFO Reset (self-clearing) |
| 3 | DMS | WO | DMA Mode Select |
| 5:4 | Reserved | WO | Reserved |
| 7:6 | RTL | WO | RX Trigger Level |

### RX Trigger Level

| RTL[1:0] | Trigger Level |
|----------|---------------|
| 00 | 1 byte |
| 01 | 4 bytes |
| 10 | 8 bytes |
| 11 | 14 bytes |

---

## LCR - Line Control Register (0x0C, R/W)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 1:0 | WLS | RW | 00 | Word Length Select |
| 2 | STB | RW | 0 | Stop Bits |
| 3 | PEN | RW | 0 | Parity Enable |
| 4 | EPS | RW | 0 | Even Parity Select |
| 5 | SP | RW | 0 | Stick Parity |
| 6 | BC | RW | 0 | Break Control |
| 7 | DLAB | RW | 0 | Divisor Latch Access Bit |

### Word Length

| WLS[1:0] | Data Bits |
|----------|-----------|
| 00 | 5 |
| 01 | 6 |
| 10 | 7 |
| 11 | 8 |

### Parity Selection

| PEN | EPS | SP | Parity |
|-----|-----|-----|--------|
| 0 | X | X | None |
| 1 | 0 | 0 | Odd |
| 1 | 1 | 0 | Even |
| 1 | 0 | 1 | Mark (1) |
| 1 | 1 | 1 | Space (0) |

---

## MCR - Modem Control Register (0x10, R/W)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | DTR | RW | 0 | Data Terminal Ready |
| 1 | RTS | RW | 0 | Request To Send |
| 2 | OUT1 | RW | 0 | User Output 1 |
| 3 | OUT2 | RW | 0 | User Output 2 |
| 4 | LOOP | RW | 0 | Loopback Mode |
| 5 | AFE | RW | 0 | Auto Flow Control Enable |
| 7:6 | Reserved | RO | 0 | Reserved |

---

## LSR - Line Status Register (0x14, Read Only)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | DR | RO | Data Ready |
| 1 | OE | RO | Overrun Error (clear on read) |
| 2 | PE | RO | Parity Error (clear on read) |
| 3 | FE | RO | Framing Error (clear on read) |
| 4 | BI | RO | Break Interrupt (clear on read) |
| 5 | THRE | RO | Transmitter Holding Register Empty |
| 6 | TEMT | RO | Transmitter Empty |
| 7 | FIFOERR | RO | Error in RX FIFO |

---

## MSR - Modem Status Register (0x18, Read Only)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | DCTS | RO | Delta Clear To Send (clear on read) |
| 1 | DDSR | RO | Delta Data Set Ready (clear on read) |
| 2 | TERI | RO | Trailing Edge Ring Indicator (clear on read) |
| 3 | DDCD | RO | Delta Data Carrier Detect (clear on read) |
| 4 | CTS | RO | Clear To Send |
| 5 | DSR | RO | Data Set Ready |
| 6 | RI | RO | Ring Indicator |
| 7 | DCD | RO | Data Carrier Detect |

---

## SCR - Scratch Register (0x1C, R/W)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | DATA | RW | 0x00 | General-purpose storage |

---

## Address Calculation

For system address:
```
Register_Address = BASE_ADDR + WINDOW_OFFSET + Register_Offset

Where:
  BASE_ADDR = 0xFEC00000 (RLB base)
  WINDOW_OFFSET = 0x8000 (UART window)
  Register_Offset = value from table above

Example:
  LSR = 0xFEC00000 + 0x8000 + 0x14 = 0xFEC08014
```

---

**Back to:** [UART 16550 Specification Index](../uart_16550_index.md)
