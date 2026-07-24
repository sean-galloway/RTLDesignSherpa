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

This implementation uses a **flat, DLAB-independent** address map: every register has its own unique offset. Unlike a classic 16550, the Divisor Latch Access Bit (LCR[7]) does **not** remap any address. LCR[7] is a stored bit with no effect on address decoding, and DLL/DLM have their own dedicated offsets (0x24/0x28). Register offsets are byte offsets; only `paddr[5:0]` is decoded (see Address Calculation).

| Offset | Register | Access | Reset | Description |
|--------|----------|--------|-------|-------------|
| 0x00 | RBR / THR | R / W | - | Receive Buffer (read) / Transmit Holding (write) |
| 0x04 | IER | RW | 0x00 | Interrupt Enable (stored; no hardware effect - see note) |
| 0x08 | IIR | RO | 0x02 | Interrupt Identification |
| 0x0C | FCR | RW | 0x00 | FIFO Control (readable in this implementation) |
| 0x10 | LCR | RW | 0x03 | Line Control (8N1 at reset) |
| 0x14 | MCR | RW | 0x00 | Modem Control |
| 0x18 | LSR | RO / W1C | 0x60 | Line Status |
| 0x1C | MSR | RO / W1C | 0x00 | Modem Status |
| 0x20 | SCR | RW | 0x00 | Scratch |
| 0x24 | DLL | RW | 0x01 | Divisor Latch LSB |
| 0x28 | DLM | RW | 0x00 | Divisor Latch MSB |

Offsets 0x2C-0x3F are unused and acknowledge reads as zero.

---

## RBR - Receiver Buffer Register (0x00, Read)

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| 15:8 | DATA | RO | Received data byte (see note) |
| 7:0 | - | RO | Returns the last value written to THR (see note) |

**Note:** Reading offset 0x00 pops data from the RX FIFO. In this implementation the received byte is returned in bits **[15:8]**, and bits **[7:0]** return the last byte written to THR - not the received byte. This deviates from the standard 16550 (which returns the received byte in [7:0]) and is a known RTL issue; software must read the received byte from bits [15:8].

---

## THR - Transmitter Holding Register (0x00, Write)

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| 7:0 | DATA | WO | Data to transmit |

**Note:** Writing offset 0x00 pushes data to the TX FIFO. The written value is also stored and is what appears in bits [7:0] of a subsequent RBR read (see RBR note); it is not otherwise software-visible.

---

## IER - Interrupt Enable Register (0x04, R/W)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | ERBFI | RW | 0 | Enable Received Data Available Interrupt |
| 1 | ETBEI | RW | 0 | Enable Transmitter Holding Register Empty |
| 2 | ELSI | RW | 0 | Enable Receiver Line Status Interrupt |
| 3 | EDSSI | RW | 0 | Enable Modem Status Interrupt |
| 7:4 | Reserved | RO | 0 | Reserved |

**Note:** These bits are stored and read back, but the RTL does not connect them to any interrupt logic - the interrupt enables are **unimplemented**. IIR reports pending sources and the `irq` pin asserts independently of IER. Writing IER has no effect on interrupt behavior. See `ch03_interfaces/04_interrupt.md`.

---

## IIR - Interrupt Identification Register (0x08, Read Only)

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| 0 | IPEND | RO | 0=Interrupt pending, 1=No interrupt |
| 3:1 | IID | RO | Interrupt ID (see table below) |
| 5:4 | Reserved | RO | Reserved |
| 7:6 | FIFOEN | RO | 11=FIFOs enabled, 00=disabled |

### Interrupt ID Encoding

IIR[0]=IPEND (0 = interrupt pending). IIR[3:1]=IID. IIR[3] (timeout) is always 0 in this implementation.

| IIR[3:0] | Priority | Source | Clear Method |
|----------|----------|--------|--------------|
| 0110 | 1 | Line Status | Clear LSR error bits (W1C - see note) |
| 0100 | 2 | RX Data Available | Read RBR until DR clears |
| 0010 | 3 | THR Empty | Write THR (fills TX FIFO) |
| 0000 | 4 | Modem Status | Clear MSR delta bits (W1C - see note) |

**Note:** The **Character Timeout** interrupt (IIR = 0x0C, IIR[3]) is **not implemented** - `int_timeout` is tied to 0 in the RTL, so IIR[3] never asserts and IIR can never read 0x0C. Reading IIR has **no** side effect; it does not clear the THR-empty condition. The THR-empty source is the level "TX FIFO empty" and clears only when the FIFO is refilled. Because interrupt enables are unimplemented (see IER), IIR reflects pending sources regardless of IER, and the `irq` pin is additionally gated by MCR.OUT2 (see MCR note).

---

## FCR - FIFO Control Register (0x0C, R/W)

FCR is fully readable in this implementation (a standard 16550 FCR is write-only).

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | FE | RW | FIFO Enable |
| 1 | RFR | RW | RX FIFO Reset (self-clearing) |
| 2 | TFR | RW | TX FIFO Reset (self-clearing) |
| 3 | DMS | RW | DMA Mode Select (stored; no effect - no DMA signals exist) |
| 5:4 | Reserved | RO | Reserved (read as 0) |
| 7:6 | RTL | RW | RX Trigger Level |

### RX Trigger Level

| RTL[1:0] | Trigger Level |
|----------|---------------|
| 00 | 1 byte |
| 01 | 4 bytes |
| 10 | 8 bytes |
| 11 | 14 bytes |

---

## LCR - Line Control Register (0x10, R/W)

Reset value is **0x03** (8 data bits, 1 stop bit, no parity - 8N1).

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 1:0 | WLS | RW | 11 | Word Length Select (reset = 8 bits) |
| 2 | STB | RW | 0 | Stop Bits (see note) |
| 3 | PEN | RW | 0 | Parity Enable |
| 4 | EPS | RW | 0 | Even Parity Select |
| 5 | SP | RW | 0 | Stick Parity |
| 6 | BC | RW | 0 | Break Control |
| 7 | DLAB | RW | 0 | Divisor Latch Access Bit (stored; no effect on decode) |

**Note (DLAB):** LCR[7] is stored and read back but has **no effect** - it does not remap any address. DLL/DLM are always at 0x24/0x28. **Note (STB):** STB=1 selects 2 stop bits for 6/7/8-bit words; 1.5 stop bits (for 5-bit words) is **not implemented** - a 5-bit word with STB=1 still produces 1 stop bit.

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

## MCR - Modem Control Register (0x14, R/W)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | DTR | RW | 0 | Data Terminal Ready |
| 1 | RTS | RW | 0 | Request To Send |
| 2 | OUT1 | RW | 0 | User Output 1 (active low) |
| 3 | OUT2 | RW | 0 | User Output 2 / interrupt gate (active low) - see note |
| 4 | LOOP | RW | 0 | Loopback Mode |
| 7:5 | Reserved | RO | 0 | Reserved (read as 0) |

**Note:** Bit 5 (AFE, Auto Flow Control Enable) is **not implemented** in this RTL - MCR is only 5 bits wide (DTR/RTS/OUT1/OUT2/LOOP) and writes to bit 5 are dropped. There is no CTS-gated transmit and RTS is not auto-driven by RX FIFO level. Additionally, OUT2 gates the `irq` output pin: `irq` can assert only when MCR.OUT2 = 1. With the reset value MCR = 0x00, the `irq` pin is masked; software must set MCR.OUT2 to route interrupts to the pin.

---

## LSR - Line Status Register (0x18, Read / W1C)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | DR | RO | Data Ready |
| 1 | OE | W1C | Overrun Error (write 1 to clear - see note) |
| 2 | PE | W1C | Parity Error (write 1 to clear - see note) |
| 3 | FE | W1C | Framing Error (write 1 to clear - see note) |
| 4 | BI | W1C | Break Interrupt (write 1 to clear - see note) |
| 5 | THRE | RO | Transmitter Holding Register Empty (TX FIFO empty) |
| 6 | TEMT | RO | Transmitter Empty (FIFO and shift register empty) |
| 7 | FIFOERR | RO | Error in RX FIFO head entry |

**Note:** The error bits [4:1] are **write-1-to-clear (W1C)**, not clear-on-read as a standard 16550. Reading LSR has no clearing side effect. Furthermore, in the current RTL the core never asserts the internal clear strobes, so once set these bits (and the associated line-status interrupt) remain asserted until full reset - a known RTL issue. FIFOERR (bit 7) reflects only the RX FIFO **head** entry, not "any entry in the FIFO".

---

## MSR - Modem Status Register (0x1C, Read / W1C)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | DCTS | W1C | Delta Clear To Send (write 1 to clear - see note) |
| 1 | DDSR | W1C | Delta Data Set Ready (write 1 to clear - see note) |
| 2 | TERI | W1C | Trailing Edge Ring Indicator (write 1 to clear - see note) |
| 3 | DDCD | W1C | Delta Data Carrier Detect (write 1 to clear - see note) |
| 4 | CTS | RO | Clear To Send |
| 5 | DSR | RO | Data Set Ready |
| 6 | RI | RO | Ring Indicator |
| 7 | DCD | RO | Data Carrier Detect |

**Note:** The delta bits [3:0] are **write-1-to-clear (W1C)**, not clear-on-read. As with LSR, the current RTL does not assert the internal clear strobes, so a delta bit (and the modem-status interrupt) stays set until full reset - a known RTL issue.

---

## SCR - Scratch Register (0x20, R/W)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | DATA | RW | 0x00 | General-purpose storage |

---

## DLL - Divisor Latch LSB (0x24, R/W)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | DLL | RW | 0x01 | Baud rate divisor low byte |

**Note:** Reset value is **0x01** (not 0x00). Accessed directly at 0x24 - no DLAB toggle required.

---

## DLM - Divisor Latch MSB (0x28, R/W)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | DLM | RW | 0x00 | Baud rate divisor high byte |

**Note:** Accessed directly at 0x28 - no DLAB toggle required.

---

## Address Calculation

```
Register_Address = BASE_ADDR + Register_Offset

Where:
  BASE_ADDR       = RLB/UART base address (system-integration dependent)
  Register_Offset = value from the Register Summary table above

Only paddr[5:0] is decoded, so the block aliases every 0x40 bytes across
its address window.

Example (BASE_ADDR = 0xFEC08000):
  LSR = 0xFEC08000 + 0x18 = 0xFEC08018
```

---

**Back to:** [UART 16550 Specification Index](../uart_16550_index.md)
