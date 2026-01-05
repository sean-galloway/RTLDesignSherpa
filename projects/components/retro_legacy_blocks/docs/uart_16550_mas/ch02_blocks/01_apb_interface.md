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

# APB UART 16550 - APB Interface Block

## Overview

The APB interface provides the connection between the system APB bus and the UART register file.

## Block Diagram

### Figure 2.1: APB Interface Block

![APB Interface Block](../assets/svg/uart_apb_interface.svg)

## Interface Signals

### APB Slave Interface

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| s_apb_psel | 1 | Input | Slave select |
| s_apb_penable | 1 | Input | Enable phase |
| s_apb_pwrite | 1 | Input | Write operation |
| s_apb_paddr | 12 | Input | Address bus |
| s_apb_pwdata | 32 | Input | Write data |
| s_apb_pstrb | 4 | Input | Byte strobes |
| s_apb_prdata | 32 | Output | Read data |
| s_apb_pready | 1 | Output | Ready response |
| s_apb_pslverr | 1 | Output | Error response |

## Address Decoding

### UART Register Addresses

| Address | DLAB=0 Read | DLAB=0 Write | DLAB=1 |
|---------|-------------|--------------|--------|
| 0x00 | RBR | THR | DLL |
| 0x04 | IER | IER | DLM |
| 0x08 | IIR | FCR | IIR/FCR |
| 0x0C | LCR | LCR | LCR |
| 0x10 | MCR | MCR | MCR |
| 0x14 | LSR | - | LSR |
| 0x18 | MSR | - | MSR |
| 0x1C | SCR | SCR | SCR |

### DLAB (Divisor Latch Access Bit)

LCR[7] controls access to divisor latches:
- DLAB=0: Normal register access
- DLAB=1: DLL/DLM accessible at addresses 0x00/0x04

## Operation

### Read Transaction
1. Master asserts `psel` and `paddr`
2. Master asserts `penable` on next cycle
3. Slave returns `prdata` with `pready`
4. Some registers have side effects on read (IIR, RBR)

### Write Transaction
1. Master asserts `psel`, `paddr`, `pwdata`, `pwrite`
2. Master asserts `penable` on next cycle
3. Slave samples data with `pready`
4. Write-only registers (THR, FCR) processed

## Implementation Notes

- Zero wait-state operation for all registers
- 32-bit data width with 8-bit register access
- Byte strobes select which byte to access
- Read-only registers ignore writes

---

**Next:** [02_register_file.md](02_register_file.md) - Register File
