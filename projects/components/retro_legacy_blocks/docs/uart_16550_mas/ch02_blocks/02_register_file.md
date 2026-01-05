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

# APB UART 16550 - Register File Block

## Overview

The register file implements the standard 16550 register set with PeakRDL generation for APB interface compatibility.

## Block Diagram

![Register File Block](../assets/svg/uart_register_file.svg)

## Register Organization

### Address 0x00 (RBR/THR/DLL)

| DLAB | Read | Write |
|------|------|-------|
| 0 | RBR - Receiver Buffer | THR - Transmitter Holding |
| 1 | DLL - Divisor LSB | DLL - Divisor LSB |

### Address 0x04 (IER/DLM)

| DLAB | Read/Write |
|------|------------|
| 0 | IER - Interrupt Enable |
| 1 | DLM - Divisor MSB |

### Address 0x08 (IIR/FCR)

| Access | Register |
|--------|----------|
| Read | IIR - Interrupt Identification |
| Write | FCR - FIFO Control |

### Addresses 0x0C-0x1C

Fixed registers, not affected by DLAB:
- 0x0C: LCR - Line Control
- 0x10: MCR - Modem Control
- 0x14: LSR - Line Status (RO)
- 0x18: MSR - Modem Status (RO)
- 0x1C: SCR - Scratch

## Hardware Interface (HWIF)

### Software-to-Hardware (reg2hw)

| Signal | Description |
|--------|-------------|
| thr_data | Data to transmit |
| thr_we | THR write enable |
| ier | Interrupt enables |
| fcr | FIFO control |
| lcr | Line control |
| mcr | Modem control |
| dll | Divisor LSB |
| dlm | Divisor MSB |

### Hardware-to-Software (hw2reg)

| Signal | Description |
|--------|-------------|
| rbr_data | Received data |
| iir | Interrupt status |
| lsr | Line status |
| msr | Modem status |

## Register Access Types

| Type | Description |
|------|-------------|
| RO | Read-only, hardware updates |
| WO | Write-only, not readable |
| RW | Read-write |
| RC | Read to clear (some IIR bits) |

## Implementation Notes

- DLAB bit controls address 0x00/0x04 mapping
- THR write pushes to TX FIFO
- RBR read pops from RX FIFO
- IIR read can clear interrupt condition

---

**Next:** [03_tx_engine.md](03_tx_engine.md) - TX Engine
