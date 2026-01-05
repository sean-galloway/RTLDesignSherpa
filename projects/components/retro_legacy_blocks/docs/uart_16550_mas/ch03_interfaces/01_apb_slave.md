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

# APB UART 16550 - APB Slave Interface

## Signal Description

### APB Slave Signals

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| pclk | 1 | I | APB clock |
| presetn | 1 | I | APB reset (active low) |
| s_apb_psel | 1 | I | Peripheral select |
| s_apb_penable | 1 | I | Enable phase |
| s_apb_pwrite | 1 | I | Write transaction |
| s_apb_paddr | 12 | I | Address bus |
| s_apb_pwdata | 32 | I | Write data |
| s_apb_pstrb | 4 | I | Byte strobes |
| s_apb_prdata | 32 | O | Read data |
| s_apb_pready | 1 | O | Ready response |
| s_apb_pslverr | 1 | O | Slave error |

## Address Map

| Address | DLAB=0 Read | DLAB=0 Write | DLAB=1 R/W |
|---------|-------------|--------------|------------|
| 0x00 | RBR | THR | DLL |
| 0x04 | IER | IER | DLM |
| 0x08 | IIR | FCR | IIR/FCR |
| 0x0C | LCR | LCR | LCR |
| 0x10 | MCR | MCR | MCR |
| 0x14 | LSR | - | LSR |
| 0x18 | MSR | - | MSR |
| 0x1C | SCR | SCR | SCR |

## Protocol Compliance

### APB3/APB4 Features

| Feature | Support |
|---------|---------|
| PSEL | Yes |
| PENABLE | Yes |
| PWRITE | Yes |
| PADDR | 12-bit |
| PWDATA | 32-bit |
| PRDATA | 32-bit |
| PREADY | Yes (always 1) |
| PSLVERR | Yes (always 0) |
| PSTRB | Yes |

## Register Access

### Byte Access

32-bit APB with 8-bit registers:
- pstrb[0]: Access register at paddr
- Other strobes: No effect (registers are 8-bit)

### Side Effects

Some registers have read/write side effects:

| Register | Read Side Effect | Write Side Effect |
|----------|-----------------|-------------------|
| RBR | Pops RX FIFO | N/A |
| THR | N/A | Pushes TX FIFO |
| IIR | May clear THRE interrupt | N/A |
| FCR | N/A | Can reset FIFOs |
| LSR | Clears error bits | N/A |
| MSR | Clears delta bits | N/A |

## Timing

### Zero Wait State

All register accesses complete in minimum APB cycles:
- Read: 2 cycles (setup + access)
- Write: 2 cycles (setup + access)

---

**Next:** [02_serial.md](02_serial.md) - Serial Interface
