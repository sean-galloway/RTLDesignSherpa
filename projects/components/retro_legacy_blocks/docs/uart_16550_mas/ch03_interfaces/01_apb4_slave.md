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

Flat, DLAB-independent map (LCR[7] does not remap any address; DLL/DLM have dedicated offsets). Only `paddr[5:0]` is decoded, so the block aliases every 0x40 bytes across the window.

| Offset | Read | Write |
|--------|------|-------|
| 0x00 | RBR | THR |
| 0x04 | IER | IER |
| 0x08 | IIR | - |
| 0x0C | FCR | FCR |
| 0x10 | LCR | LCR |
| 0x14 | MCR | MCR |
| 0x18 | LSR | LSR (W1C error bits) |
| 0x1C | MSR | MSR (W1C delta bits) |
| 0x20 | SCR | SCR |
| 0x24 | DLL | DLL |
| 0x28 | DLM | DLM |

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
| IIR | None (reading IIR does not clear any interrupt) | N/A |
| FCR | None (FCR is readable) | Can reset FIFOs |
| LSR | None | Write 1 clears error bits [4:1] (W1C) |
| MSR | None | Write 1 clears delta bits [3:0] (W1C) |

Note: A standard 16550 clears LSR/MSR sticky bits on read; this implementation uses W1C writes instead. In the current RTL the core does not assert the internal clear strobes, so those bits and their interrupts persist until reset (known RTL issue).

## Timing

### Zero Wait State

All register accesses complete in minimum APB cycles:
- Read: 2 cycles (setup + access)
- Write: 2 cycles (setup + access)

---

**Next:** [02_serial.md](02_serial.md) - Serial Interface
