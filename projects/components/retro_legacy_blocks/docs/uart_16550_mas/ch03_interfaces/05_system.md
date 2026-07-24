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

# APB UART 16550 - System Interface

## Clock Signals

### pclk - APB Clock

| Parameter | Value |
|-----------|-------|
| Purpose | APB interface and UART logic |
| Frequency | 50-200 MHz typical |
| Domain | All internal logic |

### Baud Rate Derivation

Baud rate is derived from pclk:
```
Baud Rate = pclk / (16 * Divisor)
```

## Reset Signals

### presetn - APB Reset

| Parameter | Value |
|-----------|-------|
| Polarity | Active low |
| Type | Asynchronous assert, synchronous deassert |
| Scope | All UART logic |

## Reset Behavior

### Register Reset Values

| Register | Reset | Notes |
|----------|-------|-------|
| RBR | Undefined | FIFO content |
| THR | N/A | Write-only |
| IER | 0x00 | Enable bits stored but unimplemented |
| IIR | 0x02 | THR-empty pending at reset |
| FCR | 0x00 | FIFO-enable interface bit clear |
| LCR | 0x03 | 8N1 format |
| MCR | 0x00 | Outputs deasserted (irq masked - OUT2=0) |
| LSR | 0x60 | TX empty |
| MSR | 0x00 | Inputs low |
| SCR | 0x00 | Cleared |
| DLL | 0x01 | Divisor LSB = 1 |
| DLM | 0x00 | Divisor MSB = 0 |

### Signal States During Reset

| Signal | Reset State |
|--------|-------------|
| txd | 1 (Mark/Idle) |
| rts_n | 1 (Deasserted) |
| dtr_n | 1 (Deasserted) |
| out1_n | 1 (Deasserted) |
| out2_n | 1 (Deasserted) |
| irq | 0 (No interrupt) |

### Post-Reset Initialization

1. Set baud rate (write DLL at 0x24, DLM at 0x28 directly - no DLAB toggle)
2. Configure line format (LCR at 0x10)
3. Enable FIFOs if desired (FCR at 0x0C)
4. Configure modem control (MCR at 0x14); set OUT2 to enable the irq pin
5. (IER at 0x04 is stored but does not enable/mask interrupts in this implementation)

## Reset Sequence

### Timing

```
          ________________________________________
pclk     |  |  |  |  |  |  |  |  |  |  |  |  |  |

                              _____________________
presetn  ____________________|

         |<-- Reset Active -->|<-- Normal Op ----->|
```

### Requirements

- Hold reset low for minimum 2 pclk cycles
- Allow 2 cycles after reset before first APB access
- Divisor must be programmed before operation

## Power Management

### Clock Gating

When idle (no TX/RX activity):
- Internal clocks can be gated
- APB interface remains responsive
- Wake on new data or register access

### Low Power Hints

- Use FIFO mode to reduce interrupt rate
- Set a higher RX trigger level to reduce interrupt frequency

(Note: IER masking and auto flow control are not implemented in this RTL.)

## External Connections

### Typical System

```
         +------------+
pclk --->|            |---> txd    ---> RS-232
presetn->|   UART     |<--- rxd    <--- Transceiver
         |   16550    |
APB <===>|            |<--> Modem signals
         |            |---> irq    ---> Interrupt
         +------------+      |          Controller
                             v
```

### Direct Connection (TTL)

For TTL-level serial:
- Connect txd/rxd directly to 3.3V/5V logic
- No level conversion needed
- Short cable runs recommended

---

**Back to:** [00_overview.md](00_overview.md) - Interfaces Overview

**Next Chapter:** [Chapter 4: Programming Model](../ch04_programming/00_overview.md)
