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
| IER | 0x00 | Interrupts disabled |
| IIR | 0x01 | No pending interrupt |
| FCR | 0x00 | FIFOs disabled |
| LCR | 0x00 | 5N1 format |
| MCR | 0x00 | Outputs deasserted |
| LSR | 0x60 | TX empty |
| MSR | 0x00 | Inputs low |
| SCR | 0x00 | Cleared |
| DLL | 0x00 | Divisor = 0 |
| DLM | 0x00 | Divisor = 0 |

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

1. Set baud rate (DLL, DLM via DLAB)
2. Configure line format (LCR)
3. Enable FIFOs if desired (FCR)
4. Enable interrupts (IER)
5. Configure modem control (MCR)

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

- Disable unused interrupts (IER = 0)
- Use FIFO mode to reduce interrupt rate
- Use auto flow control (AFE) to prevent overflow

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
