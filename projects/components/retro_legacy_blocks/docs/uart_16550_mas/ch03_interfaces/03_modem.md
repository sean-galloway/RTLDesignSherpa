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

# APB UART 16550 - Modem Interface

## Signal Description

### Modem Control Outputs (Active Low)

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| rts_n | 1 | O | Request To Send |
| dtr_n | 1 | O | Data Terminal Ready |
| out1_n | 1 | O | User output 1 |
| out2_n | 1 | O | User output 2 |

### Modem Status Inputs (Active Low)

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| cts_n | 1 | I | Clear To Send |
| dsr_n | 1 | I | Data Set Ready |
| dcd_n | 1 | I | Data Carrier Detect |
| ri_n | 1 | I | Ring Indicator |

## Modem Control Register (MCR)

### Output Control

| Bit | Name | Signal | Active When |
|-----|------|--------|-------------|
| 0 | DTR | dtr_n | MCR[0] = 1 |
| 1 | RTS | rts_n | MCR[1] = 1 |
| 2 | OUT1 | out1_n | MCR[2] = 1 |
| 3 | OUT2 | out2_n | MCR[3] = 1 |
| 4 | LOOP | - | Loopback mode |
| 5 | AFE | - | Auto flow control |

### Auto Flow Control (AFE)

When MCR.AFE = 1:
- **RTS** automatically controlled by RX FIFO level
  - RTS asserted when FIFO has space
  - RTS deasserted when FIFO near full
- **CTS** controls TX operation
  - TX pauses when CTS deasserted
  - TX resumes when CTS asserted

## Modem Status Register (MSR)

### Current State (Read-Only)

| Bit | Name | Source | Meaning |
|-----|------|--------|---------|
| 4 | CTS | cts_n | Current CTS state |
| 5 | DSR | dsr_n | Current DSR state |
| 6 | RI | ri_n | Current RI state |
| 7 | DCD | dcd_n | Current DCD state |

### Delta Bits (Clear on Read)

| Bit | Name | Meaning |
|-----|------|---------|
| 0 | DCTS | CTS changed since last read |
| 1 | DDSR | DSR changed since last read |
| 2 | TERI | RI changed from low to high |
| 3 | DDCD | DCD changed since last read |

## Hardware Flow Control

### RTS/CTS Flow Control

```
TX Device                    RX Device
    |                            |
    |-------- TXD ------------->|
    |                            |
    |<------- CTS_N ------------|
    |                            |
    |-------- RTS_N ----------->|
    |                            |
    |<------- RXD --------------|
```

When AFE enabled:
1. Receiver asserts RTS when ready
2. Transmitter checks CTS before sending
3. If CTS deasserted, TX pauses after current byte

### Manual Flow Control

Without AFE, software controls RTS:
```c
// Ready to receive
MCR |= 0x02;   // Assert RTS

// Stop receiving
MCR &= ~0x02;  // Deassert RTS
```

## Loopback Mode

When MCR.LOOP = 1:
- TXD internally connected to RXD
- Modem outputs connected to inputs:
  - DTR -> DSR
  - RTS -> CTS
  - OUT1 -> RI
  - OUT2 -> DCD
- External signals disconnected

Used for:
- Self-test
- UART verification
- Driver testing

## Input Synchronization

All modem inputs pass through 2-stage synchronizer:
```
cts_n --> FF1 --> FF2 --> synced_cts_n
         (clk)   (clk)
```

### Modem Status Change Detection

The following diagram shows how modem input changes are detected and reported.

![UART Modem Status](../assets/wavedrom/timing/uart_modem_status.svg)

The detection sequence:
1. External CTS# falls (device ready to receive)
2. 2-stage synchronizer captures the change
3. Edge detector compares current vs. previous state
4. Delta flag (`r_delta_cts`) latched
5. Current state (`r_cts_state`) updated
6. MSR updated, modem status interrupt asserted

## Interrupt Generation

MSR delta bits can generate interrupt:
- IER[3] enables modem status interrupt
- Any delta bit set generates interrupt
- Reading MSR clears delta bits

---

**Next:** [04_interrupt.md](04_interrupt.md) - Interrupt Interface
