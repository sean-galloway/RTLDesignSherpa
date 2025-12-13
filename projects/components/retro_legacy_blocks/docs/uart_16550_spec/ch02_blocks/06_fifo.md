# APB UART 16550 - FIFO Subsystem

## Overview

The UART includes 16-byte TX and RX FIFOs that buffer data between software and the serial interface.

## Block Diagram

![FIFO Block](../assets/svg/uart_fifo.svg)

## FIFO Configuration

### FCR (FIFO Control Register)

| Bit | Name | Description |
|-----|------|-------------|
| 0 | FE | FIFO Enable |
| 1 | RFR | RX FIFO Reset |
| 2 | TFR | TX FIFO Reset |
| 3 | DMS | DMA Mode Select |
| 5:4 | Reserved | |
| 7:6 | RTL | RX Trigger Level |

### Trigger Levels

| RTL[1:0] | RX FIFO Trigger |
|----------|-----------------|
| 00 | 1 byte |
| 01 | 4 bytes |
| 10 | 8 bytes |
| 11 | 14 bytes |

### FIFO Trigger Timing

The following diagram shows RX FIFO filling to the trigger threshold and generating an interrupt.

![UART FIFO Threshold](../assets/wavedrom/timing/uart_fifo_threshold.svg)

The interrupt sequence:
1. RX data arrives, `rx_fifo_wr` pulses
2. FIFO count increments with each byte
3. When count reaches trigger level (8 in example), `rx_trigger_match` asserts
4. RX Data Available interrupt (`rx_data_avail_int`) triggers
5. CPU reads RBR to retrieve data, decrementing FIFO count

## TX FIFO

### Characteristics

| Parameter | Value |
|-----------|-------|
| Depth | 16 bytes |
| Width | 8 bits |

### Operations

| Operation | Trigger |
|-----------|---------|
| Write | THR register write |
| Read | TX serializer ready |
| Reset | FCR.TFR write |

### Status

| Signal | LSR Bit | Condition |
|--------|---------|-----------|
| THRE | 5 | FIFO has space (not full) |
| TEMT | 6 | FIFO empty AND shift register empty |

## RX FIFO

### Characteristics

| Parameter | Value |
|-----------|-------|
| Depth | 16 entries |
| Width | 11 bits |

### Entry Format

```
[10] [9] [8] [7:0]
 BI  FE  PE  DATA
```

### Operations

| Operation | Trigger |
|-----------|---------|
| Write | RX deserializer complete |
| Read | RBR register read |
| Reset | FCR.RFR write |

### Status

| Signal | LSR Bit | Condition |
|--------|---------|-----------|
| DR | 0 | Data Ready (FIFO not empty) |
| OE | 1 | Overrun Error |
| PE | 2 | Parity Error (per character) |
| FE | 3 | Framing Error (per character) |
| BI | 4 | Break Indicator (per character) |
| FIFOERR | 7 | Error in FIFO (PE, FE, or BI) |

## FIFO vs Non-FIFO Mode

### FCR.FE = 0 (8250 Compatibility)

- FIFOs disabled
- Single-character buffering
- THR/RBR act as single registers
- IIR[7:6] = 00

### FCR.FE = 1 (16550 Mode)

- 16-byte FIFOs enabled
- Trigger level interrupts
- Character timeout interrupt
- IIR[7:6] = 11

## Error Handling

### Per-Character Errors

PE, FE, BI stored with each character in RX FIFO:
- Error appears in LSR when character read
- LSR[7] indicates any error in FIFO

### Overrun Error

OE set immediately when:
- RX FIFO full
- New character received
- New character discarded

## FIFO Reset

### TX FIFO Reset (FCR.TFR)

1. Write FCR with TFR=1
2. TX FIFO cleared immediately
3. Current transmission continues
4. THRE and TEMT updated

### RX FIFO Reset (FCR.RFR)

1. Write FCR with RFR=1
2. RX FIFO cleared immediately
3. Current reception continues
4. DR cleared, errors cleared

### Full Reset

```c
// Reset both FIFOs, enable with trigger=14
FCR = 0xC7;  // 11000111b
```

---

**Back to:** [00_overview.md](00_overview.md) - Block Descriptions Overview

**Next Chapter:** [Chapter 3: Interfaces](../ch03_interfaces/00_overview.md)
