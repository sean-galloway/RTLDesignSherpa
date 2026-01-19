# APB Configuration Interface

## Overview

RAPIDS Beats uses an APB-like interface for configuration and descriptor kick-off. This interface allows software to:

1. Configure channel parameters
2. Initiate descriptor processing (kick-off)
3. Read status and error information

## Configuration Interface

### Signal List

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `apb_valid` | NC | input | Per-channel kick-off valid |
| `apb_ready` | NC | output | Per-channel ready |
| `apb_addr` | 64 | input | Descriptor address |
| `cfg_channel_enable` | NC | input | Per-channel enable |
| `cfg_addr0_base` | 64 | input | Address range 0 base |
| `cfg_addr0_limit` | 64 | input | Address range 0 limit |
| `cfg_addr1_base` | 64 | input | Address range 1 base |
| `cfg_addr1_limit` | 64 | input | Address range 1 limit |

: APB Configuration Signals (NC = NUM_CHANNELS)

### Descriptor Kick-Off

To start descriptor processing on a channel:

1. Write descriptor to memory
2. Assert `apb_valid[ch]` with descriptor address on `apb_addr`
3. Wait for `apb_ready[ch]` assertion
4. Deassert `apb_valid[ch]`

### Timing Diagram

![APB Kick-Off Timing](../assets/wavedrom/apb_kickoff_timing.svg)

**Source:** [apb_kickoff_timing.json](../assets/wavedrom/apb_kickoff_timing.json)

```wavedrom
{
  "signal": [
    {"name": "clk", "wave": "p........"},
    {},
    {"name": "apb_valid[0]", "wave": "0.1..0..."},
    {"name": "apb_ready[0]", "wave": "1....0.1."},
    {"name": "apb_addr", "wave": "x.=..x...", "data": ["DESC_ADDR"]},
    {},
    {"name": "channel_idle[0]", "wave": "1....0..."},
    {"name": "desc_fetch_start", "wave": "0...1.0.."}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Descriptor Kick-Off Sequence"}
}
```

## Status Interface

### Per-Channel Status Signals

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `channel_idle` | NC | output | Channel idle status |
| `channel_error` | NC | output | Channel error flag |
| `scheduler_state` | 4*NC | output | FSM state per channel |

: Status Signals

### Channel State Encoding

| State | Value | Description |
|-------|-------|-------------|
| IDLE | 4'h0 | Waiting for kick-off |
| WAIT_DESC | 4'h1 | Waiting for descriptor |
| PARSE_DESC | 4'h2 | Parsing descriptor |
| CH_XFER_DATA | 4'h3 | Transfer in progress |
| CHECK_NEXT | 4'h4 | Checking next descriptor |
| COMPLETE | 4'h5 | Transfer complete |
| ERROR | 4'hF | Error state |

: Scheduler State Encoding

## Configuration Registers

### Address Range Validation

RAPIDS validates descriptor addresses against configurable ranges:

```
Valid if:
  (addr >= cfg_addr0_base && addr < cfg_addr0_limit) ||
  (addr >= cfg_addr1_base && addr < cfg_addr1_limit)
```

### Configuration Parameters

| Register | Offset | Width | Description |
|----------|--------|-------|-------------|
| `CTRL` | 0x00 | 32 | Global control |
| `STATUS` | 0x04 | 32 | Global status |
| `CH_ENABLE` | 0x08 | 8 | Channel enable bitmap |
| `CH_STATUS` | 0x0C | 8 | Channel busy bitmap |
| `ADDR0_BASE` | 0x10 | 64 | Address range 0 base |
| `ADDR0_LIMIT` | 0x18 | 64 | Address range 0 limit |
| `ADDR1_BASE` | 0x20 | 64 | Address range 1 base |
| `ADDR1_LIMIT` | 0x28 | 64 | Address range 1 limit |
| `IRQ_ENABLE` | 0x30 | 8 | IRQ enable per channel |
| `IRQ_STATUS` | 0x34 | 8 | IRQ status per channel |

: Configuration Register Map

### Control Register (CTRL)

| Bit | Name | Description |
|-----|------|-------------|
| 0 | ENABLE | Global enable |
| 1 | SOFT_RESET | Soft reset (self-clearing) |
| 7:2 | Reserved | - |

: CTRL Register Bits

### Status Register (STATUS)

| Bit | Name | Description |
|-----|------|-------------|
| 0 | BUSY | Any channel busy |
| 1 | ERROR | Any channel error |
| 7:2 | Reserved | - |

: STATUS Register Bits

## Programming Sequence

### Initialization

```c
// 1. Assert soft reset
CTRL = 0x02;
while (CTRL & 0x02);  // Wait for reset complete

// 2. Configure address ranges
ADDR0_BASE = 0x80000000;
ADDR0_LIMIT = 0x90000000;

// 3. Enable desired channels
CH_ENABLE = 0xFF;  // Enable all 8 channels

// 4. Enable IRQs if needed
IRQ_ENABLE = 0xFF;

// 5. Global enable
CTRL = 0x01;
```

### Descriptor Kick-Off

```c
// Prepare descriptor in memory
desc->src_addr = src;
desc->dst_addr = dst;
desc->length = beats;
desc->last = 1;
desc->valid = 1;

// Kick off channel 0
apb_kickoff(0, desc_addr);

// Wait for completion
while (!(channel_idle & 0x01));

// Check for errors
if (channel_error & 0x01) {
    handle_error(0);
}
```
