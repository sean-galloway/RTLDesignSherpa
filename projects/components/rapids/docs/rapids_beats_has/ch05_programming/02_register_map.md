# Register Map

## Overview

RAPIDS Beats provides a memory-mapped register interface for configuration and status. Registers are accessed via the APB interface and organized by function.

## Register Summary

### Global Registers (Offset 0x000-0x0FF)

| Offset | Name | Width | Access | Description |
|--------|------|-------|--------|-------------|
| 0x000 | `VERSION` | 32 | RO | IP version register |
| 0x004 | `CONFIG` | 32 | RO | Configuration parameters |
| 0x008 | `GLOBAL_CTRL` | 32 | RW | Global control |
| 0x00C | `GLOBAL_STATUS` | 32 | RO | Global status |
| 0x010 | `IRQ_STATUS` | 32 | RW1C | Interrupt status |
| 0x014 | `IRQ_ENABLE` | 32 | RW | Interrupt enable |
| 0x018 | `IRQ_FORCE` | 32 | WO | Force interrupt (debug) |

: Global Registers

### Per-Channel Registers (Offset 0x100 + ch*0x40)

| Offset | Name | Width | Access | Description |
|--------|------|-------|--------|-------------|
| +0x00 | `CH_CTRL` | 32 | RW | Channel control |
| +0x04 | `CH_STATUS` | 32 | RO | Channel status |
| +0x08 | `DESC_PTR_LO` | 32 | RW | Descriptor pointer [31:0] |
| +0x0C | `DESC_PTR_HI` | 32 | RW | Descriptor pointer [63:32] |
| +0x10 | `XFER_COUNT` | 32 | RO | Beats transferred |
| +0x14 | `ERR_STATUS` | 32 | RW1C | Error status |
| +0x18 | `CH_CONFIG` | 32 | RW | Channel configuration |

: Per-Channel Registers

## Register Descriptions

### VERSION (0x000) - Read Only

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31:24] | `major` | 0x01 | Major version |
| [23:16] | `minor` | 0x00 | Minor version |
| [15:0] | `patch` | 0x0000 | Patch level |

: VERSION Register

### CONFIG (0x004) - Read Only

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31:24] | `num_channels` | 0x08 | Number of channels |
| [23:16] | `data_width` | 0x40 | Data width / 8 (64 = 512-bit) |
| [15:8] | `sram_depth` | varies | SRAM depth / 16 |
| [7:0] | `features` | varies | Feature bits |

: CONFIG Register

### GLOBAL_CTRL (0x008) - Read/Write

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31] | `soft_reset` | 0 | Write 1 to reset all channels |
| [30:8] | Reserved | 0 | Reserved |
| [7:0] | `clock_gate_en` | 0xFF | Per-channel clock gate enable |

: GLOBAL_CTRL Register

### GLOBAL_STATUS (0x00C) - Read Only

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31:24] | Reserved | 0 | Reserved |
| [23:16] | `error_channels` | 0 | Channels with errors |
| [15:8] | `active_channels` | 0 | Channels in transfer |
| [7:0] | `idle_channels` | 0xFF | Channels idle |

: GLOBAL_STATUS Register

### IRQ_STATUS (0x010) - Read/Write-1-to-Clear

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31:24] | `ch_error` | 0 | Channel error interrupts |
| [23:16] | Reserved | 0 | Reserved |
| [15:8] | `ch_complete` | 0 | Channel completion interrupts |
| [7:0] | Reserved | 0 | Reserved |

: IRQ_STATUS Register

### CH_CTRL (0x100 + ch*0x40) - Read/Write

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31] | `enable` | 0 | Channel enable |
| [30] | `kick` | 0 | Write 1 to start (self-clearing) |
| [29] | `abort` | 0 | Write 1 to abort (self-clearing) |
| [28] | `soft_reset` | 0 | Write 1 to reset channel |
| [27:0] | Reserved | 0 | Reserved |

: CH_CTRL Register

### CH_STATUS (0x104 + ch*0x40) - Read Only

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31:28] | `state` | 0 | FSM state encoding |
| [27:24] | Reserved | 0 | Reserved |
| [23:16] | `desc_count` | 0 | Descriptors processed |
| [15:8] | `sram_level` | 0 | Current SRAM fill level |
| [7:0] | `flags` | 0 | Status flags |

: CH_STATUS Register

**State Encoding:**

| Value | State |
|-------|-------|
| 0x0 | IDLE |
| 0x1 | WAIT_DESC |
| 0x2 | PARSE_DESC |
| 0x3 | XFER_DATA |
| 0x4 | CHECK_NEXT |
| 0x5 | COMPLETE |
| 0xE | ERROR |
| 0xF | RESET |

: CH_STATUS State Encoding

### ERR_STATUS (0x114 + ch*0x40) - Read/Write-1-to-Clear

| Bits | Field | Reset | Description |
|------|-------|-------|-------------|
| [31:28] | `axi_resp` | 0 | AXI error response code |
| [27:24] | `error_type` | 0 | Error type encoding |
| [23:16] | `error_desc_idx` | 0 | Descriptor index at error |
| [15:0] | Reserved | 0 | Reserved |

: ERR_STATUS Register

## Register Access Timing

![Register Read](../assets/wavedrom/register_read.svg)

**Source:** [register_read.json](../assets/wavedrom/register_read.json)

```wavedrom
{
  "signal": [
    {"name": "pclk", "wave": "p........"},
    {},
    {"name": "psel", "wave": "01....0.."},
    {"name": "penable", "wave": "0.1...0.."},
    {"name": "pwrite", "wave": "0........"},
    {"name": "paddr", "wave": "x=....x..", "data": ["0x104"]},
    {},
    {"name": "pready", "wave": "0..1..0.."},
    {"name": "prdata", "wave": "x..=..x..", "data": ["STATUS"]},
    {"name": "pslverr", "wave": "0........"}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "APB Register Read (CH0 Status)"}
}
```

![Register Write](../assets/wavedrom/register_write.svg)

**Source:** [register_write.json](../assets/wavedrom/register_write.json)

```wavedrom
{
  "signal": [
    {"name": "pclk", "wave": "p........"},
    {},
    {"name": "psel", "wave": "01....0.."},
    {"name": "penable", "wave": "0.1...0.."},
    {"name": "pwrite", "wave": "01....0.."},
    {"name": "paddr", "wave": "x=....x..", "data": ["0x100"]},
    {"name": "pwdata", "wave": "x=....x..", "data": ["0x8000_0000"]},
    {},
    {"name": "pready", "wave": "0..1..0.."},
    {"name": "pslverr", "wave": "0........"},
    {},
    {"name": "ch0_enable", "wave": "0....1..."}
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "APB Register Write (CH0 Enable)"}
}
```

## Channel Kick Sequence

Writing to the `kick` bit triggers descriptor processing:

```wavedrom
{
  "signal": [
    {"name": "pclk", "wave": "p............"},
    {},
    ["APB Write",
      {"name": "psel", "wave": "01...0......."},
      {"name": "penable", "wave": "0.1..0......."},
      {"name": "paddr", "wave": "x=...x.......", "data": ["0x100"]},
      {"name": "pwdata", "wave": "x=...x.......", "data": ["KICK"]}
    ],
    {},
    ["Channel Response",
      {"name": "kick_valid", "wave": "0...1.0......"},
      {"name": "ch_state", "wave": "=....=.......", "data": ["IDLE","WAIT_DESC"]},
      {"name": "desc_fetch", "wave": "0....1.0....."}
    ]
  ],
  "config": {"hscale": 1.5},
  "head": {"text": "Channel Kick Sequence"}
}
```

## Address Decoding

### Address Space Layout

```
0x000 - 0x0FF: Global registers
0x100 - 0x13F: Channel 0 registers
0x140 - 0x17F: Channel 1 registers
0x180 - 0x1BF: Channel 2 registers
0x1C0 - 0x1FF: Channel 3 registers
0x200 - 0x23F: Channel 4 registers
0x240 - 0x27F: Channel 5 registers
0x280 - 0x2BF: Channel 6 registers
0x2C0 - 0x2FF: Channel 7 registers
0x300 - 0x3FF: Reserved
```

### Channel Address Formula

```
channel_base = 0x100 + (channel_number * 0x40)
register_addr = channel_base + register_offset
```

Example: Channel 3 CH_STATUS = 0x100 + (3 * 0x40) + 0x04 = 0x1C4

