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

# STREAM Register Map

## Overview

The STREAM DMA engine register interface consists of two distinct regions:

1. **Channel Kick-off Registers** (0x000 - 0x03F) - Direct routing to descriptor engines
2. **Configuration and Status Registers** (0x100 - 0xFFF) - PeakRDL-generated register file

## Address Space Layout

```
Base Address (configurable parameter)
│
├─ 0x000 - 0x03F: Channel Kick-off (apbtodescr.sv routing)
│  ├─ 0x000: CH0_CTRL_LOW  - Channel 0 descriptor address [31:0]
│  ├─ 0x004: CH0_CTRL_HIGH - Channel 0 descriptor address [63:32]
│  ├─ 0x008: CH1_CTRL_LOW  - Channel 1 descriptor address [31:0]
│  ├─ 0x00C: CH1_CTRL_HIGH - Channel 1 descriptor address [63:32]
│  ├─ 0x010: CH2_CTRL_LOW  - Channel 2 descriptor address [31:0]
│  ├─ 0x014: CH2_CTRL_HIGH - Channel 2 descriptor address [63:32]
│  ├─ 0x018: CH3_CTRL_LOW  - Channel 3 descriptor address [31:0]
│  ├─ 0x01C: CH3_CTRL_HIGH - Channel 3 descriptor address [63:32]
│  ├─ 0x020: CH4_CTRL_LOW  - Channel 4 descriptor address [31:0]
│  ├─ 0x024: CH4_CTRL_HIGH - Channel 4 descriptor address [63:32]
│  ├─ 0x028: CH5_CTRL_LOW  - Channel 5 descriptor address [31:0]
│  ├─ 0x02C: CH5_CTRL_HIGH - Channel 5 descriptor address [63:32]
│  ├─ 0x030: CH6_CTRL_LOW  - Channel 6 descriptor address [31:0]
│  ├─ 0x034: CH6_CTRL_HIGH - Channel 6 descriptor address [63:32]
│  ├─ 0x038: CH7_CTRL_LOW  - Channel 7 descriptor address [31:0]
│  └─ 0x03C: CH7_CTRL_HIGH - Channel 7 descriptor address [63:32]
│
├─ 0x040 - 0x0FF: Reserved
│
└─ 0x100 - 0x3FF: Configuration and Status Registers
   ├─ 0x100 - 0x11F: Global Control and Status
   ├─ 0x120 - 0x13F: Per-Channel Control
   ├─ 0x140 - 0x16F: Per-Channel Status
   ├─ 0x170 - 0x17F: Engine Completion and Error Status
   ├─ 0x180 - 0x1FF: Monitor FIFO Status
   ├─ 0x200 - 0x21F: Scheduler Configuration
   ├─ 0x220 - 0x23F: Descriptor Engine Configuration
   ├─ 0x240 - 0x25F: Descriptor AXI Monitor Configuration
   ├─ 0x260 - 0x27F: Read Engine AXI Monitor Configuration
   ├─ 0x280 - 0x29F: Write Engine AXI Monitor Configuration
   ├─ 0x2A0 - 0x2AF: AXI Transfer Configuration
   └─ 0x2B0 - 0x2BF: Performance Profiler Configuration
```

## Register Details

### Channel Kick-off Registers (0x000 - 0x03F)

These registers are **NOT** traditional registers. Writes are routed directly to descriptor engine APB ports via `apbtodescr.sv`.

**Note:** Descriptor addresses are 64-bit (ADDR_WIDTH parameter, default 64). On 32-bit APB bus, each channel requires TWO registers (LOW/HIGH).

| Offset | Register       | Type | Reset | Description                                    |
|--------|----------------|------|-------|------------------------------------------------|
| 0x000  | CH0_CTRL_LOW   | WO   | N/A   | Channel 0 descriptor address [31:0]            |
| 0x004  | CH0_CTRL_HIGH  | WO   | N/A   | Channel 0 descriptor address [63:32]           |
| 0x008  | CH1_CTRL_LOW   | WO   | N/A   | Channel 1 descriptor address [31:0]            |
| 0x00C  | CH1_CTRL_HIGH  | WO   | N/A   | Channel 1 descriptor address [63:32]           |
| 0x010  | CH2_CTRL_LOW   | WO   | N/A   | Channel 2 descriptor address [31:0]            |
| 0x014  | CH2_CTRL_HIGH  | WO   | N/A   | Channel 2 descriptor address [63:32]           |
| 0x018  | CH3_CTRL_LOW   | WO   | N/A   | Channel 3 descriptor address [31:0]            |
| 0x01C  | CH3_CTRL_HIGH  | WO   | N/A   | Channel 3 descriptor address [63:32]           |
| 0x020  | CH4_CTRL_LOW   | WO   | N/A   | Channel 4 descriptor address [31:0]            |
| 0x024  | CH4_CTRL_HIGH  | WO   | N/A   | Channel 4 descriptor address [63:32]           |
| 0x028  | CH5_CTRL_LOW   | WO   | N/A   | Channel 5 descriptor address [31:0]            |
| 0x02C  | CH5_CTRL_HIGH  | WO   | N/A   | Channel 5 descriptor address [63:32]           |
| 0x030  | CH6_CTRL_LOW   | WO   | N/A   | Channel 6 descriptor address [31:0]            |
| 0x034  | CH6_CTRL_HIGH  | WO   | N/A   | Channel 6 descriptor address [63:32]           |
| 0x038  | CH7_CTRL_LOW   | WO   | N/A   | Channel 7 descriptor address [31:0]            |
| 0x03C  | CH7_CTRL_HIGH  | WO   | N/A   | Channel 7 descriptor address [63:32]           |

: Channel Kick-off Registers

**Write Behavior:**
- Descriptor address is 64-bit, split across LOW and HIGH registers
- Write to HIGH register triggers descriptor engine kick-off
- LOW register write is buffered, HIGH register write initiates transfer
- Both registers must be written in order (LOW then HIGH)
- Write blocks until descriptor engine accepts (back-pressure)
- Read not supported (returns error)

**Example:**
```c
// Start DMA transfer on channel 0
// Descriptor at physical address 0x0000_0001_8000_0000 (64-bit)

// Write lower 32 bits first (buffered)
write32(BASE + CH0_CTRL_LOW, 0x8000_0000);

// Write upper 32 bits second (triggers kick-off)
write32(BASE + CH0_CTRL_HIGH, 0x0000_0001);  // Blocks until accepted

// For descriptors in lower 4GB (typical case):
write32(BASE + CH0_CTRL_LOW, 0x8000_0000);
write32(BASE + CH0_CTRL_HIGH, 0x0000_0000);  // Upper 32 bits = 0
```

---

### Global Control and Status (0x100 - 0x11F)

#### GLOBAL_CTRL (0x100)

Master control register for entire STREAM engine.

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:2  | Reserved    | RO   | 0x0   | Reserved                                 |
| 1     | GLOBAL_RST  | RW   | 0     | Global reset (self-clearing)             |
| 0     | GLOBAL_EN   | RW   | 0     | Global enable (1=enabled, 0=disabled)    |

: GLOBAL_CTRL

**Usage:**
```c
// Enable STREAM engine
write32(BASE + GLOBAL_CTRL, 0x1);

// Reset all channels
write32(BASE + GLOBAL_CTRL, 0x3);  // Set both EN and RST
// RST self-clears after one cycle
```

#### GLOBAL_STATUS (0x104)

Overall system status.

| Bits  | Field         | Type | Description                              |
|-------|---------------|------|------------------------------------------|
| 31:1  | Reserved      | RO   | Reserved                                 |
| 0     | SYSTEM_IDLE   | RO   | System idle (all channels idle)          |

: GLOBAL_STATUS

#### VERSION (0x108)

Version and configuration information (read-only).

| Bits   | Field         | Type | Value | Description                        |
|--------|---------------|------|-------|------------------------------------|
| 31:24  | Reserved      | RO   | 0x00  | Reserved                           |
| 23:16  | NUM_CHANNELS  | RO   | 0x08  | Number of channels (8)             |
| 15:8   | MAJOR         | RO   | 0x00  | Major version (0)                  |
| 7:0    | MINOR         | RO   | 0x5A  | Minor version (90 decimal = 0.90)  |

: VERSION

---

### Per-Channel Control and Status (0x120 - 0x17F)

#### CHANNEL_ENABLE (0x120)

Per-channel enable control (bit vector).

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:8  | Reserved    | RO   | 0x0   | Reserved                                 |
| 7:0   | CH_EN       | RW   | 0x00  | Channel enable [7:0] (1=enabled)         |

: CHANNEL_ENABLE

**Usage:**
```c
// Enable channels 0, 1, 2
write32(BASE + CHANNEL_ENABLE, 0x07);

// Disable channel 1, keep others
uint32_t val = read32(BASE + CHANNEL_ENABLE);
val &= ~(1 << 1);  // Clear bit 1
write32(BASE + CHANNEL_ENABLE, val);
```

#### CHANNEL_RESET (0x124)

Per-channel reset control (bit vector, self-clearing).

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:8  | Reserved    | RO   | 0x0   | Reserved                                 |
| 7:0   | CH_RST      | RW   | 0x00  | Channel reset [7:0] (write 1 to reset)   |

: CHANNEL_RESET

**Usage:**
```c
// Reset channels 0 and 3
write32(BASE + CHANNEL_RESET, 0x09);  // Bits 0 and 3
// Self-clears after reset completes
```

#### CHANNEL_IDLE (0x140)

Per-channel idle status (bit vector, read-only).

| Bits  | Field       | Type | Description                              |
|-------|-------------|------|------------------------------------------|
| 31:8  | Reserved    | RO   | Reserved                                 |
| 7:0   | CH_IDLE     | RO   | Channel idle [7:0] (1=idle, 0=active)    |

: CHANNEL_IDLE

#### DESC_ENGINE_IDLE (0x144)

Per-channel descriptor engine idle status.

| Bits  | Field       | Type | Description                                     |
|-------|-------------|------|-------------------------------------------------|
| 31:8  | Reserved    | RO   | Reserved                                        |
| 7:0   | DESC_IDLE   | RO   | Descriptor engine idle [7:0] (1=idle, 0=active) |

: DESC_ENGINE_IDLE

#### SCHEDULER_IDLE (0x148)

Per-channel scheduler idle status.

| Bits  | Field       | Type | Description                                   |
|-------|-------------|------|-----------------------------------------------|
| 31:8  | Reserved    | RO   | Reserved                                      |
| 7:0   | SCHED_IDLE  | RO   | Scheduler idle [7:0] (1=idle, 0=active)       |

: SCHEDULER_IDLE

#### CH_STATE[0..7] (0x150 - 0x16C)

Per-channel scheduler FSM state (8 registers, stride 0x4).

| Offset | Register   | Bits  | Field    | Type | Description                    |
|--------|------------|-------|----------|------|--------------------------------|
| 0x150  | CH0_STATE  | 31:7  | Reserved | RO   | Reserved                       |
|        |            | 6:0   | STATE    | RO   | Channel 0 scheduler state (one-hot) |
| 0x154  | CH1_STATE  | 6:0   | STATE    | RO   | Channel 1 scheduler state (one-hot) |
| 0x158  | CH2_STATE  | 6:0   | STATE    | RO   | Channel 2 scheduler state (one-hot) |
| 0x15C  | CH3_STATE  | 6:0   | STATE    | RO   | Channel 3 scheduler state (one-hot) |
| 0x160  | CH4_STATE  | 6:0   | STATE    | RO   | Channel 4 scheduler state (one-hot) |
| 0x164  | CH5_STATE  | 6:0   | STATE    | RO   | Channel 5 scheduler state (one-hot) |
| 0x168  | CH6_STATE  | 6:0   | STATE    | RO   | Channel 6 scheduler state (one-hot) |
| 0x16C  | CH7_STATE  | 6:0   | STATE    | RO   | Channel 7 scheduler state (one-hot) |

: CH_STATE[0..7]

**State Encoding (One-Hot):**
```
Bit 0 (0x01) = CH_IDLE         - Channel idle, waiting for descriptor
Bit 1 (0x02) = CH_FETCH_DESC   - Fetching descriptor from memory
Bit 2 (0x04) = CH_XFER_DATA    - Concurrent read AND write transfer
Bit 3 (0x08) = CH_COMPLETE     - Transfer complete
Bit 4 (0x10) = CH_NEXT_DESC    - Fetching next chained descriptor
Bit 5 (0x20) = CH_ERROR        - Error state
Bit 6 (0x40) = CH_RESERVED     - Reserved for future use
```

**Note:** Only ONE bit should be set at a time (one-hot encoding). Multiple bits set indicates a logic error.

---

### Engine Completion and Error Status (0x170 - 0x17F)

#### SCHED_ERROR (0x170)

Per-channel scheduler error flags.

| Bits  | Field      | Type | Description                                     |
|-------|------------|------|-------------------------------------------------|
| 31:8  | Reserved   | RO   | Reserved                                        |
| 7:0   | SCHED_ERR  | RO   | Scheduler error bits [7:0] (1=error, 0=no error) |

: SCHED_ERROR

#### AXI_RD_COMPLETE (0x174)

Per-channel AXI read engine completion status.

| Bits  | Field       | Type | Description                                        |
|-------|-------------|------|----------------------------------------------------|
| 31:8  | Reserved    | RO   | Reserved                                           |
| 7:0   | RD_COMPLETE | RO   | Read completion bits [7:0] (1=complete, 0=pending) |

: AXI_RD_COMPLETE

#### AXI_WR_COMPLETE (0x178)

Per-channel AXI write engine completion status.

| Bits  | Field       | Type | Description                                         |
|-------|-------------|------|-----------------------------------------------------|
| 31:8  | Reserved    | RO   | Reserved                                            |
| 7:0   | WR_COMPLETE | RO   | Write completion bits [7:0] (1=complete, 0=pending) |

: AXI_WR_COMPLETE

---

### Monitor FIFO Status (0x180 - 0x1FF)

These registers are active when `USE_AXI_MONITORS=1`.

#### MON_FIFO_STATUS (0x180)

Monitor bus FIFO status indicators.

| Bits  | Field          | Type | Description                           |
|-------|----------------|------|---------------------------------------|
| 31:4  | Reserved       | RO   | Reserved                              |
| 3     | MON_FIFO_UNFL  | RO   | FIFO underflow detected (1=error)     |
| 2     | MON_FIFO_OVFL  | RO   | FIFO overflow detected (1=error)      |
| 1     | MON_FIFO_EMPTY | RO   | FIFO empty (1=empty, 0=data available)|
| 0     | MON_FIFO_FULL  | RO   | FIFO full (1=full, 0=space available) |

: MON_FIFO_STATUS

#### MON_FIFO_COUNT (0x184)

Monitor bus FIFO entry count.

| Bits   | Field      | Type | Description                        |
|--------|------------|------|------------------------------------|
| 31:16  | Reserved   | RO   | Reserved                           |
| 15:0   | FIFO_COUNT | RO   | Number of entries in FIFO [15:0]   |

: MON_FIFO_COUNT

---

### Scheduler Configuration (0x200 - 0x21F)

#### SCHED_TIMEOUT_CYCLES (0x200)

Timeout threshold for scheduler (global for all channels).

| Bits   | Field           | Type | Reset | Description                          |
|--------|-----------------|------|-------|--------------------------------------|
| 31:16  | Reserved        | RO   | 0x0   | Reserved                             |
| 15:0   | TIMEOUT_CYCLES  | RW   | 1000  | Timeout in clock cycles              |

: SCHED_TIMEOUT_CYCLES

#### SCHED_CONFIG (0x204)

Scheduler feature enables (global for all channels).

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:5  | Reserved    | RO   | 0x0   | Reserved                                 |
| 4     | PERF_EN     | RW   | 0     | Performance monitoring enable            |
| 3     | COMPL_EN    | RW   | 1     | Completion reporting enable              |
| 2     | ERR_EN      | RW   | 1     | Error reporting enable                   |
| 1     | TIMEOUT_EN  | RW   | 1     | Timeout detection enable                 |
| 0     | SCHED_EN    | RW   | 1     | Scheduler enable                         |

: SCHED_CONFIG

---

### Descriptor Engine Configuration (0x220 - 0x23F)

#### DESCENG_CONFIG (0x220)

Descriptor engine feature enables (global for all channels).

| Bits  | Field         | Type | Reset | Description                              |
|-------|---------------|------|-------|------------------------------------------|
| 31:6  | Reserved      | RO   | 0x0   | Reserved                                 |
| 5:2   | FIFO_THRESH   | RW   | 0x8   | Prefetch FIFO threshold (4 bits)         |
| 1     | PREFETCH_EN   | RW   | 0     | Prefetch enable                          |
| 0     | DESCENG_EN    | RW   | 1     | Descriptor engine enable                 |

: DESCENG_CONFIG

#### DESCENG_ADDR0_BASE (0x224)

Base address for descriptor address range 0 (lower 32 bits).

| Bits   | Field       | Type | Reset      | Description                          |
|--------|-------------|------|------------|--------------------------------------|
| 31:0   | ADDR0_BASE  | RW   | 0x00000000 | Address range 0 base                 |

: DESCENG_ADDR0_BASE

#### DESCENG_ADDR0_LIMIT (0x228)

Limit address for descriptor address range 0 (lower 32 bits).

| Bits   | Field        | Type | Reset      | Description                          |
|--------|--------------|------|------------|--------------------------------------|
| 31:0   | ADDR0_LIMIT  | RW   | 0xFFFFFFFF | Address range 0 limit                |

: DESCENG_ADDR0_LIMIT

#### DESCENG_ADDR1_BASE (0x22C)

Base address for descriptor address range 1 (lower 32 bits).

| Bits   | Field       | Type | Reset      | Description                          |
|--------|-------------|------|------------|--------------------------------------|
| 31:0   | ADDR1_BASE  | RW   | 0x00000000 | Address range 1 base                 |

: DESCENG_ADDR1_BASE

#### DESCENG_ADDR1_LIMIT (0x230)

Limit address for descriptor address range 1 (lower 32 bits).

| Bits   | Field        | Type | Reset      | Description                          |
|--------|--------------|------|------------|--------------------------------------|
| 31:0   | ADDR1_LIMIT  | RW   | 0xFFFFFFFF | Address range 1 limit                |

: DESCENG_ADDR1_LIMIT

---

### Descriptor AXI Monitor Configuration (0x240 - 0x25F)

#### DAXMON_ENABLE (0x240)

Descriptor AXI master monitor enable controls.

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:5  | Reserved    | RO   | 0x0   | Reserved                                 |
| 4     | PERF_EN     | RW   | 0     | Performance packet enable                |
| 3     | TIMEOUT_EN  | RW   | 1     | Timeout detection enable                 |
| 2     | COMPL_EN    | RW   | 0     | Completion packet enable                 |
| 1     | ERR_EN      | RW   | 1     | Error detection enable                   |
| 0     | MON_EN      | RW   | 1     | Master enable for descriptor monitor     |

: DAXMON_ENABLE

#### DAXMON_TIMEOUT (0x244)

Descriptor AXI monitor timeout threshold.

| Bits   | Field           | Type | Reset  | Description                          |
|--------|-----------------|------|--------|--------------------------------------|
| 31:0   | TIMEOUT_CYCLES  | RW   | 10000  | Timeout in clock cycles              |

: DAXMON_TIMEOUT

#### DAXMON_LATENCY_THRESH (0x248)

Descriptor AXI monitor latency threshold.

| Bits   | Field          | Type | Reset | Description                           |
|--------|----------------|------|-------|---------------------------------------|
| 31:0   | LATENCY_THRESH | RW   | 5000  | Latency threshold in clock cycles     |

: DAXMON_LATENCY_THRESH

#### DAXMON_PKT_MASK (0x24C)

Descriptor AXI monitor packet type filtering.

| Bits   | Field     | Type | Reset  | Description                              |
|--------|-----------|------|--------|------------------------------------------|
| 31:16  | Reserved  | RO   | 0x0    | Reserved                                 |
| 15:0   | PKT_MASK  | RW   | 0xFFFF | Packet type mask (1=enable, 0=disable)   |

: DAXMON_PKT_MASK

#### DAXMON_ERR_CFG (0x250)

Descriptor AXI monitor error selection and filtering.

| Bits   | Field      | Type | Reset | Description                              |
|--------|------------|------|-------|------------------------------------------|
| 31:16  | Reserved   | RO   | 0x0   | Reserved                                 |
| 15:8   | ERR_MASK   | RW   | 0xFF  | Error type filtering mask                |
| 7:4    | Reserved   | RO   | 0x0   | Reserved                                 |
| 3:0    | ERR_SELECT | RW   | 0x0   | Error type selection                     |

: DAXMON_ERR_CFG

#### DAXMON_MASK1 (0x254)

Descriptor AXI monitor timeout and completion masks.

| Bits   | Field        | Type | Reset | Description                    |
|--------|--------------|------|-------|--------------------------------|
| 31:16  | Reserved     | RO   | 0x0   | Reserved                       |
| 15:8   | COMPL_MASK   | RW   | 0x00  | Completion mask                |
| 7:0    | TIMEOUT_MASK | RW   | 0xFF  | Timeout mask                   |

: DAXMON_MASK1

#### DAXMON_MASK2 (0x258)

Descriptor AXI monitor threshold and performance masks.

| Bits   | Field       | Type | Reset | Description                    |
|--------|-------------|------|-------|--------------------------------|
| 31:16  | Reserved    | RO   | 0x0   | Reserved                       |
| 15:8   | PERF_MASK   | RW   | 0x00  | Performance mask               |
| 7:0    | THRESH_MASK | RW   | 0xFF  | Threshold mask                 |

: DAXMON_MASK2

#### DAXMON_MASK3 (0x25C)

Descriptor AXI monitor address and debug masks.

| Bits   | Field      | Type | Reset | Description                    |
|--------|------------|------|-------|--------------------------------|
| 31:16  | Reserved   | RO   | 0x0   | Reserved                       |
| 15:8   | DEBUG_MASK | RW   | 0x00  | Debug mask                     |
| 7:0    | ADDR_MASK  | RW   | 0xFF  | Address mask                   |

: DAXMON_MASK3

---

### Read Engine AXI Monitor Configuration (0x260 - 0x27F)

#### RDMON_ENABLE (0x260)

Read engine AXI master monitor enable controls.

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:5  | Reserved    | RO   | 0x0   | Reserved                                 |
| 4     | PERF_EN     | RW   | 0     | Performance packet enable                |
| 3     | TIMEOUT_EN  | RW   | 1     | Timeout detection enable                 |
| 2     | COMPL_EN    | RW   | 0     | Completion packet enable                 |
| 1     | ERR_EN      | RW   | 1     | Error detection enable                   |
| 0     | MON_EN      | RW   | 1     | Master enable for read monitor           |

: RDMON_ENABLE

#### RDMON_TIMEOUT (0x264)

Read engine AXI monitor timeout threshold.

| Bits   | Field           | Type | Reset  | Description                          |
|--------|-----------------|------|--------|--------------------------------------|
| 31:0   | TIMEOUT_CYCLES  | RW   | 10000  | Timeout in clock cycles              |

: RDMON_TIMEOUT

#### RDMON_LATENCY_THRESH (0x268)

Read engine AXI monitor latency threshold.

| Bits   | Field          | Type | Reset | Description                           |
|--------|----------------|------|-------|---------------------------------------|
| 31:0   | LATENCY_THRESH | RW   | 5000  | Latency threshold in clock cycles     |

: RDMON_LATENCY_THRESH

#### RDMON_PKT_MASK (0x26C)

Read engine AXI monitor packet type filtering.

| Bits   | Field     | Type | Reset  | Description                              |
|--------|-----------|------|--------|------------------------------------------|
| 31:16  | Reserved  | RO   | 0x0    | Reserved                                 |
| 15:0   | PKT_MASK  | RW   | 0xFFFF | Packet type mask (1=enable, 0=disable)   |

: RDMON_PKT_MASK

#### RDMON_ERR_CFG (0x270)

Read engine AXI monitor error selection and filtering.

| Bits   | Field      | Type | Reset | Description                              |
|--------|------------|------|-------|------------------------------------------|
| 31:16  | Reserved   | RO   | 0x0   | Reserved                                 |
| 15:8   | ERR_MASK   | RW   | 0xFF  | Error type filtering mask                |
| 7:4    | Reserved   | RO   | 0x0   | Reserved                                 |
| 3:0    | ERR_SELECT | RW   | 0x0   | Error type selection                     |

: RDMON_ERR_CFG

#### RDMON_MASK1 (0x274)

Read engine AXI monitor timeout and completion masks.

| Bits   | Field        | Type | Reset | Description                    |
|--------|--------------|------|-------|--------------------------------|
| 31:16  | Reserved     | RO   | 0x0   | Reserved                       |
| 15:8   | COMPL_MASK   | RW   | 0x00  | Completion mask                |
| 7:0    | TIMEOUT_MASK | RW   | 0xFF  | Timeout mask                   |

: RDMON_MASK1

#### RDMON_MASK2 (0x278)

Read engine AXI monitor threshold and performance masks.

| Bits   | Field       | Type | Reset | Description                    |
|--------|-------------|------|-------|--------------------------------|
| 31:16  | Reserved    | RO   | 0x0   | Reserved                       |
| 15:8   | PERF_MASK   | RW   | 0x00  | Performance mask               |
| 7:0    | THRESH_MASK | RW   | 0xFF  | Threshold mask                 |

: RDMON_MASK2

#### RDMON_MASK3 (0x27C)

Read engine AXI monitor address and debug masks.

| Bits   | Field      | Type | Reset | Description                    |
|--------|------------|------|-------|--------------------------------|
| 31:16  | Reserved   | RO   | 0x0   | Reserved                       |
| 15:8   | DEBUG_MASK | RW   | 0x00  | Debug mask                     |
| 7:0    | ADDR_MASK  | RW   | 0xFF  | Address mask                   |

: RDMON_MASK3

---

### Write Engine AXI Monitor Configuration (0x280 - 0x29F)

#### WRMON_ENABLE (0x280)

Write engine AXI master monitor enable controls.

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:5  | Reserved    | RO   | 0x0   | Reserved                                 |
| 4     | PERF_EN     | RW   | 0     | Performance packet enable                |
| 3     | TIMEOUT_EN  | RW   | 1     | Timeout detection enable                 |
| 2     | COMPL_EN    | RW   | 0     | Completion packet enable                 |
| 1     | ERR_EN      | RW   | 1     | Error detection enable                   |
| 0     | MON_EN      | RW   | 1     | Master enable for write monitor          |

: WRMON_ENABLE

#### WRMON_TIMEOUT (0x284)

Write engine AXI monitor timeout threshold.

| Bits   | Field           | Type | Reset  | Description                          |
|--------|-----------------|------|--------|--------------------------------------|
| 31:0   | TIMEOUT_CYCLES  | RW   | 10000  | Timeout in clock cycles              |

: WRMON_TIMEOUT

#### WRMON_LATENCY_THRESH (0x288)

Write engine AXI monitor latency threshold.

| Bits   | Field          | Type | Reset | Description                           |
|--------|----------------|------|-------|---------------------------------------|
| 31:0   | LATENCY_THRESH | RW   | 5000  | Latency threshold in clock cycles     |

: WRMON_LATENCY_THRESH

#### WRMON_PKT_MASK (0x28C)

Write engine AXI monitor packet type filtering.

| Bits   | Field     | Type | Reset  | Description                              |
|--------|-----------|------|--------|------------------------------------------|
| 31:16  | Reserved  | RO   | 0x0    | Reserved                                 |
| 15:0   | PKT_MASK  | RW   | 0xFFFF | Packet type mask (1=enable, 0=disable)   |

: WRMON_PKT_MASK

#### WRMON_ERR_CFG (0x290)

Write engine AXI monitor error selection and filtering.

| Bits   | Field      | Type | Reset | Description                              |
|--------|------------|------|-------|------------------------------------------|
| 31:16  | Reserved   | RO   | 0x0   | Reserved                                 |
| 15:8   | ERR_MASK   | RW   | 0xFF  | Error type filtering mask                |
| 7:4    | Reserved   | RO   | 0x0   | Reserved                                 |
| 3:0    | ERR_SELECT | RW   | 0x0   | Error type selection                     |

: WRMON_ERR_CFG

#### WRMON_MASK1 (0x294)

Write engine AXI monitor timeout and completion masks.

| Bits   | Field        | Type | Reset | Description                    |
|--------|--------------|------|-------|--------------------------------|
| 31:16  | Reserved     | RO   | 0x0   | Reserved                       |
| 15:8   | COMPL_MASK   | RW   | 0x00  | Completion mask                |
| 7:0    | TIMEOUT_MASK | RW   | 0xFF  | Timeout mask                   |

: WRMON_MASK1

#### WRMON_MASK2 (0x298)

Write engine AXI monitor threshold and performance masks.

| Bits   | Field       | Type | Reset | Description                    |
|--------|-------------|------|-------|--------------------------------|
| 31:16  | Reserved    | RO   | 0x0   | Reserved                       |
| 15:8   | PERF_MASK   | RW   | 0x00  | Performance mask               |
| 7:0    | THRESH_MASK | RW   | 0xFF  | Threshold mask                 |

: WRMON_MASK2

#### WRMON_MASK3 (0x29C)

Write engine AXI monitor address and debug masks.

| Bits   | Field      | Type | Reset | Description                    |
|--------|------------|------|-------|--------------------------------|
| 31:16  | Reserved   | RO   | 0x0   | Reserved                       |
| 15:8   | DEBUG_MASK | RW   | 0x00  | Debug mask                     |
| 7:0    | ADDR_MASK  | RW   | 0xFF  | Address mask                   |

: WRMON_MASK3

---

### AXI Transfer Configuration (0x2A0 - 0x2AF)

#### AXI_XFER_CONFIG (0x2A0)

AXI read and write transfer burst sizes.

| Bits   | Field          | Type | Reset | Description                                     |
|--------|----------------|------|-------|-------------------------------------------------|
| 31:16  | Reserved       | RO   | 0x0   | Reserved                                        |
| 15:8   | WR_XFER_BEATS  | RW   | 15    | AXI write transfer beats (AWLEN: 0-255 = 1-256) |
| 7:0    | RD_XFER_BEATS  | RW   | 15    | AXI read transfer beats (ARLEN: 0-255 = 1-256)  |

: AXI_XFER_CONFIG

**Usage:**
```c
// Configure for 16-beat bursts (default)
write32(BASE + AXI_XFER_CONFIG, 0x0F0F);

// Configure for 64-beat bursts
write32(BASE + AXI_XFER_CONFIG, 0x3F3F);

// Configure for maximum 256-beat bursts
write32(BASE + AXI_XFER_CONFIG, 0xFFFF);
```

---

### Performance Profiler Configuration (0x2B0 - 0x2BF)

#### PERF_CONFIG (0x2B0)

Performance profiler enable and mode controls.

| Bits   | Field       | Type | Reset | Description                              |
|--------|-------------|------|-------|------------------------------------------|
| 31:3   | Reserved    | RO   | 0x0   | Reserved                                 |
| 2      | PERF_CLEAR  | RW   | 0     | Clear counters (write 1, self-clearing)  |
| 1      | PERF_MODE   | RW   | 0     | Mode: 0=count, 1=histogram               |
| 0      | PERF_EN     | RW   | 0     | Performance profiler enable              |

: PERF_CONFIG

**Usage:**
```c
// Enable performance profiler in count mode
write32(BASE + PERF_CONFIG, 0x01);

// Enable in histogram mode
write32(BASE + PERF_CONFIG, 0x03);

// Clear counters
write32(BASE + PERF_CONFIG, 0x05);  // EN + CLEAR
// PERF_CLEAR self-clears after one cycle
```

---

## Typical Usage Flow

### Initialization

```c
// 1. Global enable
write32(BASE + GLOBAL_CTRL, 0x1);

// 2. Configure scheduler
write32(BASE + SCHED_TIMEOUT_CYCLES, 10000);
write32(BASE + SCHED_CONFIG, 0x1F);  // All features enabled

// 3. Configure descriptor engine
write32(BASE + DESCENG_CONFIG, 0x01);  // Enable, no prefetch
write32(BASE + DESCENG_ADDR0_BASE, 0x8000_0000);
write32(BASE + DESCENG_ADDR0_LIMIT, 0x8FFF_FFFF);

// 4. Configure monitors (minimal reporting)
write32(BASE + DAXMON_CONFIG, 0x05);  // Error + timeout only
write32(BASE + RDMON_CONFIG, 0x05);
write32(BASE + WRMON_CONFIG, 0x05);

// 5. Enable desired channels
write32(BASE + CHANNEL_ENABLE, 0xFF);  // All 8 channels
```

### Start Transfer

```c
// Write 64-bit descriptor address to channel kick-off registers
// Descriptor at address 0x0000_0000_8000_0100 (64-bit)
write32(BASE + CH0_CTRL_LOW, 0x8000_0100);   // Lower 32 bits (buffered)
write32(BASE + CH0_CTRL_HIGH, 0x0000_0000);  // Upper 32 bits (triggers kick-off)
// Transfer starts immediately (blocks until descriptor engine ready)
```

### Poll for Completion

```c
// Check channel 0 idle status
while (!(read32(BASE + CHANNEL_IDLE) & 0x01)) {
    // Wait for channel 0 to become idle
}

// Or check scheduler state (one-hot encoding)
while ((read32(BASE + CH0_STATE) & 0x7F) != 0x01) {
    // Wait for CH_IDLE state (bit 0 = 0x01)
}
```

### Error Handling

```c
// Check all channel states for errors (one-hot encoding)
for (int ch = 0; ch < 8; ch++) {
    uint32_t state = read32(BASE + CH0_STATE + (ch * 4)) & 0x7F;
    if (state & 0x20) {  // CH_ERROR (bit 5)
        // Reset channel
        write32(BASE + CHANNEL_RESET, 1 << ch);
    }
}
```

---

## Register Summary Table

| Offset Range | Description                           | Count | Type          |
|--------------|---------------------------------------|-------|---------------|
| 0x000-0x03F  | Channel kick-off registers (LOW/HIGH) | 16    | Write-routing |
| 0x100-0x11F  | Global control and status             | 3     | RW/RO         |
| 0x120-0x13F  | Per-channel control                   | 2     | RW            |
| 0x140-0x16F  | Per-channel status                    | 11    | RO            |
| 0x170-0x17F  | Engine completion and error status    | 3     | RO            |
| 0x180-0x1FF  | Monitor FIFO status                   | 2     | RO            |
| 0x200-0x21F  | Scheduler configuration               | 2     | RW            |
| 0x220-0x23F  | Descriptor engine configuration       | 5     | RW            |
| 0x240-0x25F  | Descriptor AXI monitor configuration  | 8     | RW            |
| 0x260-0x27F  | Read engine AXI monitor configuration | 8     | RW            |
| 0x280-0x29F  | Write engine AXI monitor configuration| 8     | RW            |
| 0x2A0-0x2AF  | AXI transfer configuration            | 1     | RW            |
| 0x2B0-0x2BF  | Performance profiler configuration    | 1     | RW            |

: Register Summary Table

**Total:** 70 registers (16 kick-off + 54 config/status)

---

## PeakRDL Generation

To generate SystemVerilog from the register definition:

```bash
cd projects/components/stream/rtl/stream_macro/
peakrdl regblock stream_regs.rdl -o generated/
```

This generates:
- `stream_regs_pkg.sv` - Register definitions package
- `stream_regs.sv` - APB slave register interface

---

**Revision History:**

| Version | Date       | Author         | Description                                      |
|---------|------------|----------------|--------------------------------------------------|
| 1.0     | 2025-10-20 | sean galloway  | Initial creation                                 |
| 1.1     | 2025-12-01 | sean galloway  | Added complete monitor registers from RDL        |
|         |            |                | Added engine completion/error status (0x170)     |
|         |            |                | Added monitor FIFO status (0x180)                |
|         |            |                | Added AXI transfer config (0x2A0)                |
|         |            |                | Added performance profiler config (0x2B0)        |

: PeakRDL Generation
