# STREAM Register Map

## Overview

The STREAM DMA engine register interface consists of two distinct regions:

1. **Channel Kick-off Registers** (0x000 - 0x01C) - Direct routing to descriptor engines
2. **Configuration and Status Registers** (0x100 - 0xFFF) - PeakRDL-generated register file

## Address Space Layout

```
Base Address (configurable parameter)
│
├─ 0x000 - 0x01C: Channel Kick-off (apbtodescr.sv routing)
│  ├─ 0x000: CH0_CTRL - Channel 0 descriptor address
│  ├─ 0x004: CH1_CTRL - Channel 1 descriptor address
│  ├─ 0x008: CH2_CTRL - Channel 2 descriptor address
│  ├─ 0x00C: CH3_CTRL - Channel 3 descriptor address
│  ├─ 0x010: CH4_CTRL - Channel 4 descriptor address
│  ├─ 0x014: CH5_CTRL - Channel 5 descriptor address
│  ├─ 0x018: CH6_CTRL - Channel 6 descriptor address
│  └─ 0x01C: CH7_CTRL - Channel 7 descriptor address
│
├─ 0x020 - 0x0FF: Reserved
│
└─ 0x100 - 0xFFF: Configuration and Status Registers
   ├─ 0x100 - 0x11F: Global Control and Status
   ├─ 0x120 - 0x17F: Per-Channel Control and Status
   ├─ 0x200 - 0x21F: Scheduler Configuration
   ├─ 0x220 - 0x23F: Descriptor Engine Configuration
   └─ 0x240 - 0x27F: Monitor Configuration
```

## Register Details

### Channel Kick-off Registers (0x000 - 0x01C)

These registers are **NOT** traditional registers. Writes are routed directly to descriptor engine APB ports via `apbtodescr.sv`.

| Offset | Register   | Type | Reset | Description                                    |
|--------|------------|------|-------|------------------------------------------------|
| 0x000  | CH0_CTRL   | WO   | N/A   | Channel 0 descriptor address kick-off          |
| 0x004  | CH1_CTRL   | WO   | N/A   | Channel 1 descriptor address kick-off          |
| 0x008  | CH2_CTRL   | WO   | N/A   | Channel 2 descriptor address kick-off          |
| 0x00C  | CH3_CTRL   | WO   | N/A   | Channel 3 descriptor address kick-off          |
| 0x010  | CH4_CTRL   | WO   | N/A   | Channel 4 descriptor address kick-off          |
| 0x014  | CH5_CTRL   | WO   | N/A   | Channel 5 descriptor address kick-off          |
| 0x018  | CH6_CTRL   | WO   | N/A   | Channel 6 descriptor address kick-off          |
| 0x01C  | CH7_CTRL   | WO   | N/A   | Channel 7 descriptor address kick-off          |

**Write Behavior:**
- Write data = 32-bit descriptor address (lower 32 bits)
- Upper 32 bits assumed to be 0 (descriptors in lower 4GB)
- Write blocks until descriptor engine accepts (back-pressure)
- Read not supported (returns error)

**Example:**
```c
// Start DMA transfer on channel 0
// Descriptor at physical address 0x8000_0000
write32(BASE + CH0_CTRL, 0x8000_0000);  // Blocks until accepted
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

#### VERSION (0x108)

Version and configuration information (read-only).

| Bits   | Field         | Type | Value | Description                        |
|--------|---------------|------|-------|------------------------------------|
| 31:24  | Reserved      | RO   | 0x00  | Reserved                           |
| 23:16  | NUM_CHANNELS  | RO   | 0x08  | Number of channels (8)             |
| 15:8   | MAJOR         | RO   | 0x01  | Major version (1)                  |
| 7:0    | MINOR         | RO   | 0x00  | Minor version (0)                  |

---

### Per-Channel Control and Status (0x120 - 0x17F)

#### CHANNEL_ENABLE (0x120)

Per-channel enable control (bit vector).

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:8  | Reserved    | RO   | 0x0   | Reserved                                 |
| 7:0   | CH_EN       | RW   | 0x00  | Channel enable [7:0] (1=enabled)         |

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

#### DESC_ENGINE_IDLE (0x144)

Per-channel descriptor engine idle status.

| Bits  | Field       | Type | Description                                     |
|-------|-------------|------|-------------------------------------------------|
| 31:8  | Reserved    | RO   | Reserved                                        |
| 7:0   | DESC_IDLE   | RO   | Descriptor engine idle [7:0] (1=idle, 0=active) |

#### SCHEDULER_IDLE (0x148)

Per-channel scheduler idle status.

| Bits  | Field       | Type | Description                                   |
|-------|-------------|------|-----------------------------------------------|
| 31:8  | Reserved    | RO   | Reserved                                      |
| 7:0   | SCHED_IDLE  | RO   | Scheduler idle [7:0] (1=idle, 0=active)       |

#### CH_STATE[0..7] (0x150 - 0x16C)

Per-channel scheduler FSM state (8 registers, stride 0x4).

| Offset | Register   | Bits  | Field    | Type | Description                    |
|--------|------------|-------|----------|------|--------------------------------|
| 0x150  | CH0_STATE  | 31:4  | Reserved | RO   | Reserved                       |
|        |            | 3:0   | STATE    | RO   | Channel 0 scheduler state      |
| 0x154  | CH1_STATE  | 3:0   | STATE    | RO   | Channel 1 scheduler state      |
| 0x158  | CH2_STATE  | 3:0   | STATE    | RO   | Channel 2 scheduler state      |
| 0x15C  | CH3_STATE  | 3:0   | STATE    | RO   | Channel 3 scheduler state      |
| 0x160  | CH4_STATE  | 3:0   | STATE    | RO   | Channel 4 scheduler state      |
| 0x164  | CH5_STATE  | 3:0   | STATE    | RO   | Channel 5 scheduler state      |
| 0x168  | CH6_STATE  | 3:0   | STATE    | RO   | Channel 6 scheduler state      |
| 0x16C  | CH7_STATE  | 3:0   | STATE    | RO   | Channel 7 scheduler state      |

**State Encoding:**
```
0x0 = CH_IDLE       - Idle, waiting for descriptor
0x1 = CH_FETCH_DESC - Fetching descriptor
0x2 = CH_READ_DATA  - Reading source data
0x3 = CH_WRITE_DATA - Writing destination data
0x4 = CH_COMPLETE   - Transfer complete
0x5 = CH_NEXT_DESC  - Chaining to next descriptor
0x6 = CH_ERROR      - Error state
```

---

### Scheduler Configuration (0x200 - 0x21F)

#### SCHED_TIMEOUT_CYCLES (0x200)

Timeout threshold for scheduler (global for all channels).

| Bits   | Field           | Type | Reset | Description                          |
|--------|-----------------|------|-------|--------------------------------------|
| 31:16  | Reserved        | RO   | 0x0   | Reserved                             |
| 15:0   | TIMEOUT_CYCLES  | RW   | 1000  | Timeout in clock cycles              |

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

#### DESCENG_ADDR0_BASE (0x224)

Base address for descriptor address range 0 (lower 32 bits).

| Bits   | Field       | Type | Reset      | Description                          |
|--------|-------------|------|------------|--------------------------------------|
| 31:0   | ADDR0_BASE  | RW   | 0x00000000 | Address range 0 base                 |

#### DESCENG_ADDR0_LIMIT (0x228)

Limit address for descriptor address range 0 (lower 32 bits).

| Bits   | Field        | Type | Reset      | Description                          |
|--------|--------------|------|------------|--------------------------------------|
| 31:0   | ADDR0_LIMIT  | RW   | 0xFFFFFFFF | Address range 0 limit                |

#### DESCENG_ADDR1_BASE (0x22C)

Base address for descriptor address range 1 (lower 32 bits).

| Bits   | Field       | Type | Reset      | Description                          |
|--------|-------------|------|------------|--------------------------------------|
| 31:0   | ADDR1_BASE  | RW   | 0x00000000 | Address range 1 base                 |

#### DESCENG_ADDR1_LIMIT (0x230)

Limit address for descriptor address range 1 (lower 32 bits).

| Bits   | Field        | Type | Reset      | Description                          |
|--------|--------------|------|------------|--------------------------------------|
| 31:0   | ADDR1_LIMIT  | RW   | 0xFFFFFFFF | Address range 1 limit                |

---

### Monitor Configuration (0x240 - 0x27F)

#### DAXMON_CONFIG (0x240)

Descriptor AXI master monitor configuration.

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:5  | Reserved    | RO   | 0x0   | Reserved                                 |
| 4     | DEBUG_EN    | RW   | 0     | Debug packet enable                      |
| 3     | PERF_EN     | RW   | 0     | Performance packet enable                |
| 2     | TIMEOUT_EN  | RW   | 1     | Timeout detection enable                 |
| 1     | COMPL_EN    | RW   | 0     | Completion packet enable                 |
| 0     | ERR_EN      | RW   | 1     | Error detection enable                   |

#### RDMON_CONFIG (0x244)

Data read AXI master monitor configuration.

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:5  | Reserved    | RO   | 0x0   | Reserved                                 |
| 4     | DEBUG_EN    | RW   | 0     | Debug packet enable                      |
| 3     | PERF_EN     | RW   | 0     | Performance packet enable                |
| 2     | TIMEOUT_EN  | RW   | 1     | Timeout detection enable                 |
| 1     | COMPL_EN    | RW   | 0     | Completion packet enable                 |
| 0     | ERR_EN      | RW   | 1     | Error detection enable                   |

#### RDMON_TIMEOUT (0x248)

Data read monitor timeout threshold.

| Bits   | Field           | Type | Reset | Description                          |
|--------|-----------------|------|-------|--------------------------------------|
| 31:16  | Reserved        | RO   | 0x0   | Reserved                             |
| 15:0   | TIMEOUT_CYCLES  | RW   | 5000  | Timeout in clock cycles              |

#### WRMON_CONFIG (0x24C)

Data write AXI master monitor configuration.

| Bits  | Field       | Type | Reset | Description                              |
|-------|-------------|------|-------|------------------------------------------|
| 31:5  | Reserved    | RO   | 0x0   | Reserved                                 |
| 4     | DEBUG_EN    | RW   | 0     | Debug packet enable                      |
| 3     | PERF_EN     | RW   | 0     | Performance packet enable                |
| 2     | TIMEOUT_EN  | RW   | 1     | Timeout detection enable                 |
| 1     | COMPL_EN    | RW   | 0     | Completion packet enable                 |
| 0     | ERR_EN      | RW   | 1     | Error detection enable                   |

#### WRMON_TIMEOUT (0x250)

Data write monitor timeout threshold.

| Bits   | Field           | Type | Reset | Description                          |
|--------|-----------------|------|-------|--------------------------------------|
| 31:16  | Reserved        | RO   | 0x0   | Reserved                             |
| 15:0   | TIMEOUT_CYCLES  | RW   | 5000  | Timeout in clock cycles              |

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
// Write descriptor address to channel kick-off register
write32(BASE + CH0_CTRL, 0x8000_0100);  // Channel 0 descriptor at 0x8000_0100
// Transfer starts immediately (blocks until descriptor engine ready)
```

### Poll for Completion

```c
// Check channel 0 idle status
while (!(read32(BASE + CHANNEL_IDLE) & 0x01)) {
    // Wait for channel 0 to become idle
}

// Or check scheduler state
while ((read32(BASE + CH0_STATE) & 0xF) != 0x0) {
    // Wait for CH_IDLE state (0x0)
}
```

### Error Handling

```c
// Check all channel states for errors
for (int ch = 0; ch < 8; ch++) {
    uint32_t state = read32(BASE + CH0_STATE + (ch * 4)) & 0xF;
    if (state == 0x6) {  // CH_ERROR
        // Reset channel
        write32(BASE + CHANNEL_RESET, 1 << ch);
    }
}
```

---

## Register Summary Table

| Offset Range | Description                           | Count | Type          |
|--------------|---------------------------------------|-------|---------------|
| 0x000-0x01C  | Channel kick-off registers            | 8     | Write-routing |
| 0x100-0x11F  | Global control and status             | 3     | RW/RO         |
| 0x120-0x17F  | Per-channel control and status        | 12    | RW/RO         |
| 0x200-0x21F  | Scheduler configuration               | 2     | RW            |
| 0x220-0x23F  | Descriptor engine configuration       | 6     | RW            |
| 0x240-0x27F  | Monitor configuration                 | 5     | RW            |

**Total:** 36 registers (8 kick-off + 28 config/status)

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

| Version | Date       | Author         | Description          |
|---------|------------|----------------|----------------------|
| 1.0     | 2025-10-20 | sean galloway  | Initial creation     |
