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
└─ 0x100 - 0xFFF: Configuration and Status Registers
   ├─ 0x100 - 0x11F: Global Control and Status
   ├─ 0x120 - 0x17F: Per-Channel Control and Status
   ├─ 0x200 - 0x21F: Scheduler Configuration
   ├─ 0x220 - 0x23F: Descriptor Engine Configuration
   └─ 0x240 - 0x27F: Monitor Configuration
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
| 15:8   | MAJOR         | RO   | 0x00  | Major version (0)                  |
| 7:0    | MINOR         | RO   | 0x5A  | Minor version (90 decimal = 0.90)  |

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
| 0x150  | CH0_STATE  | 31:7  | Reserved | RO   | Reserved                       |
|        |            | 6:0   | STATE    | RO   | Channel 0 scheduler state (one-hot) |
| 0x154  | CH1_STATE  | 6:0   | STATE    | RO   | Channel 1 scheduler state (one-hot) |
| 0x158  | CH2_STATE  | 6:0   | STATE    | RO   | Channel 2 scheduler state (one-hot) |
| 0x15C  | CH3_STATE  | 6:0   | STATE    | RO   | Channel 3 scheduler state (one-hot) |
| 0x160  | CH4_STATE  | 6:0   | STATE    | RO   | Channel 4 scheduler state (one-hot) |
| 0x164  | CH5_STATE  | 6:0   | STATE    | RO   | Channel 5 scheduler state (one-hot) |
| 0x168  | CH6_STATE  | 6:0   | STATE    | RO   | Channel 6 scheduler state (one-hot) |
| 0x16C  | CH7_STATE  | 6:0   | STATE    | RO   | Channel 7 scheduler state (one-hot) |

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
| 0x120-0x17F  | Per-channel control and status        | 12    | RW/RO         |
| 0x200-0x21F  | Scheduler configuration               | 2     | RW            |
| 0x220-0x23F  | Descriptor engine configuration       | 6     | RW            |
| 0x240-0x27F  | Monitor configuration                 | 5     | RW            |

**Total:** 44 registers (16 kick-off + 28 config/status)

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
