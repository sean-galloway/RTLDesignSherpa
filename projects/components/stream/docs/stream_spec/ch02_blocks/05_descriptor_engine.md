# Descriptor Engine

**Module:** `descriptor_engine.sv`
**Location:** `projects/components/stream/rtl/fub/`
**Category:** FUB (Functional Unit Block)
**Parent:** `scheduler_group.sv`
**Status:** Implemented
**Last Updated:** 2025-11-30

---

## Overview

The `descriptor_engine` module is an autonomous descriptor fetch engine with chaining support. It fetches 256-bit STREAM descriptors from memory via AXI4 master interface and provides two operating modes for kick-off.

### Key Features

- **Two Operating Modes:**
  - APB-initiated: Software writes descriptor address, engine fetches
  - Autonomous chaining: Engine automatically fetches next_descriptor_ptr
- **Two-FIFO Architecture:**
  - Descriptor address FIFO: Holds addresses to fetch
  - Descriptor data FIFO: Buffers fetched descriptors for scheduler
- **Address Range Validation:** Two configurable ranges for security
- **MonBus Event Reporting:** Fetch complete and error events

---

## Architecture

### Operating Flow

**APB Mode:**
```
APB write -> skid buffer -> desc addr FIFO -> AXI fetch -> desc data FIFO -> scheduler
```

**Chaining Mode:**
```
Descriptor complete -> extract next_ptr -> validate -> desc addr FIFO ->
AXI fetch -> desc data FIFO -> scheduler (repeat until last=1 or next_ptr=0)
```

### FSM States

```systemverilog
typedef enum logic [2:0] {
    RD_IDLE       = 3'b000,  // Waiting for descriptor address
    RD_ISSUE_ADDR = 3'b001,  // Issue AXI AR transaction
    RD_WAIT_DATA  = 3'b010,  // Wait for AXI R response
    RD_COMPLETE   = 3'b011,  // Descriptor fetched, push to FIFO
    RD_ERROR      = 3'b100   // Error occurred
} read_engine_state_t;
```

### Descriptor Format (256-bit STREAM)

| Bits | Field | Description |
|------|-------|-------------|
| [63:0] | src_addr | Source memory address (64-bit, must be aligned) |
| [127:64] | dst_addr | Destination memory address (64-bit, must be aligned) |
| [159:128] | length | Transfer length in BEATS (not bytes!) |
| [191:160] | next_descriptor_ptr | Address of next descriptor (32-bit, 0 = last) |
| [192] | valid | Descriptor valid flag |
| [193] | gen_irq | Generate interrupt on completion |
| [194] | last | Last descriptor in chain (explicit termination) |
| [195] | error | Descriptor error flag |
| [199:196] | channel_id | Channel identifier |
| [207:200] | priority | Descriptor priority |
| [255:208] | reserved | Reserved for future use |

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CHANNEL_ID` | int | 0 | Channel identifier |
| `NUM_CHANNELS` | int | 32 | Total number of channels |
| `CHAN_WIDTH` | int | $clog2(NUM_CHANNELS) | Channel ID width |
| `ADDR_WIDTH` | int | 64 | Address bus width |
| `AXI_ID_WIDTH` | int | 8 | AXI transaction ID width |
| `FIFO_DEPTH` | int | 8 | Descriptor data FIFO depth |
| `DESC_ADDR_FIFO_DEPTH` | int | 2 | Descriptor address FIFO depth |
| `TIMEOUT_CYCLES` | int | 1000 | AXI timeout threshold |

### Monitor Bus Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `MON_AGENT_ID` | 8-bit | 0x10 | Descriptor Engine Agent ID |
| `MON_UNIT_ID` | 4-bit | 0x1 | Unit identifier |
| `MON_CHANNEL_ID` | 6-bit | 0x0 | Base channel ID |

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low asynchronous reset |

### APB Programming Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `apb_valid` | input | 1 | Descriptor address valid |
| `apb_ready` | output | 1 | Ready to accept address |
| `apb_addr` | input | ADDR_WIDTH | Descriptor address |

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `channel_idle` | input | 1 | Scheduler idle (enables APB) |
| `descriptor_valid` | output | 1 | Descriptor available |
| `descriptor_ready` | input | 1 | Scheduler ready to accept |
| `descriptor_packet` | output | 256 | FIXED 256-bit descriptor |
| `descriptor_error` | output | 1 | Fetch error flag |

### Enhanced Control Outputs

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `descriptor_eos` | output | 1 | End of Stream (future use) |
| `descriptor_eol` | output | 1 | End of Line (future use) |
| `descriptor_eod` | output | 1 | End of Data (future use) |
| `descriptor_type` | output | 2 | Packet type (future use) |

### AXI4 AR Channel

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `ar_valid` | output | 1 | Address valid |
| `ar_ready` | input | 1 | Address ready |
| `ar_addr` | output | ADDR_WIDTH | Address |
| `ar_len` | output | 8 | Burst length - 1 |
| `ar_size` | output | 3 | Burst size (log2 bytes) |
| `ar_burst` | output | 2 | Burst type (INCR) |
| `ar_id` | output | AXI_ID_WIDTH | Transaction ID |
| `ar_lock` | output | 1 | Lock type |
| `ar_cache` | output | 4 | Cache attributes |
| `ar_prot` | output | 3 | Protection attributes |
| `ar_qos` | output | 4 | QoS value |
| `ar_region` | output | 4 | Region identifier |

### AXI4 R Channel (FIXED 256-bit)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `r_valid` | input | 1 | Read data valid |
| `r_ready` | output | 1 | Read data ready |
| `r_data` | input | 256 | Read data (FIXED 256-bit) |
| `r_resp` | input | 2 | Response |
| `r_last` | input | 1 | Last beat |
| `r_id` | input | AXI_ID_WIDTH | Transaction ID |

### Configuration Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_prefetch_enable` | input | 1 | Enable descriptor prefetch |
| `cfg_fifo_threshold` | input | 4 | FIFO threshold for prefetch |
| `cfg_addr0_base` | input | ADDR_WIDTH | Address range 0 base |
| `cfg_addr0_limit` | input | ADDR_WIDTH | Address range 0 limit |
| `cfg_addr1_base` | input | ADDR_WIDTH | Address range 1 base |
| `cfg_addr1_limit` | input | ADDR_WIDTH | Address range 1 limit |
| `cfg_channel_reset` | input | 1 | Channel reset |

### Status Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `descriptor_engine_idle` | output | 1 | Engine idle |

### Monitor Bus Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `mon_valid` | output | 1 | Monitor packet valid |
| `mon_ready` | input | 1 | Monitor packet ready |
| `mon_packet` | output | 64 | Monitor packet data |

---

## Operation

### APB Acceptance Policy

APB writes are accepted ONLY when ALL conditions met:
1. `!r_channel_reset_active` - Not in channel reset
2. `w_desc_addr_fifo_empty` - No pending descriptor fetches
3. `channel_idle` - Scheduler completed all prior descriptors
4. `!r_apb_ip` - No APB transaction currently in progress
5. `apb_addr != 0` - Address 0 is invalid

### Autonomous Chaining Decision Tree

**Level 1: Basic Eligibility (w_chain_condition)**
- `next_descriptor_ptr != 0` (non-null pointer)
- `descriptor.last == 0` (not explicitly marked as last)
- `descriptor.valid == 1` (valid descriptor)

**Level 2: Address Validation (w_next_addr_valid)**
- next_addr within `cfg_addr0_base..cfg_addr0_limit` OR
- next_addr within `cfg_addr1_base..cfg_addr1_limit`

**Level 3: Final Decision (w_should_chain)**
- Level 1 + Level 2 conditions met
- `!r_descriptor_error` (no fetch error)
- `w_desc_fifo_wr_ready` (descriptor FIFO has space)

### AXI Transaction

```systemverilog
ar_len = 8'h00;           // Single beat transfer
ar_size = 3'b110;         // 64 bytes (512-bit for 256-bit descriptor)
ar_burst = 2'b01;         // INCR burst type
ar_id = {{padding}, CHANNEL_ID};  // Channel ID in lower bits
ar_cache = 4'b0010;       // Normal non-cacheable bufferable
ar_prot = 3'b000;         // Data, secure, unprivileged
```

---

## Integration Example

```systemverilog
descriptor_engine #(
    .CHANNEL_ID         (ch),
    .NUM_CHANNELS       (8),
    .ADDR_WIDTH         (64),
    .AXI_ID_WIDTH       (8),
    .FIFO_DEPTH         (8),
    .MON_AGENT_ID       (8'h10 + ch)
) u_descriptor_engine (
    .clk                (clk),
    .rst_n              (rst_n),

    // APB interface
    .apb_valid          (apb_valid),
    .apb_ready          (apb_ready),
    .apb_addr           (apb_addr),

    // Scheduler interface
    .channel_idle       (scheduler_idle),
    .descriptor_valid   (desc_valid),
    .descriptor_ready   (desc_ready),
    .descriptor_packet  (desc_packet),
    .descriptor_error   (desc_error),

    // AXI interface
    .ar_valid           (ar_valid),
    .ar_ready           (ar_ready),
    .ar_addr            (ar_addr),
    // ... full AR/R interface

    // Configuration
    .cfg_prefetch_enable    (cfg_desceng_prefetch),
    .cfg_addr0_base         (cfg_desceng_addr0_base),
    .cfg_addr0_limit        (cfg_desceng_addr0_limit),
    .cfg_addr1_base         (cfg_desceng_addr1_base),
    .cfg_addr1_limit        (cfg_desceng_addr1_limit),
    .cfg_channel_reset      (cfg_channel_reset),

    // Status
    .descriptor_engine_idle (desc_engine_idle),

    // Monitor bus
    .mon_valid          (desceng_mon_valid),
    .mon_ready          (desceng_mon_ready),
    .mon_packet         (desceng_mon_packet)
);
```

---

## Common Issues

### Issue 1: APB Write Not Accepted

**Symptom:** `apb_ready` never asserts

**Root Causes:**
1. Channel not idle (`channel_idle = 0`)
2. Previous APB transaction still in progress (`r_apb_ip = 1`)
3. Descriptor address FIFO not empty
4. Channel reset active

**Solution:** Wait for channel to complete current work before next kick-off.

### Issue 2: Descriptor Chain Stops Early

**Symptom:** Chaining stops before expected

**Root Causes:**
1. `next_descriptor_ptr` is 0 or out of valid range
2. `last` flag set in descriptor
3. AXI error during fetch

**Debug:** Check descriptor memory contents and address range configuration.

---

## Related Documentation

- **Parent:** `03_scheduler_group.md` - Channel wrapper
- **Consumer:** `04_scheduler.md` - Scheduler that receives descriptors
- **Arbiter:** `02_scheduler_group_array.md` - Descriptor AXI arbitration
- **APB Interface:** `13_apbtodescr.md` - APB to descriptor kick-off

---

**Last Updated:** 2025-11-30 (verified against RTL implementation)
