# Chapter 6: Configuration Reference

**Version:** 0.90
**Last Updated:** 2025-11-22
**Purpose:** Complete reference for all STREAM configuration signals

---

## Overview

STREAM provides comprehensive runtime configuration through APB registers and compile-time parameters. This chapter documents all configuration signals, their valid ranges, default values, and recommended settings for different use cases.

### Configuration Categories

| Category | Signals | Purpose |
|----------|---------|---------|
| **Channel Control** | 2 | Enable/reset individual channels |
| **Scheduler** | 6 | Transfer scheduling and timeouts |
| **Descriptor Engine** | 7 | Descriptor fetch behavior |
| **AXI Monitors** | 45 (15 per monitor × 3) | Debug/trace filtering |
| **AXI Transfer** | 2 | Burst configuration |
| **Performance** | 3 | Profiling and metrics |
| **Total** | **65 configuration signals** | Full system control |

---

## 1. Channel Control Configuration

### cfg_channel_enable[NUM_CHANNELS-1:0]

**Type:** Per-channel enable
**Width:** 1 bit × NUM_CHANNELS (default 8)
**Default:** 8'hFF (all enabled)
**Register:** CHANNEL_ENABLE @ 0x120

**Description:**
Enables or disables individual DMA channels. When disabled, the channel:
- Ignores descriptor kick-off requests
- Completes current transfer if in progress
- Enters idle state
- Remains in idle until re-enabled

**Valid Values:**
- `1'b1`: Channel enabled (can accept transfers)
- `1'b0`: Channel disabled (ignores new transfers)

**Use Cases:**
```systemverilog
// Enable only channels 0, 2, 4 (even channels)
cfg_channel_enable = 8'b01010101;

// Disable all channels (emergency stop)
cfg_channel_enable = 8'b00000000;

// Enable all channels (normal operation)
cfg_channel_enable = 8'b11111111;
```

**Interaction with Global Enable:**
The final channel enable is: `cfg_channel_enable[i] & reg_global_ctrl_global_en`

---

### cfg_channel_reset[NUM_CHANNELS-1:0]

**Type:** Per-channel reset
**Width:** 1 bit × NUM_CHANNELS (default 8)
**Default:** 8'h00 (no resets active)
**Register:** CHANNEL_RESET @ 0x124

**Description:**
Asserts reset for individual channels without affecting other channels or global state. When asserted:
- Channel FSM returns to IDLE
- Pending transfers aborted
- SRAM buffers flushed
- Descriptor engine reset

**Valid Values:**
- `1'b1`: Channel in reset (clears state)
- `1'b0`: Channel operating normally

**Use Cases:**
```systemverilog
// Reset channel 3 after error
cfg_channel_reset = 8'b00001000;
wait_cycles(10);
cfg_channel_reset = 8'b00000000;  // Release reset

// Reset all channels (soft reset)
cfg_channel_reset = 8'hFF;
wait_cycles(10);
cfg_channel_reset = 8'h00;
```

**IMPORTANT:** Assert reset for minimum 10 clock cycles to ensure complete FSM reset.

---

## 2. Scheduler Configuration

### cfg_sched_timeout_cycles[15:0]

**Type:** Timeout threshold
**Width:** 16 bits
**Default:** 16'd1000 (1,000 cycles)
**Register:** SCHED_TIMEOUT_CYCLES @ 0x200[15:0]

**Description:**
Number of clock cycles before a channel operation times out. Applies to:
- Descriptor fetch latency
- AXI read/write response latency
- Scheduler state transitions

**Valid Range:** 100 to 65535 cycles
**Typical Values:**
- Fast SRAM: 100-500 cycles
- DDR3/DDR4: 1000-10000 cycles
- High-latency: 10000-65535 cycles

**Calculation:**
```
Timeout cycles = (Expected latency × 10) + margin

Example for DDR4 @ 200 MHz:
- Expected read latency: 100 cycles (500 ns)
- Safety margin: 10x
- Timeout = 100 × 10 = 1000 cycles
```

---

### cfg_sched_enable

**Type:** Global scheduler enable
**Width:** 1 bit
**Default:** 1'b1 (enabled)
**Register:** SCHED_CONFIG @ 0x204[0]

**Description:**
Master enable for all schedulers. When disabled, all channels stop scheduling new operations.

---

### cfg_sched_timeout_enable

**Type:** Timeout detection enable
**Width:** 1 bit
**Default:** 1'b1 (enabled)
**Register:** SCHED_CONFIG @ 0x204[1]

**Description:**
Enables timeout detection for scheduler operations. Disable for simulation or known slow memory.

---

### cfg_sched_err_enable

**Type:** Error detection enable
**Width:** 1 bit
**Default:** 1'b1 (enabled)
**Register:** SCHED_CONFIG @ 0x204[2]

**Description:**
Enables error packet generation for scheduler errors (AXI SLVERR, DECERR, timeouts).

---

### cfg_sched_compl_enable

**Type:** Completion event enable
**Width:** 1 bit
**Default:** 1'b1 (enabled by default)
**Register:** SCHED_CONFIG @ 0x204[3]

**Description:**
Enables MonBus packets for transfer completion events. Generate high traffic, use sparingly.

---

### cfg_sched_perf_enable

**Type:** Performance monitoring enable
**Width:** 1 bit
**Default:** 1'b0 (disabled by default)
**Register:** SCHED_CONFIG @ 0x204[4]

**Description:**
Enables performance profiling packets (latency, throughput metrics).

---

## 3. Descriptor Engine Configuration

### cfg_desceng_enable

**Type:** Descriptor engine global enable
**Width:** 1 bit
**Default:** 1'b1 (enabled)
**Register:** DESCENG_CTRL @ 0x220[0]

**Description:**
Global enable for all descriptor engines. When disabled, descriptor fetch stops.

---

### cfg_desceng_prefetch

**Type:** Prefetch enable
**Width:** 1 bit
**Default:** 1'b0 (disabled)
**Register:** DESCENG_CTRL @ 0x220[1]

**Description:**
Enables descriptor prefetching to hide fetch latency.

**Prefetch Behavior:**
- Enabled: Fetch next descriptor while current transfer executes
- Disabled: Wait for current transfer completion before fetching next

**Performance Impact:**
- Prefetch ON: +15-30% throughput for chained descriptors
- Prefetch OFF: Simpler logic, lower area

---

### cfg_desceng_fifo_thresh[3:0]

**Type:** FIFO threshold
**Width:** 4 bits
**Default:** 4'h8 (8 entries)
**Register:** DESCENG_CTRL @ 0x220[7:4]

**Description:**
Number of entries in descriptor FIFO before asserting backpressure.

**Valid Range:** 1-15 entries
**Typical Values:**
- Low latency: 2-4 entries
- Balanced: 8 entries (default)
- High throughput: 12-15 entries

---

### cfg_desceng_addr0_base[31:0]

**Type:** Base address for descriptor region 0
**Width:** 32 bits
**Default:** 32'h0000_0000
**Register:** DESCENG_ADDR0_BASE @ 0x224

**Description:**
Base address of first descriptor memory region. Descriptors fetched from this region if within range.

**Alignment:** Must be aligned to descriptor size (256 bits = 32 bytes)

---

### cfg_desceng_addr0_limit[31:0]

**Type:** Limit address for descriptor region 0
**Width:** 32 bits
**Default:** 32'hFFFF_FFFF (no limit)
**Register:** DESCENG_ADDR0_LIMIT @ 0x228

**Description:**
Upper limit of first descriptor region. Descriptors beyond this address use region 1.

---

### cfg_desceng_addr1_base[31:0]

**Type:** Base address for descriptor region 1
**Width:** 32 bits
**Default:** 32'h0000_0000
**Register:** DESCENG_ADDR1_BASE @ 0x22C

**Description:**
Base address of second descriptor memory region (optional).

---

### cfg_desceng_addr1_limit[31:0]

**Type:** Limit address for descriptor region 1
**Width:** 32 bits
**Default:** 32'hFFFF_FFFF
**Register:** DESCENG_ADDR1_LIMIT @ 0x230

**Description:**
Upper limit of second descriptor region.

---

## 4. AXI Monitor Configuration

STREAM includes three independent AXI monitors with identical configuration sets:

1. **Descriptor AXI Monitor** (`cfg_desc_mon_*`) - Monitors descriptor fetch AXI master
2. **Read Engine Monitor** (`cfg_rdeng_mon_*`) - Monitors data read AXI master
3. **Write Engine Monitor** (`cfg_wreng_mon_*`) - Monitors data write AXI master

Each monitor has 15 configuration signals with the same structure.

---

### 4.1 Descriptor AXI Monitor (cfg_desc_mon_*)

**Register Base:** 0x240-0x25F

#### cfg_desc_mon_enable

**Type:** Monitor master enable
**Width:** 1 bit
**Default:** 1'b1 (enabled)
**Register:** DAXMON_ENABLE @ 0x240[0]

**Description:**
Master enable for descriptor AXI monitor. All monitor packets disabled when this is 0.

---

#### cfg_desc_mon_err_enable

**Type:** Error packet enable
**Width:** 1 bit
**Default:** 1'b1 (enabled)
**Register:** DAXMON_ENABLE @ 0x240[1]

**Description:**
Enables error packet generation (SLVERR, DECERR, protocol violations).

---

#### cfg_desc_mon_perf_enable

**Type:** Performance packet enable
**Width:** 1 bit
**Default:** 1'b0 (disabled)
**Register:** DAXMON_ENABLE @ 0x240[2]

**Description:**
Enables performance monitoring packets (latency, bandwidth).

**WARNING:** High packet rate - use only during debug.

---

#### cfg_desc_mon_timeout_enable

**Type:** Timeout detection enable
**Width:** 1 bit
**Default:** 1'b1 (enabled)
**Register:** DAXMON_ENABLE @ 0x240[3]

**Description:**
Enables timeout packet generation when transactions exceed threshold.

---

#### cfg_desc_mon_timeout_cycles[31:0]

**Type:** Timeout threshold
**Width:** 32 bits
**Default:** 32'd10000
**Register:** DAXMON_TIMEOUT @ 0x244

**Description:**
Number of cycles before transaction times out.

---

#### cfg_desc_mon_latency_thresh[31:0]

**Type:** Latency threshold
**Width:** 32 bits
**Default:** 32'd1000
**Register:** DAXMON_LATENCY @ 0x248

**Description:**
Latency threshold for performance warnings.

---

#### cfg_desc_mon_pkt_mask[15:0]

**Type:** Packet type filter
**Width:** 16 bits (1 bit per packet type)
**Default:** 16'h00FF (errors + completions)
**Register:** DAXMON_PKT_MASK @ 0x24C[15:0]

**Description:**
Bit mask to filter packet types. Only packet types with corresponding bit set are generated.

**Packet Type Mapping:**
```
Bit  | Packet Type
-----|-------------
0    | AR command
1    | AW command
2    | R completion
3    | W data
4    | B response
5    | Error
6    | Timeout
7    | Completion
8-15 | Reserved
```

**Examples:**
```systemverilog
// Only errors
cfg_desc_mon_pkt_mask = 16'h0020;  // Bit 5

// Errors + timeouts
cfg_desc_mon_pkt_mask = 16'h0060;  // Bits 5-6

// All packets
cfg_desc_mon_pkt_mask = 16'hFFFF;
```

---

#### cfg_desc_mon_err_select[3:0]

**Type:** Error type selector
**Width:** 4 bits
**Default:** 4'hF (all errors)
**Register:** DAXMON_ERR_SELECT @ 0x24C[19:16]

**Description:**
Selects which error types to monitor.

**Error Type Bits:**
```
Bit | Error Type
----|------------
0   | SLVERR
1   | DECERR
2   | Protocol violation
3   | Reserved
```

---

#### cfg_desc_mon_err_mask[7:0]

**Type:** Error event filter
**Width:** 8 bits
**Default:** 8'hFF (all errors)
**Register:** DAXMON_MASK1 @ 0x250[7:0]

**Description:**
Bit mask for error packet generation (channel-specific filtering).

---

#### cfg_desc_mon_timeout_mask[7:0]

**Type:** Timeout channel filter
**Width:** 8 bits
**Default:** 8'hFF (all channels)
**Register:** DAXMON_MASK1 @ 0x250[15:8]

**Description:**
Channel mask for timeout packets. Set bit enables timeout detection for corresponding channel.

---

#### cfg_desc_mon_compl_mask[7:0]

**Type:** Completion channel filter
**Width:** 8 bits
**Default:** 8'h00 (no channels)
**Register:** DAXMON_MASK1 @ 0x250[23:16]

**Description:**
Channel mask for completion packets.

**WARNING:** Completion packets are high volume - enable only for specific channels.

---

#### cfg_desc_mon_thresh_mask[7:0]

**Type:** Threshold event filter
**Width:** 8 bits
**Default:** 8'hFF (all channels)
**Register:** DAXMON_MASK2 @ 0x254[7:0]

**Description:**
Channel mask for latency threshold exceedance packets.

---

#### cfg_desc_mon_perf_mask[7:0]

**Type:** Performance packet filter
**Width:** 8 bits
**Default:** 8'h00 (no channels)
**Register:** DAXMON_MASK2 @ 0x254[15:8]

**Description:**
Channel mask for performance monitoring packets.

---

#### cfg_desc_mon_addr_mask[7:0]

**Type:** Address-based filter
**Width:** 8 bits
**Default:** 8'hFF (all addresses)
**Register:** DAXMON_MASK2 @ 0x254[23:16]

**Description:**
Channel mask for address-range-based packet filtering.

---

#### cfg_desc_mon_debug_mask[7:0]

**Type:** Debug event filter
**Width:** 8 bits
**Default:** 8'h00 (no debug packets)
**Register:** DAXMON_MASK2 @ 0x254[31:24]

**Description:**
Channel mask for debug-level packets (verbose trace).

---

### 4.2 Read Engine Monitor (cfg_rdeng_mon_*)

**Register Base:** 0x260-0x27F

All signals identical to Descriptor Monitor (Section 4.1), but applied to data read AXI master.

**Key Differences:**
- Monitors data transfers (not descriptors)
- Higher throughput → more packets
- Recommended: Keep `cfg_rdeng_mon_compl_enable = 0` unless debugging

---

### 4.3 Write Engine Monitor (cfg_wreng_mon_*)

**Register Base:** 0x280-0x29F

All signals identical to Descriptor Monitor (Section 4.1), but applied to data write AXI master.

**Key Differences:**
- Monitors write transactions (AW/W/B channels)
- B response timing critical for performance
- Recommended: Enable only error packets by default

---

## 5. AXI Transfer Configuration

### cfg_axi_rd_xfer_beats[7:0]

**Type:** Read transfer size
**Width:** 8 bits
**Default:** 8'd16 (16 beats)
**Register:** AXI_RD_XFER @ 0x2A0[7:0]

**Description:**
Default number of beats per AXI read burst. Actual burst size may be less to respect 4KB boundaries.

**Valid Range:** 1-256 beats (AXI4 standard)
**Typical Values:**
- Small transfers: 4-8 beats
- Balanced: 16 beats (default)
- Large transfers: 32-64 beats
- Maximum throughput: 128-256 beats

**Calculation:**
```
Transfer size (bytes) = beats × (DATA_WIDTH / 8)

Example for DATA_WIDTH = 512 bits:
- 16 beats = 16 × 64 = 1024 bytes (1 KB)
- 64 beats = 64 × 64 = 4096 bytes (4 KB)
```

---

### cfg_axi_wr_xfer_beats[7:0]

**Type:** Write transfer size
**Width:** 8 bits
**Default:** 8'd16 (16 beats)
**Register:** AXI_WR_XFER @ 0x2A0[15:8]

**Description:**
Default number of beats per AXI write burst.

**Same constraints as `cfg_axi_rd_xfer_beats`**

---

## 6. Performance Profiler Configuration

### cfg_perf_enable

**Type:** Profiler enable
**Width:** 1 bit
**Default:** 1'b0 (disabled)
**Register:** PERF_CTRL @ 0x2B0[0]

**Description:**
Enables performance profiling for all channels. When enabled, profiler captures:
- Transfer start/end timestamps
- Latency per channel
- Throughput measurements
- Channel utilization

---

### cfg_perf_mode

**Type:** Profiling mode
**Width:** 1 bit
**Default:** 1'b0 (timestamp mode)
**Register:** PERF_CTRL @ 0x2B0[1]

**Description:**
Selects profiling mode:
- `1'b0`: Timestamp mode - Record absolute timestamps
- `1'b1`: Elapsed time mode - Record delta times

**Use Cases:**
- Timestamp: Correlate events across multiple blocks
- Elapsed: Measure operation latencies

---

### cfg_perf_clear

**Type:** Clear profiler state
**Width:** 1 bit (write-only)
**Default:** 1'b0
**Register:** PERF_CTRL @ 0x2B0[2]

**Description:**
Write `1'b1` to clear profiler FIFOs and counters. Self-clearing (automatically returns to 0).

---

## 7. Configuration Presets

### 7.1 Minimal Configuration (Tutorial/Embedded)

**Use Case:** Educational, minimal logic, single-channel operation

```systemverilog
// Channel control
cfg_channel_enable = 8'b00000001;  // Only channel 0

// Scheduler
cfg_sched_enable = 1'b1;
cfg_sched_timeout_cycles = 16'd500;      // Short timeout (SRAM)
cfg_sched_timeout_enable = 1'b1;
cfg_sched_err_enable = 1'b1;
cfg_sched_compl_enable = 1'b0;           // Disable completion packets
cfg_sched_perf_enable = 1'b0;            // Disable performance packets

// Descriptor engine
cfg_desceng_enable = 1'b1;
cfg_desceng_prefetch = 1'b0;             // No prefetch (simpler)
cfg_desceng_fifo_thresh = 4'h4;          // Small FIFO

// All monitors DISABLED (reduce logic)
cfg_desc_mon_enable = 1'b0;
cfg_rdeng_mon_enable = 1'b0;
cfg_wreng_mon_enable = 1'b0;

// AXI transfer
cfg_axi_rd_xfer_beats = 8'd8;            // Small bursts
cfg_axi_wr_xfer_beats = 8'd8;

// Performance profiler
cfg_perf_enable = 1'b0;                  // Disabled
```

---

### 7.2 Balanced Configuration (Typical FPGA)

**Use Case:** General-purpose DMA, moderate channels, balanced performance/area

```systemverilog
// Channel control
cfg_channel_enable = 8'hFF;              // All 8 channels

// Scheduler
cfg_sched_enable = 1'b1;
cfg_sched_timeout_cycles = 16'd5000;     // DDR4 timeout
cfg_sched_timeout_enable = 1'b1;
cfg_sched_err_enable = 1'b1;
cfg_sched_compl_enable = 1'b0;           // Errors only
cfg_sched_perf_enable = 1'b0;

// Descriptor engine
cfg_desceng_enable = 1'b1;
cfg_desceng_prefetch = 1'b1;             // Enable prefetch
cfg_desceng_fifo_thresh = 4'h8;          // Balanced FIFO

// Descriptor monitor (errors only)
cfg_desc_mon_enable = 1'b1;
cfg_desc_mon_err_enable = 1'b1;
cfg_desc_mon_perf_enable = 1'b0;
cfg_desc_mon_timeout_enable = 1'b1;
cfg_desc_mon_timeout_cycles = 32'd10000;
cfg_desc_mon_pkt_mask = 16'h0060;        // Errors + timeouts

// Read/write monitors (errors only)
cfg_rdeng_mon_enable = 1'b1;
cfg_rdeng_mon_err_enable = 1'b1;
cfg_rdeng_mon_perf_enable = 1'b0;

cfg_wreng_mon_enable = 1'b1;
cfg_wreng_mon_err_enable = 1'b1;
cfg_wreng_mon_perf_enable = 1'b0;

// AXI transfer
cfg_axi_rd_xfer_beats = 8'd32;           // Moderate bursts
cfg_axi_wr_xfer_beats = 8'd32;

// Performance profiler
cfg_perf_enable = 1'b1;                  // Enable profiling
cfg_perf_mode = 1'b1;                    // Elapsed time mode
```

---

### 7.3 High-Performance Configuration (ASIC/Datacenter)

**Use Case:** Maximum throughput, all channels active, full monitoring

```systemverilog
// Channel control
cfg_channel_enable = 8'hFF;              // All channels

// Scheduler
cfg_sched_enable = 1'b1;
cfg_sched_timeout_cycles = 16'd20000;    // High latency tolerance
cfg_sched_timeout_enable = 1'b1;
cfg_sched_err_enable = 1'b1;
cfg_sched_compl_enable = 1'b1;           // Full monitoring
cfg_sched_perf_enable = 1'b1;

// Descriptor engine
cfg_desceng_enable = 1'b1;
cfg_desceng_prefetch = 1'b1;
cfg_desceng_fifo_thresh = 4'hF;          // Max FIFO depth

// All monitors ENABLED with full profiling
cfg_desc_mon_enable = 1'b1;
cfg_desc_mon_err_enable = 1'b1;
cfg_desc_mon_perf_enable = 1'b1;         // Performance monitoring
cfg_desc_mon_timeout_enable = 1'b1;
cfg_desc_mon_timeout_cycles = 32'd20000;
cfg_desc_mon_pkt_mask = 16'hFFFF;        // All packet types

// Same for read/write monitors
cfg_rdeng_mon_enable = 1'b1;
cfg_rdeng_mon_err_enable = 1'b1;
cfg_rdeng_mon_perf_enable = 1'b1;

cfg_wreng_mon_enable = 1'b1;
cfg_wreng_mon_err_enable = 1'b1;
cfg_wreng_mon_perf_enable = 1'b1;

// AXI transfer
cfg_axi_rd_xfer_beats = 8'd128;          // Large bursts
cfg_axi_wr_xfer_beats = 8'd128;

// Performance profiler
cfg_perf_enable = 1'b1;
cfg_perf_mode = 1'b0;                    // Timestamp mode (correlation)
```

---

### 7.4 Debug Configuration (Verbose Monitoring)

**Use Case:** Debugging integration issues, detailed trace analysis

```systemverilog
// Enable specific channel for debug
cfg_channel_enable = 8'b00000001;        // Channel 0 only

// Scheduler
cfg_sched_enable = 1'b1;
cfg_sched_timeout_cycles = 16'd65535;    // Long timeout for debug
cfg_sched_timeout_enable = 1'b1;
cfg_sched_err_enable = 1'b1;
cfg_sched_compl_enable = 1'b1;           // All events
cfg_sched_perf_enable = 1'b1;

// Descriptor engine
cfg_desceng_enable = 1'b1;
cfg_desceng_prefetch = 1'b0;             // Simpler for debug

// All monitors ENABLED with verbose trace
cfg_desc_mon_enable = 1'b1;
cfg_desc_mon_err_enable = 1'b1;
cfg_desc_mon_perf_enable = 1'b1;
cfg_desc_mon_timeout_enable = 1'b1;
cfg_desc_mon_pkt_mask = 16'hFFFF;        // ALL packets
cfg_desc_mon_compl_mask = 8'h01;         // Channel 0 completions
cfg_desc_mon_debug_mask = 8'h01;         // Channel 0 debug packets

// Same for read/write monitors
cfg_rdeng_mon_enable = 1'b1;
cfg_rdeng_mon_pkt_mask = 16'hFFFF;       // Verbose
cfg_rdeng_mon_compl_mask = 8'h01;

cfg_wreng_mon_enable = 1'b1;
cfg_wreng_mon_pkt_mask = 16'hFFFF;
cfg_wreng_mon_compl_mask = 8'h01;

// AXI transfer (small for debug)
cfg_axi_rd_xfer_beats = 8'd4;
cfg_axi_wr_xfer_beats = 8'd4;

// Performance profiler
cfg_perf_enable = 1'b1;
cfg_perf_mode = 1'b0;                    // Timestamps
```

---

## 8. Configuration Best Practices

### 8.1 Monitor Configuration Guidelines

**General Rules:**

1. **Start with errors only:**
   Enable only `cfg_*_mon_err_enable` initially. Add other packets as needed.

2. **Completion packets are expensive:**
   Only enable `cfg_*_mon_compl_enable` for specific channels during debug.

3. **Performance packets flood MonBus:**
   Enable `cfg_*_mon_perf_enable` sparingly (1-2 channels maximum).

4. **Use masks aggressively:**
   Set channel masks to enable monitoring only on channels of interest.

---

### 8.2 Timeout Configuration

**Calculation Method:**

```
Recommended timeout = (Expected latency × Safety factor) + Margin

Safety factor:
- SRAM: 2-5x
- DDR3/DDR4: 5-10x
- High-latency: 10-20x

Margin: +100 cycles minimum
```

**Examples:**
```
SRAM @ 200 MHz:
- Expected: 20 cycles (100 ns)
- Safety: 5x
- Timeout: 20 × 5 + 100 = 200 cycles

DDR4 @ 200 MHz:
- Expected: 100 cycles (500 ns)
- Safety: 10x
- Timeout: 100 × 10 + 100 = 1100 cycles
```

---

### 8.3 Prefetch Configuration

**Enable prefetch when:**
- Descriptor chains > 2 descriptors
- Memory latency > 50 cycles
- Throughput is priority

**Disable prefetch when:**
- Area is constrained
- Single descriptors only
- Simplicity is priority

---

### 8.4 Burst Size Selection

**Read Burst Size:**
```
Optimal burst size = min(
    Memory controller page size,
    4KB (AXI limit),
    SRAM FIFO depth / 2
)

Example for DDR4 (8KB page), FIFO depth 512 entries:
- Page size: 8192 bytes = 128 beats (512-bit)
- AXI limit: 4096 bytes = 64 beats
- FIFO limit: 512/2 = 256 beats
- Optimal: min(128, 64, 256) = 64 beats
```

**Write Burst Size:**
- Usually same as read burst size
- May be smaller if write FIFO depth is limited

---

## 9. Configuration Register Map Summary

| Address | Register Name | Fields | Section |
|---------|---------------|--------|---------|
| 0x100 | GLOBAL_CTRL | global_en, global_rst | - |
| 0x120 | CHANNEL_ENABLE | ch_en[7:0] | 1 |
| 0x124 | CHANNEL_RESET | ch_rst[7:0] | 1 |
| 0x200 | SCHED_TIMEOUT_CYCLES | timeout_cycles[15:0] | 2 |
| 0x204 | SCHED_CONFIG | enable, timeout_en, err_en, compl_en, perf_en | 2 |
| 0x220 | DESCENG_CONFIG | enable, prefetch, fifo_thresh | 3 |
| 0x224 | DESCENG_ADDR0_BASE | addr0_base[31:0] | 3 |
| 0x228 | DESCENG_ADDR0_LIMIT | addr0_limit[31:0] | 3 |
| 0x22C | DESCENG_ADDR1_BASE | addr1_base[31:0] | 3 |
| 0x230 | DESCENG_ADDR1_LIMIT | addr1_limit[31:0] | 3 |
| 0x240-0x25F | DAXMON_* | Descriptor monitor (15 signals) | 4.1 |
| 0x260-0x27F | RDMON_* | Read engine monitor (15 signals) | 4.2 |
| 0x280-0x29F | WRMON_* | Write engine monitor (15 signals) | 4.3 |
| 0x2A0 | AXI_XFER_CFG | rd_xfer_beats, wr_xfer_beats | 5 |
| 0x2B0 | PERF_CTRL | perf_enable, perf_mode, perf_clear | 6 |

**Total Address Space:** 0x000-0x3FF (1KB)

---

## 10. Software Configuration Examples

### 10.1 C/C++ Initialization (Minimal)

```c
// Minimal configuration for single-channel operation
void stream_init_minimal(volatile uint32_t *base_addr) {
    // Global enable
    base_addr[0x100/4] = 0x00000001;  // GLOBAL_CTRL.global_en

    // Enable channel 0 only
    base_addr[0x120/4] = 0x00000001;  // CHANNEL_ENABLE.ch_en

    // Scheduler config
    base_addr[0x200/4] = 500;         // SCHED_TIMEOUT_CYCLES (SRAM)
    base_addr[0x204/4] = 0x00000007;  // SCHED_CONFIG: enable | timeout_en | err_en

    // Descriptor engine
    base_addr[0x220/4] = 0x00000041;  // enable | fifo_thresh=4

    // Disable all monitors (minimal)
    base_addr[0x240/4] = 0x00000000;  // DAXMON_ENABLE
    base_addr[0x260/4] = 0x00000000;  // RDMON_ENABLE
    base_addr[0x280/4] = 0x00000000;  // WRMON_ENABLE

    // AXI transfer config
    base_addr[0x2A0/4] = 0x00000808;  // 8 beats read + write
}
```

---

### 10.2 C/C++ Initialization (Balanced)

```c
// Balanced configuration for typical FPGA
void stream_init_balanced(volatile uint32_t *base_addr) {
    // Global enable
    base_addr[0x100/4] = 0x00000001;

    // Enable all 8 channels
    base_addr[0x120/4] = 0x000000FF;

    // Scheduler config
    base_addr[0x200/4] = 5000;        // SCHED_TIMEOUT_CYCLES (DDR4)
    base_addr[0x204/4] = 0x00000007;  // SCHED_CONFIG: enable | timeout_en | err_en

    // Descriptor engine
    base_addr[0x220/4] = 0x00000083;  // enable | prefetch | fifo_thresh=8

    // Descriptor AXI monitor (errors only)
    base_addr[0x240/4] = 0x0000000B;  // enable | err_en | timeout_en
    base_addr[0x244/4] = 10000;       // timeout_cycles
    base_addr[0x24C/4] = 0x00000060;  // pkt_mask: errors + timeouts

    // Read/write monitors (errors only)
    base_addr[0x260/4] = 0x0000000B;  // RDMON: enable | err_en | timeout_en
    base_addr[0x280/4] = 0x0000000B;  // WRMON: enable | err_en | timeout_en

    // AXI transfer config
    base_addr[0x2A0/4] = 0x00002020;  // 32 beats read + write

    // Enable performance profiler
    base_addr[0x2B0/4] = 0x00000003;  // enable | elapsed mode
}
```

---

## 11. Troubleshooting Configuration Issues

### Problem: No transfers occurring

**Check:**
1. `cfg_channel_enable[n]` set for channel n?
2. `cfg_sched_enable = 1`?
3. `cfg_desceng_enable = 1`?
4. Global enable set?

---

### Problem: Timeout errors

**Check:**
1. `cfg_sched_timeout_cycles` too small?
2. Memory latency higher than expected?
3. AXI backpressure not handled?

**Solution:**
- Increase timeout: `cfg_sched_timeout_cycles = 20000`
- Disable temporarily: `cfg_sched_timeout_enable = 0`

---

### Problem: MonBus overflow

**Check:**
1. Too many completion packets enabled?
2. Performance packets enabled on all channels?
3. Debug packets enabled?

**Solution:**
- Disable completion: `cfg_*_mon_compl_enable = 0`
- Use channel masks: `cfg_*_mon_compl_mask = 8'h01` (channel 0 only)
- Reduce packet types: `cfg_*_mon_pkt_mask = 16'h0060` (errors + timeouts)

---

### Problem: Low throughput

**Check:**
1. Prefetch disabled?
2. Burst size too small?
3. FIFO threshold too conservative?

**Solution:**
- Enable prefetch: `cfg_desceng_prefetch = 1`
- Increase bursts: `cfg_axi_rd_xfer_beats = 64`
- Increase FIFO: `cfg_desceng_fifo_thresh = 12`

---

## Related Documentation

- **[Register Map](../ch04_registers/register_map.md)** - Complete APB register specification
- **[Clocks and Reset](../ch01_overview/03_clocks_and_reset.md)** - Timing requirements
- **[Programming Guide](../ch05_programming/README.md)** - Software API examples

---

**Last Updated:** 2025-12-01
**Maintained By:** STREAM Architecture Team
