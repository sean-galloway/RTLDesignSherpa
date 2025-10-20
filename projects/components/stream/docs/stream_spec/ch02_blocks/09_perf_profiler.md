# Performance Profiler Specification

**Module:** `perf_profiler.sv`
**Location:** `rtl/stream_fub/`
**Source:** New for STREAM

---

## Overview

The Performance Profiler captures timing information for channel activity to enable performance analysis and bottleneck identification. It monitors channel idle signals and records timestamps or elapsed times into a FIFO for later retrieval via APB registers.

### Key Features

- Dual-mode profiling: timestamp mode or elapsed time mode
- 32-bit free-running counter for timing reference
- 256-entry FIFO for buffering performance events
- Per-channel tracking (up to 8 channels)
- Channel ID tagging for multi-channel identification
- Priority encoder for simultaneous events
- Two-register APB read interface (36-bit data over 32-bit bus)

---

## Interface

### Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;              // Number of channels to monitor
parameter int CHANNEL_WIDTH = $clog2(NUM_CHANNELS);
parameter int TIMESTAMP_WIDTH = 32;          // Timestamp counter width
parameter int FIFO_DEPTH = 256;              // Performance event FIFO depth
parameter int FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH);
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                    clk;
input  logic                    rst_n;
```

**Channel Idle Signals (from Schedulers):**
```systemverilog
input  logic [NUM_CHANNELS-1:0] channel_idle;  // Idle status per channel
                                                // 1 = idle, 0 = active
```

**Configuration Interface:**
```systemverilog
input  logic                    cfg_enable;    // Enable profiling
input  logic                    cfg_mode;      // 0=timestamp, 1=elapsed
input  logic                    cfg_clear;     // Clear FIFO and counters
```

**FIFO Read Interface (to APB Config Space):**
```systemverilog
input  logic                    perf_fifo_rd;        // Read strobe (pops FIFO)
output logic [31:0]             perf_fifo_data_low;  // [31:0] timestamp/elapsed
output logic [31:0]             perf_fifo_data_high; // {28'b0, event_type, channel_id[2:0]}
output logic                    perf_fifo_empty;     // FIFO empty flag
output logic                    perf_fifo_full;      // FIFO full flag
output logic [15:0]             perf_fifo_count;     // Number of entries
```

---

## Profiling Modes

### Mode 0: TIMESTAMP_MODE (More Flexible)

**Operation:**
- Records timestamp when channel transitions idle → active (start event)
- Records timestamp when channel transitions active → idle (end event)
- Software calculates elapsed time from timestamp pairs
- Simpler hardware, more flexible post-processing

**FIFO Entry Format:**
- `perf_fifo_data_low[31:0]`: Timestamp (cycles)
- `perf_fifo_data_high[3]`: Event type (0=start, 1=end)
- `perf_fifo_data_high[2:0]`: Channel ID (0-7)

**Software Processing:**
```c
// Read two FIFO entries for start/end pair
uint32_t timestamp_start = read_perf_fifo();  // event_type=0
uint32_t timestamp_end   = read_perf_fifo();  // event_type=1
uint32_t elapsed = timestamp_end - timestamp_start;
```

### Mode 1: ELAPSED_MODE (Simpler Software)

**Operation:**
- Captures timestamp when channel becomes active (idle falls)
- Computes elapsed time when channel returns to idle (idle rises)
- Records elapsed time directly in FIFO
- Hardware calculates duration, simpler software

**FIFO Entry Format:**
- `perf_fifo_data_low[31:0]`: Elapsed time (cycles)
- `perf_fifo_data_high[3]`: Always 1 (end event)
- `perf_fifo_data_high[2:0]`: Channel ID (0-7)

**Software Processing:**
```c
// Read single FIFO entry for complete measurement
uint32_t elapsed = read_perf_fifo();  // Direct elapsed time
```

---

## Two-Register Read Interface

The profiler stores 36-bit entries (32-bit timestamp/elapsed + 4-bit metadata) in the FIFO. Since APB registers are 32 bits wide, the data is split across two registers with atomic read semantics.

### Read Sequence

**Hardware Behavior:**
1. **Read PERF_FIFO_DATA_LOW (address 0xXXX):**
   - APB slave asserts `perf_fifo_rd` for one cycle
   - FIFO pops and provides 36-bit data
   - Data is latched into internal register
   - APB returns `[31:0]` (timestamp or elapsed time)

2. **Read PERF_FIFO_DATA_HIGH (address 0xXXX+4):**
   - APB returns `{28'b0, [35:32]}` from latched data
   - No FIFO pop occurs (reads previously latched data)

**Software Example:**
```c
// APB register addresses (example)
#define PERF_FIFO_DATA_LOW   0x200
#define PERF_FIFO_DATA_HIGH  0x204
#define PERF_FIFO_STATUS     0x208

// Check if data available
if (!(read_apb(PERF_FIFO_STATUS) & FIFO_EMPTY)) {
    // Read 36-bit entry atomically
    uint32_t timestamp = read_apb(PERF_FIFO_DATA_LOW);  // Pops FIFO, latches data
    uint32_t metadata  = read_apb(PERF_FIFO_DATA_HIGH); // Reads latched data

    // Parse metadata
    uint8_t channel_id = metadata & 0x7;       // Bits [2:0]
    uint8_t event_type = (metadata >> 3) & 1;  // Bit [3]

    // Process based on mode
    if (cfg_mode == TIMESTAMP_MODE) {
        if (event_type == 0) {
            // Start event
            start_times[channel_id] = timestamp;
        } else {
            // End event - calculate elapsed
            uint32_t elapsed = timestamp - start_times[channel_id];
            printf("Channel %d: %u cycles\n", channel_id, elapsed);
        }
    } else {
        // ELAPSED_MODE - timestamp is already elapsed time
        printf("Channel %d: %u cycles\n", channel_id, timestamp);
    }
}
```

---

## Operation Details

### Free-Running Timestamp Counter

- 32-bit counter increments every clock cycle when profiling enabled
- Provides global timing reference for all measurements
- Wraps around at 2^32 - 1 (software must handle rollover)
- Can be cleared via `cfg_clear`

**Example:**
- Clock frequency: 100 MHz
- Counter range: 0 to 4,294,967,295
- Maximum time: ~42.9 seconds before rollover
- Software should handle wrap-around in timestamp calculations

### Edge Detection

**Falling Edge (Idle → Active):**
- Channel starts operation
- In TIMESTAMP_MODE: Records timestamp with event_type=0 (start)
- In ELAPSED_MODE: Records start time internally, no FIFO write

**Rising Edge (Active → Idle):**
- Channel completes operation
- In TIMESTAMP_MODE: Records timestamp with event_type=1 (end)
- In ELAPSED_MODE: Computes elapsed time, writes to FIFO

### Multi-Channel Priority Encoder

When multiple channels have events simultaneously (rare but possible):
- Priority encoder selects lowest channel number first
- One event processed per cycle
- Remaining events captured in subsequent cycles

**Example:**
```
Cycle N:   Channels 0, 3, 5 all transition
           → Process Channel 0 event, push to FIFO
Cycle N+1: Channels 3, 5 still pending
           → Process Channel 3 event, push to FIFO
Cycle N+2: Channel 5 still pending
           → Process Channel 5 event, push to FIFO
```

---

## Configuration

### Enable Profiling

```c
// Enable profiler in timestamp mode
write_apb(PERF_CTRL, (1 << ENABLE_BIT) | (0 << MODE_BIT));

// Enable profiler in elapsed mode
write_apb(PERF_CTRL, (1 << ENABLE_BIT) | (1 << MODE_BIT));
```

### Clear FIFO and Counters

```c
// Clear all profiler state
write_apb(PERF_CTRL, (1 << CLEAR_BIT));
// Wait one cycle, then clear bit
write_apb(PERF_CTRL, 0);
```

### Read FIFO Entries

```c
void read_all_perf_events(void) {
    uint32_t status;

    // Poll until FIFO empty
    while ((status = read_apb(PERF_FIFO_STATUS)) & FIFO_EMPTY_BIT) {
        // Read 36-bit entry (two registers)
        uint32_t data_low  = read_apb(PERF_FIFO_DATA_LOW);
        uint32_t data_high = read_apb(PERF_FIFO_DATA_HIGH);

        // Parse and process
        uint8_t channel_id = data_high & 0x7;
        uint8_t event_type = (data_high >> 3) & 1;

        printf("Channel %d: %s at %u\n",
               channel_id,
               event_type ? "END" : "START",
               data_low);
    }
}
```

---

## FIFO Behavior

### Buffering

- 256-entry FIFO (configurable via `FIFO_DEPTH` parameter)
- Each entry: 36 bits (32-bit timestamp/elapsed + 4-bit metadata)
- Status outputs: `perf_fifo_empty`, `perf_fifo_full`, `perf_fifo_count`

### Full Handling

**When FIFO full:**
- New events are **DROPPED** (no backpressure to schedulers)
- Profiler continues tracking but cannot record new events
- Software should poll frequently to prevent loss

**Best Practices:**
1. Monitor `perf_fifo_count` to detect near-full conditions
2. Enable interrupt on FIFO half-full threshold (future enhancement)
3. Poll FIFO regularly during active profiling
4. Increase `FIFO_DEPTH` parameter if loss occurs

---

## Integration Example

```systemverilog
perf_profiler #(
    .NUM_CHANNELS(8),
    .TIMESTAMP_WIDTH(32),
    .FIFO_DEPTH(256)
) u_perf_profiler (
    // Clock and Reset
    .clk                  (aclk),
    .rst_n                (aresetn),

    // Channel idle signals from schedulers
    .channel_idle         ({sched7_idle, sched6_idle, ..., sched0_idle}),

    // Configuration from APB registers
    .cfg_enable           (perf_ctrl_reg[0]),
    .cfg_mode             (perf_ctrl_reg[1]),
    .cfg_clear            (perf_ctrl_reg[2]),

    // FIFO read interface (connect to APB slave)
    .perf_fifo_rd         (perf_fifo_rd_strobe),  // Triggered by LOW register read
    .perf_fifo_data_low   (perf_fifo_data_low),   // Maps to APB register 0x200
    .perf_fifo_data_high  (perf_fifo_data_high),  // Maps to APB register 0x204
    .perf_fifo_empty      (perf_fifo_empty),      // Status register bit
    .perf_fifo_full       (perf_fifo_full),       // Status register bit
    .perf_fifo_count      (perf_fifo_count)       // Status register [15:0]
);
```

---

## APB Register Map Example

Suggested APB register mapping (to be integrated into `stream_regs.rdl`):

| Address | Register | Access | Description |
|---------|----------|--------|-------------|
| 0x1F0 | PERF_CTRL | RW | [2]=clear, [1]=mode, [0]=enable |
| 0x1F4 | PERF_STATUS | RO | [31:16]=count, [1]=full, [0]=empty |
| 0x1F8 | PERF_FIFO_DATA_LOW | RO | [31:0] timestamp/elapsed (pops FIFO) |
| 0x1FC | PERF_FIFO_DATA_HIGH | RO | {28'b0, event_type, channel_id[2:0]} |

---

## Use Cases

### 1. Identify Busy Channels

Monitor which channels spend most time active (not idle):

```c
// Enable elapsed mode profiling
enable_profiler(ELAPSED_MODE);

// Run workload for 1 second
sleep(1);

// Read and accumulate per-channel totals
uint32_t channel_busy_time[8] = {0};
while (!fifo_empty()) {
    uint32_t elapsed = read_perf_fifo_low();
    uint32_t meta    = read_perf_fifo_high();
    uint8_t ch = meta & 0x7;
    channel_busy_time[ch] += elapsed;
}

// Report busiest channels
for (int ch = 0; ch < 8; ch++) {
    printf("Channel %d: %.1f%% busy\n",
           ch,
           100.0 * channel_busy_time[ch] / total_cycles);
}
```

### 2. Measure Transfer Latency

Measure time from descriptor kick-off to completion:

```c
// Enable timestamp mode
enable_profiler(TIMESTAMP_MODE);

// Kick off descriptor
kick_channel(0);

// Wait for completion
while (!channel_done(0)) {
    // Poll FIFO for events
    if (!fifo_empty()) {
        uint32_t timestamp = read_perf_fifo_low();
        uint32_t meta      = read_perf_fifo_high();
        uint8_t ch = meta & 0x7;
        uint8_t type = (meta >> 3) & 1;

        if (ch == 0 && type == 0) {
            start_time = timestamp;
        } else if (ch == 0 && type == 1) {
            end_time = timestamp;
            printf("Transfer latency: %u cycles\n", end_time - start_time);
        }
    }
}
```

### 3. Detect Performance Bottlenecks

Identify channels with unexpectedly long active periods:

```c
#define EXPECTED_MAX_CYCLES 10000

while (!fifo_empty()) {
    uint32_t elapsed = read_perf_fifo_low();
    uint32_t meta    = read_perf_fifo_high();
    uint8_t ch = meta & 0x7;

    if (elapsed > EXPECTED_MAX_CYCLES) {
        printf("WARNING: Channel %d took %u cycles (expected < %u)\n",
               ch, elapsed, EXPECTED_MAX_CYCLES);
    }
}
```

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/fub_tests/perf_profiler/`

**Test Scenarios:**
1. Timestamp mode - single channel
2. Timestamp mode - multiple channels
3. Elapsed mode - single channel
4. Elapsed mode - multiple channels
5. FIFO full handling (event dropping)
6. Simultaneous channel transitions (priority encoder)
7. Counter rollover handling
8. Two-register read sequence (atomic access)

---

## Formal Verification

The module includes formal assertions (enabled with `FORMAL` define):

**timestamp_monotonic:**
- Timestamp counter never decreases (unless clear or rollover)
- Ensures timing measurements are valid

**elapsed_requires_active:**
- In elapsed mode, channel must be active before recording elapsed time
- Prevents spurious elapsed time entries

**fifo_write_conditions:**
- FIFO write only when enabled and event detected
- Ensures all FIFO entries are valid events

---

## Related Documentation

- **Source:** `rtl/stream_fub/perf_profiler.sv`
- **Integration:** `rtl/stream_macro/stream_top.sv`
- **Registers:** `regs/stream_regs.rdl` (PeakRDL specification)
- **FIFO:** `rtl/amba/gaxi/gaxi_fifo_sync.sv` (underlying FIFO implementation)

---

**Last Updated:** 2025-10-20
