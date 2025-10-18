# SRAM Controller Specification

**Module:** `sram_controller.sv`
**Location:** `rtl/stream_fub/`
**Status:** To be created

---

## Overview

The SRAM Controller provides a monolithic buffer interface that is internally partitioned across 8 independent channels. Each channel gets its own address space, write/read pointers, and space/availability tracking, while the physical SRAM implementation is abstracted.

### Key Features

- **Monolithic interface:** Single SRAM controller at top level
- **Per-channel partitioning:** 8 independent channel buffers
- **Dedicated pointers:** Each channel has own write/read pointers
- **Space tracking:** Write interface reports free lines available
- **Availability tracking:** Read interface reports ready lines to drain
- **Overflow protection:** Per-channel full/empty detection
- **Physical abstraction:** May use one large SRAM or multiple discrete SRAMs internally

---

## Architecture

### Conceptual Partitioning

```
Monolithic SRAM Controller (64 KB total)
|
|-- Channel 0: Base 0x0000, Size 8 KB (128 lines x 64B)
|-- Channel 1: Base 0x2000, Size 8 KB (128 lines x 64B)
|-- Channel 2: Base 0x4000, Size 8 KB (128 lines x 64B)
|-- Channel 3: Base 0x6000, Size 8 KB (128 lines x 64B)
|-- Channel 4: Base 0x8000, Size 8 KB (128 lines x 64B)
|-- Channel 5: Base 0xA000, Size 8 KB (128 lines x 64B)
|-- Channel 6: Base 0xC000, Size 8 KB (128 lines x 64B)
`-- Channel 7: Base 0xE000, Size 8 KB (128 lines x 64B)
```

### Physical Implementation Options

**Option 1: Single Large SRAM**
- One 1024-line x 512-bit SRAM
- Address decode: `{channel_id[2:0], line_offset[6:0]}`
- Simple, single clock domain

**Option 2: Per-Channel SRAMs**
- Eight 128-line x 512-bit SRAMs
- Independent instances for each channel
- Better for banking/power gating

---

## Interface

### Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;           // Fixed at 8 for STREAM
parameter int DATA_WIDTH = 512;           // Data width in bits
parameter int LINES_PER_CHANNEL = 128;    // Buffer depth per channel
parameter int ADDR_WIDTH = $clog2(LINES_PER_CHANNEL);  // 7 bits
localparam int TOTAL_LINES = NUM_CHANNELS * LINES_PER_CHANNEL;  // 1024
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                        aclk;
input  logic                        aresetn;
```

**Per-Channel Write Interface:**
```systemverilog
// Channel 0-7 write ports
input  logic [NUM_CHANNELS-1:0]              ch_wr_en;
input  logic [NUM_CHANNELS-1:0][DATA_WIDTH-1:0]
                                             ch_wr_data;
output logic [NUM_CHANNELS-1:0][ADDR_WIDTH:0]
                                             ch_wr_free;  // Free lines available
```

**Per-Channel Read Interface:**
```systemverilog
// Channel 0-7 read ports
input  logic [NUM_CHANNELS-1:0]              ch_rd_en;
output logic [NUM_CHANNELS-1:0][DATA_WIDTH-1:0]
                                             ch_rd_data;
output logic [NUM_CHANNELS-1:0][ADDR_WIDTH:0]
                                             ch_rd_avail; // Ready lines to drain
```

**Status Outputs (per channel):**
```systemverilog
output logic [NUM_CHANNELS-1:0]              ch_full;
output logic [NUM_CHANNELS-1:0]              ch_empty;
output logic [NUM_CHANNELS-1:0]              ch_overflow;  // Overflow error
output logic [NUM_CHANNELS-1:0]              ch_underflow; // Underflow error
```

---

## Operation

### Per-Channel Pointer Management

Each channel maintains independent write and read pointers:

```systemverilog
// Per-channel state (replicated 8 times)
logic [ADDR_WIDTH-1:0] r_wr_ptr[NUM_CHANNELS];  // Write pointer
logic [ADDR_WIDTH-1:0] r_rd_ptr[NUM_CHANNELS];  // Read pointer
logic [ADDR_WIDTH:0]   r_count[NUM_CHANNELS];   // Occupancy counter
```

### Write Operation

**For each channel independently:**

```systemverilog
// Channel i write
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_wr_ptr[i] <= '0;
    end else if (ch_wr_en[i]) begin
        if (!ch_full[i]) begin
            // Write to SRAM at channel's partition
            sram_wr_addr = {i[2:0], r_wr_ptr[i]};  // Channel base + offset
            sram_wr_data = ch_wr_data[i];
            sram_wr_en = 1'b1;

            // Advance write pointer (wraps within channel)
            r_wr_ptr[i] <= r_wr_ptr[i] + 1;
            r_count[i] <= r_count[i] + 1;
        end else begin
            ch_overflow[i] <= 1'b1;  // Overflow error
        end
    end
end
```

### Read Operation

**For each channel independently:**

```systemverilog
// Channel i read
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_rd_ptr[i] <= '0;
    end else if (ch_rd_en[i]) begin
        if (!ch_empty[i]) begin
            // Read from SRAM at channel's partition
            sram_rd_addr = {i[2:0], r_rd_ptr[i]};
            sram_rd_en = 1'b1;

            // Advance read pointer (wraps within channel)
            r_rd_ptr[i] <= r_rd_ptr[i] + 1;
            r_count[i] <= r_count[i] - 1;
        end else begin
            ch_underflow[i] <= 1'b1;  // Underflow error
        end
    end
end

// Read data available next cycle (SRAM read latency = 1)
assign ch_rd_data[i] = sram_rd_data_q;
```

### Space Tracking

**Free lines for writes:**

```systemverilog
// Free space available for writes
assign ch_wr_free[i] = LINES_PER_CHANNEL - r_count[i];
```

**Available lines for reads:**

```systemverilog
// Data available for reads
assign ch_rd_avail[i] = r_count[i];
```

### Full/Empty Detection

```systemverilog
// Per-channel status
assign ch_full[i]  = (r_count[i] == LINES_PER_CHANNEL);
assign ch_empty[i] = (r_count[i] == 0);
```

---

## Physical SRAM Instantiation

### Option 1: Single Monolithic SRAM

```systemverilog
// Single 1024-line SRAM shared across all channels
simple_sram #(
    .DATA_WIDTH(512),
    .ADDR_WIDTH(10),  // 1024 lines = 8 channels x 128 lines
    .CHUNK_WIDTH(64)
) u_sram (
    .aclk(aclk),
    .aresetn(aresetn),

    // Write port (arbitrated across channels)
    .wr_en(w_sram_wr_en),
    .wr_addr(w_sram_wr_addr),      // {ch_id[2:0], line_offset[6:0]}
    .wr_data(w_sram_wr_data),
    .wr_chunk_en({8{1'b1}}),       // All chunks enabled

    // Read port (arbitrated across channels)
    .rd_en(w_sram_rd_en),
    .rd_addr(w_sram_rd_addr),      // {ch_id[2:0], line_offset[6:0]}
    .rd_data(w_sram_rd_data)
);
```

### Option 2: Per-Channel SRAMs

```systemverilog
// Replicate 8 times (one per channel)
generate
    for (genvar ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_sram
        simple_sram #(
            .DATA_WIDTH(512),
            .ADDR_WIDTH(7),  // 128 lines per channel
            .CHUNK_WIDTH(64)
        ) u_ch_sram (
            .aclk(aclk),
            .aresetn(aresetn),

            // Write port (dedicated to this channel)
            .wr_en(ch_wr_en[ch] && !ch_full[ch]),
            .wr_addr(r_wr_ptr[ch]),
            .wr_data(ch_wr_data[ch]),
            .wr_chunk_en({8{1'b1}}),

            // Read port (dedicated to this channel)
            .rd_en(ch_rd_en[ch] && !ch_empty[ch]),
            .rd_addr(r_rd_ptr[ch]),
            .rd_data(ch_rd_data[ch])
        );
    end
endgenerate
```

---

## Integration with AXI Engines

### AXI Read Engine -> SRAM Write

```systemverilog
// Read engine writes fetched data to SRAM
axi_read_engine u_rd_engine (
    // ... AXI master interface

    // SRAM controller interface (channel selected by arbiter)
    .sram_wr_en(ch_wr_en[granted_ch_id]),
    .sram_wr_data(ch_wr_data[granted_ch_id]),
    .sram_wr_free(ch_wr_free[granted_ch_id])  // Backpressure signal
);
```

### SRAM Read -> AXI Write Engine

```systemverilog
// Write engine reads data from SRAM
axi_write_engine u_wr_engine (
    // ... AXI master interface

    // SRAM controller interface (channel selected by arbiter)
    .sram_rd_en(ch_rd_en[granted_ch_id]),
    .sram_rd_data(ch_rd_data[granted_ch_id]),
    .sram_rd_avail(ch_rd_avail[granted_ch_id])  // Data available
);
```

---

## Arbiter Integration

The SRAM controller accepts per-channel signals, but the AXI engines are shared resources. Arbiters select which channel has access:

```systemverilog
// Write arbiter: Grants one channel access to AXI read engine
channel_arbiter u_write_arbiter (
    .requests(ch_datard_req),
    .grant_id(wr_grant_ch_id),
    .grant_valid(wr_grant_valid)
);

// Read arbiter: Grants one channel access to AXI write engine
channel_arbiter u_read_arbiter (
    .requests(ch_datawr_req),
    .grant_id(rd_grant_ch_id),
    .grant_valid(rd_grant_valid)
);

// Mux channel signals to engines based on grant
assign engine_sram_wr_en = ch_wr_en[wr_grant_ch_id] && wr_grant_valid;
assign engine_sram_rd_en = ch_rd_en[rd_grant_ch_id] && rd_grant_valid;
```

---

## Differences from RAPIDS

| Feature | RAPIDS | STREAM |
|---------|--------|--------|
| **Partitioning** | Dynamic (credit-based) | Fixed per-channel |
| **Address Space** | Shared with complex allocation | Fixed base per channel |
| **Chunk Support** | Full partial write support | Aligned only (all chunks) |
| **Overflow Handling** | Credit system prevents | Error flag on overflow |
| **Configuration** | Runtime configurable sizes | Compile-time fixed sizes |

---

## Buffer Sizing

**Per-Channel Allocation:**
- 128 lines x 512 bits = 128 lines x 64 bytes = 8 KB per channel
- Total: 8 channels x 8 KB = 64 KB

**Typical Transfer:**
- Descriptor length: 64 beats
- Channel buffer: 128 lines
- Can hold 2x typical descriptor (allows pipelining)

**Overflow Condition:**
- If read engine fills buffer faster than write engine drains
- `ch_wr_free` goes to 0
- Read engine must stall (backpressure)

**Underflow Condition:**
- If write engine tries to read before data available
- `ch_rd_avail` is 0
- Write engine must wait

---

## Error Handling

### Overflow Detection

```systemverilog
// Write when full
always_ff @(posedge aclk) begin
    if (ch_wr_en[i] && ch_full[i]) begin
        ch_overflow[i] <= 1'b1;
        // Generate MonBus error packet
    end
end
```

### Underflow Detection

```systemverilog
// Read when empty
always_ff @(posedge aclk) begin
    if (ch_rd_en[i] && ch_empty[i]) begin
        ch_underflow[i] <= 1'b1;
        // Generate MonBus error packet
    end
end
```

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/fub_tests/sram_controller/`

**Test Scenarios:**
1. Single channel write/read (independent operation)
2. All 8 channels active simultaneously
3. Overflow detection (write to full buffer)
4. Underflow detection (read from empty buffer)
5. Wrap-around pointer behavior
6. Space/availability tracking accuracy
7. Concurrent multi-channel operations

---

## Performance

**Throughput:** 1 write + 1 read per cycle (per channel, if using per-channel SRAMs)

**Latency:**
- Write to SRAM: 1 cycle
- Read from SRAM: 1 cycle (registered output)
- Space/availability updates: Combinational (same cycle)

**Area Estimate:**
- Controller logic: ~200 LUTs per channel x 8 = ~1,600 LUTs
- SRAM: 1024 lines x 512 bits = 64 KB
- Total: ~1,600 LUTs + 64 KB

---

## Related Documentation

- **Simple SRAM:** `fub_07_simple_sram.md` - Physical SRAM primitive
- **AXI Read Engine:** `fub_03_axi_read_engine.md` - SRAM write interface consumer
- **AXI Write Engine:** `fub_04_axi_write_engine.md` - SRAM read interface consumer
- **RAPIDS SRAM Controllers:** `projects/components/rapids/` - Reference implementation

---

**Last Updated:** 2025-10-17
