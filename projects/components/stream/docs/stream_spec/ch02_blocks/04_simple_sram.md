# Simple SRAM Specification

**Module:** `simple_sram.sv`
**Location:** `rtl/stream_fub/`
**Source:** Copied from RAPIDS (no changes)

---

## Overview

The Simple SRAM provides dual-port buffering between read and write engines. This module is **identical to RAPIDS** with no modifications.

### Key Features

- Dual-port synchronous SRAM
- Independent read and write ports
- Configurable depth and width
- Chunk enable support (for partial writes)
- Single clock domain

---

## Interface

### Parameters

```systemverilog
parameter int DATA_WIDTH = 512;         // Data width in bits
parameter int ADDR_WIDTH = 10;          // Address width (depth = 2^ADDR_WIDTH)
parameter int CHUNK_WIDTH = 64;         // Chunk width for enables
localparam int NUM_CHUNKS = DATA_WIDTH / CHUNK_WIDTH;
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                        aclk;
input  logic                        aresetn;
```

**Write Port:**
```systemverilog
input  logic                        wr_en;
input  logic [ADDR_WIDTH-1:0]       wr_addr;
input  logic [DATA_WIDTH-1:0]       wr_data;
input  logic [NUM_CHUNKS-1:0]       wr_chunk_en;  // Per-chunk write enable
```

**Read Port:**
```systemverilog
input  logic                        rd_en;
input  logic [ADDR_WIDTH-1:0]       rd_addr;
output logic [DATA_WIDTH-1:0]       rd_data;
```

---

## Operation

### Write Operation

```systemverilog
// Synchronous write with chunk enables
always_ff @(posedge aclk) begin
    if (wr_en) begin
        for (int i = 0; i < NUM_CHUNKS; i++) begin
            if (wr_chunk_en[i]) begin
                mem[wr_addr][(i+1)*CHUNK_WIDTH-1 -: CHUNK_WIDTH] <=
                    wr_data[(i+1)*CHUNK_WIDTH-1 -: CHUNK_WIDTH];
            end
        end
    end
end
```

### Read Operation

```systemverilog
// Synchronous read with registered output
always_ff @(posedge aclk) begin
    if (rd_en) begin
        rd_data <= mem[rd_addr];
    end
end
```

**Read Latency:** 1 cycle (registered output)

---

## Usage in STREAM

### Buffer Decoupling

SRAM decouples read and write engine timing:

```
AXI Read Engine -> SRAM Write Port
                     |
                  [Buffer]
                     |
                  SRAM Read Port -> AXI Write Engine
```

**Benefits:**
- Read and write engines operate at different rates
- Absorbs backpressure from either direction
- Enables asymmetric burst lengths (read=8, write=16)

### Pointer Management

**External logic tracks pointers:**
```systemverilog
// Write pointer (managed by read engine)
logic [ADDR_WIDTH-1:0] wr_ptr;
always_ff @(posedge aclk) begin
    if (axi_read_complete) begin
        wr_ptr <= wr_ptr + beats_read;
    end
end

// Read pointer (managed by write engine)
logic [ADDR_WIDTH-1:0] rd_ptr;
always_ff @(posedge aclk) begin
    if (axi_write_complete) begin
        rd_ptr <= rd_ptr + beats_written;
    end
end

// Space calculation
assign sram_wr_space = SRAM_DEPTH - (wr_ptr - rd_ptr);
assign sram_rd_avail = wr_ptr - rd_ptr;
```

---

## Chunk Enable Usage

**Purpose:** Support partial writes for unaligned transfers.

**Note:** STREAM requires aligned addresses, so chunk enables are typically all '1.

```systemverilog
// STREAM: All chunks enabled (aligned addresses)
assign wr_chunk_en = {NUM_CHUNKS{1'b1}};

// RAPIDS: May have partial chunk enables for alignment
assign wr_chunk_en = alignment_logic(...);
```

---

## Differences from RAPIDS

**None.** This module is identical to RAPIDS simple_sram.sv.

---

## Typical Configuration

**For 512-bit data width:**
```systemverilog
simple_sram #(
    .DATA_WIDTH(512),      // 64 bytes per beat
    .ADDR_WIDTH(10),       // 1024 entries
    .CHUNK_WIDTH(64)       // 8-byte chunks
) u_sram (
    .aclk(aclk),
    .aresetn(aresetn),
    // ... ports
);
```

**Memory size:** 1024 entries   64 bytes = 64 KB

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/fub_tests/sram/`

**Test Scenarios:**
1. Basic write -> read
2. Concurrent read/write (different addresses)
3. Full buffer fill/drain
4. Chunk enable combinations (if used)

**Reference:** RAPIDS simple_sram tests can be reused directly.

---

## Related Documentation

- **RAPIDS Spec:** `projects/components/rapids/docs/rapids_spec/` (if available)
- **Source:** `rtl/stream_fub/simple_sram.sv`

---

**Last Updated:** 2025-10-17
