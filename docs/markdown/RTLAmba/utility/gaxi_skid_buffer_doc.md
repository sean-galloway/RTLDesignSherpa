# GAXI Skid Buffer Module

## Overview

The `gaxi_skid_buffer` module implements a parameterized skid buffer designed specifically for AXI interfaces. A skid buffer acts as a specialized FIFO that improves timing closure and throughput in pipelined designs by providing buffering capability with flow control. This module offers configurable data width and buffer depth to meet various design requirements.

## Features

- Configurable data width and buffer depth
- Low-latency operation for timing optimization
- AXI-compatible valid/ready handshaking
- Data count output for monitoring
- Support for zero-latency pass-through
- Full throughput capability (one transaction per cycle)
- Simple integration with AXI interfaces

## Module Parameters

| Parameter | Description | Default |
|-----------|-------------|---------|
| `DATA_WIDTH` | Width of the data bus | 32 |
| `DEPTH` | Buffer depth (must be one of {2, 4, 6, 8}) | 2 |
| `DW` | Alias for DATA_WIDTH | DATA_WIDTH |
| `BUF_WIDTH` | Total buffer width (DATA_WIDTH * DEPTH) | DATA_WIDTH * DEPTH |
| `BW` | Alias for BUF_WIDTH | BUF_WIDTH |

## Interface Ports

### Clock and Reset Signals

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_axi_aclk` | input | 1 | System clock |
| `i_axi_aresetn` | input | 1 | Active-low reset |

### Write Interface (Input Side)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_wr_valid` | input | 1 | Write data valid signal |
| `o_wr_ready` | output | 1 | Write ready signal |
| `i_wr_data` | input | DW | Write data input |

### Read Interface (Output Side)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `ow_count` | output | 4 | Current buffer occupancy count |
| `o_rd_valid` | output | 1 | Read data valid signal |
| `i_rd_ready` | input | 1 | Read ready signal |
| `o_rd_count` | output | 4 | Same as ow_count (alternative output) |
| `o_rd_data` | output | DW | Read data output |

## Architecture and Functional Description

### High-Level Block Diagram

```
                  +------------------------+
                  |                        |
 i_wr_data ------>|                        |
                  |                        |
 i_wr_valid ----->|     Skid Buffer        |----> o_rd_data
                  |                        |
 o_wr_ready <-----|   (DEPTH x DW bits)    |----> o_rd_valid
                  |                        |
                  |                        |<---- i_rd_ready
                  |                        |
                  +------------------------+
                           |
                           v
                        ow_count
                        o_rd_count
```

### Skid Buffer Operation

The skid buffer is essentially a small FIFO with special handling for low-latency operation:

1. **Data Storage**:
   - Uses a shift register-like structure to store data
   - New data is inserted at the position indicated by the data count
   - Data is always read from the lowest position (index 0)

2. **Flow Control Logic**:
   - Manages `o_wr_ready` based on available space
   - Manages `o_rd_valid` based on data availability
   - Handles the case where data arrives and departs simultaneously

3. **Count Tracking**:
   - Maintains current buffer occupancy (`r_data_count`)
   - Increments on write without read
   - Decrements on read without write
   - Remains unchanged when both read and write occur

### Data Flow Scenarios

1. **Write Only** (when `w_wr_xfer = 1` and `w_rd_xfer = 0`):
   - New data is stored at position indicated by `r_data_count`
   - `r_data_count` is incremented

2. **Read Only** (when `w_wr_xfer = 0` and `w_rd_xfer = 1`):
   - Data shifts down (all entries move down one position)
   - `r_data_count` is decremented

3. **Simultaneous Read and Write** (when `w_wr_xfer = 1` and `w_rd_xfer = 1`):
   - Data shifts down as in read-only case
   - New data is inserted at position `r_data_count - 1`
   - `r_data_count` remains unchanged

4. **No Transfer** (when `w_wr_xfer = 0` and `w_rd_xfer = 0`):
   - Data and count remain unchanged

## Detailed Operation

### Initialization

Upon reset:
1. All buffer entries are cleared to zero
2. Data count is initialized to zero
3. `o_wr_ready` is deasserted
4. `o_rd_valid` is deasserted

### Write Operation

The module defines write transfer as:
```verilog
assign w_wr_xfer = i_wr_valid & o_wr_ready;
```

Data storage logic:
```verilog
if (w_wr_xfer & ~w_rd_xfer) begin
    // Shift in new data at the highest available position
    r_data[(DW * r_data_count) +: DW] <= i_wr_data;
    r_data_count <= r_data_count + 1;
end
```

### Read Operation

The module defines read transfer as:
```verilog
assign w_rd_xfer = o_rd_valid & i_rd_ready;
```

Data shifting logic:
```verilog
if (~w_wr_xfer & w_rd_xfer) begin
    // Shift out old data
    r_data <= {zeros, r_data[BUF_WIDTH-1:DW]};
    r_data_count <= r_data_count - 1;
end
```

### Ready/Valid Generation

The module uses sophisticated logic to generate the ready and valid signals:

```verilog
always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
    if (~i_axi_aresetn) begin
        o_wr_ready <= 1'b0;
        o_rd_valid <= 1'b0;
    end else begin
        o_wr_ready <= (32'(r_data_count) <= DEPTH-2) ||
                        (32'(r_data_count) == DEPTH-1 && (~w_wr_xfer || w_rd_xfer)) ||
                        (32'(r_data_count) == DEPTH && w_rd_xfer);

        o_rd_valid <= (r_data_count >= 2) ||
                        (r_data_count == 4'b0001 && (~w_rd_xfer || w_wr_xfer)) ||
                        (r_data_count == 4'b0000 && w_wr_xfer);
    end
end
```

These expressions ensure:
1. Write is accepted when there's space or when reads are occurring
2. Valid is asserted when there's data or when new data is arriving

### Zero-Latency Pass-Through

A key feature of the skid buffer is its ability to pass data through with zero latency when the buffer is empty:

- When `r_data_count = 0` and both `i_wr_valid` and `i_rd_ready` are high, data passes directly from input to output
- The `o_rd_valid` signal immediately reflects the presence of input data when the buffer is empty

## Usage Considerations

### Buffer Depth Selection

The `DEPTH` parameter must be one of {2, 4, 6, 8}:

1. **DEPTH=2**:
   - Minimal buffering (1 or 2 entries depending on flow control)
   - Suitable for simple pipeline stages
   - Lowest resource usage

2. **DEPTH=4**:
   - Moderate buffering for absorbing short bursts
   - Good balance of performance and resource usage

3. **DEPTH=6 or DEPTH=8**:
   - Higher buffering capacity for longer bursts
   - Useful when upstream or downstream may stall for multiple cycles

### Timing Considerations

1. **Critical Paths**:
   - The data path is typically not critical due to the register stage
   - The valid/ready logic may be critical, especially for zero-latency pass-through

2. **Clock Frequency Impact**:
   - Higher clock frequencies may benefit from larger DEPTH
   - The skid buffer helps improve timing closure at high frequencies

### Flow Control Behavior

1. **Backpressure Handling**:
   - When downstream asserts backpressure (`i_rd_ready=0`), the buffer begins filling
   - Once full, the buffer asserts backpressure upstream (`o_wr_ready=0`)
   - When downstream releases backpressure, the buffer begins emptying

2. **Sustained Throughput**:
   - The buffer can sustain full throughput (one transfer per cycle) indefinitely
   - Even with intermittent downstream stalls, throughput can be maintained

### Integration Examples

#### Basic Pipeline Stage

```systemverilog
// Instantiate skid buffer as a pipeline stage
gaxi_skid_buffer #(
    .DATA_WIDTH(32),   // 32-bit data
    .DEPTH(2)          // Minimal buffering
) pipeline_stage (
    // Clock and reset
    .i_axi_aclk(system_clk),
    .i_axi_aresetn(system_rst_n),
    
    // Write interface (from upstream)
    .i_wr_valid(upstream_valid),
    .o_wr_ready(upstream_ready),
    .i_wr_data(upstream_data),
    
    // Read interface (to downstream)
    .o_rd_valid(downstream_valid),
    .i_rd_ready(downstream_ready),
    .o_rd_data(downstream_data),
    .ow_count(buffer_count),
    .o_rd_count()  // Unused alternative count output
);
```

#### AXI Stream Data Path Element

```systemverilog
// Instantiate skid buffer in AXI Stream data path
gaxi_skid_buffer #(
    .DATA_WIDTH(DATA_W + 2),  // Data + TLAST + TUSER
    .DEPTH(4)                 // More buffering for bursts
) axis_skid_buffer (
    // Clock and reset
    .i_axi_aclk(axi_clk),
    .i_axi_aresetn(axi_rstn),
    
    // Write interface (from source)
    .i_wr_valid(axis_src_tvalid),
    .o_wr_ready(axis_src_tready),
    .i_wr_data({axis_src_tuser, axis_src_tlast, axis_src_tdata}),
    
    // Read interface (to destination)
    .i_rd_ready(axis_dst_tready),
    .o_rd_valid(axis_dst_tvalid),
    .o_rd_data({axis_dst_tuser, axis_dst_tlast, axis_dst_tdata}),
    .ow_count(skid_count),
    .o_rd_count()  // Unused
);
```

## Implementation Details

### Buffer Data Structure

The module stores data in a single large register:

```verilog
logic [BW-1:0] r_data;
```

This is treated as a packed array of data elements, each of width `DATA_WIDTH`. New data is inserted at the position calculated from the current count:

```verilog
r_data[(DW * r_data_count) +: DW] <= i_wr_data;
```

### Count Tracking

A 4-bit counter tracks the current buffer occupancy:

```verilog
logic [3:0] r_data_count;
```

This counter is manipulated based on transfer conditions:
- Incremented on write without read
- Decremented on read without write
- Unchanged on simultaneous read and write or no transfer

### Data Shifting

When a read occurs, data is shifted down:

```verilog
r_data <= {zeros, r_data[BUF_WIDTH-1:DW]};
```

This moves all entries down one position, effectively removing the entry at position 0.

### Output Data Selection

The output data is always taken from the first entry:

```verilog
assign o_rd_data = r_data[DW-1:0];
```

## Performance Optimization

### Low-Latency Path

The skid buffer is designed to offer a low-latency path when empty:

1. **Empty Buffer Behavior**:
   - When `r_data_count = 0`, incoming data can pass through immediately
   - `o_rd_valid` is asserted based on `i_wr_valid` when empty

2. **Ready Generation**:
   - `o_wr_ready` is typically high unless the buffer is near full
   - This allows upstream to continue sending data with minimal stalling

### Full Throughput Support

The buffer supports full throughput in steady state:

1. **Simultaneous Read/Write Handling**:
   - Special case for handling simultaneous read and write
   - Ensures buffer count remains stable during full throughput

2. **Buffer Depth Impact**:
   - Larger buffer depths can better absorb temporary imbalances
   - This helps maintain throughput despite downstream stalls

## Verification Strategies

### Key Test Scenarios

1. **Basic Operation**:
   - Write followed by read
   - Simultaneous write and read
   - Zero-latency pass-through when empty

2. **Boundary Conditions**:
   - Empty to not-empty transition
   - Not-full to full transition
   - Full to not-full transition
   - Not-empty to empty transition

3. **Flow Control Testing**:
   - Upstream valid without downstream ready
   - Downstream ready without upstream valid
   - Intermittent downstream ready with continuous upstream valid

4. **Stress Testing**:
   - Fill completely, then empty completely
   - Alternating read/write patterns
   - Random valid/ready patterns

### Assertion-Based Verification

Key properties to verify:

1. **Data Integrity**:
   - Data passes through unchanged
   - Data order is preserved (FIFO behavior)

2. **Count Accuracy**:
   - Count correctly reflects buffer occupancy
   - Count updates properly for all transfer scenarios

3. **Flow Control Correctness**:
   - `o_wr_ready` deasserts when buffer is full
   - `o_rd_valid` deasserts when buffer is empty

## Related Modules

- **gaxi_fifo_sync**: Synchronous FIFO for larger buffer requirements
- **gaxi_fifo_async**: Asynchronous FIFO for clock domain crossing
- **gaxi_skid_buffer_async**: Asynchronous skid buffer combining skid buffer and CDC capabilities

## Summary

The `gaxi_skid_buffer` module provides a flexible, parameterizable skid buffer designed for AXI interfaces. With configurable data width and buffer depth, it offers efficient buffering with flow control capabilities. The module supports full throughput operation with simultaneous read and write, while also providing zero-latency pass-through when empty. These features make it ideal for pipelined designs where timing closure and throughput are critical concerns.
