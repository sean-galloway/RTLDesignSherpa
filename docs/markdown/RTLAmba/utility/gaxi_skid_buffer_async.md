# GAXI Skid Buffer Async Module

## Overview

The `gaxi_skid_buffer_async` module implements an asynchronous skid buffer designed for AXI interfaces operating across different clock domains. This module combines the functionality of a traditional skid buffer with clock domain crossing (CDC) capabilities, offering buffering, flow control, and safe data transfer between asynchronous clock domains.

## Features

- Asynchronous operation across independent write and read clock domains
- Configurable data width and buffer depth
- Parameterizable synchronizer stages for metastability protection
- AXI-compatible valid/ready handshaking
- Both registered and unregistered read data outputs
- Safe clock domain crossing for control and data signals
- Full throughput capability in both clock domains

## Module Parameters

| Parameter | Description | Default |
|-----------|-------------|---------|
| `DATA_WIDTH` | Width of the data bus | 32 |
| `DEPTH` | Buffer depth for the asynchronous FIFO | 2 |
| `N_FLOP_CROSS` | Number of flops in synchronizer chains | 2 |
| `INSTANCE_NAME` | Name used for error reporting | "DEADF1F0" |
| `DW` | Alias for DATA_WIDTH | DATA_WIDTH |

## Interface Ports

### Clock and Reset Signals

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_axi_wr_aclk` | input | 1 | Write domain clock |
| `i_axi_wr_aresetn` | input | 1 | Write domain active-low reset |
| `i_axi_rd_aclk` | input | 1 | Read domain clock |
| `i_axi_rd_aresetn` | input | 1 | Read domain active-low reset |

### Write Interface (Input Side)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_wr_valid` | input | 1 | Write data valid signal |
| `o_wr_ready` | output | 1 | Write ready signal |
| `i_wr_data` | input | DW | Write data input |

### Read Interface (Output Side)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `o_rd_valid` | output | 1 | Read data valid signal |
| `i_rd_ready` | input | 1 | Read ready signal |
| `ow_rd_data` | output | DW | Unregistered read data output |
| `o_rd_data` | output | DW | Registered read data output |

## Architecture and Functional Description

### High-Level Block Diagram

```
                  +------------+     +----------------+
                  |            |     |                |
 i_wr_data ------>|            |     |                |
                  |            |     |                |
 i_wr_valid ----->| Skid Buffer|---->| Async FIFO     |----> ow_rd_data
                  |            |     |                |
 o_wr_ready <-----|            |     |                |----> o_rd_data
                  |            |     |                |
                  +------------+     |                |----> o_rd_valid
                                     |                |
                                     |                |<---- i_rd_ready
                                     |                |
                                     +----------------+
                  
                  Write Clock Domain  |  Read Clock Domain
                                      |
```

### Component Architecture

The `gaxi_skid_buffer_async` module consists of two main components:

1. **Skid Buffer Stage**:
   - Implemented using `gaxi_skid_buffer`
   - Operates entirely in the write clock domain
   - Provides initial buffering and flow control
   - Smooths out traffic before the CDC boundary

2. **Asynchronous FIFO Stage**:
   - Implemented using `gaxi_fifo_async`
   - Handles the actual clock domain crossing
   - Provides additional buffering
   - Ensures safe transfer of data between clock domains

### Data Flow

1. **Write Path**:
   - Data enters through the write interface (`i_wr_valid`, `o_wr_ready`, `i_wr_data`)
   - The skid buffer provides initial buffering in the write clock domain
   - Data is then passed to the async FIFO for clock domain crossing

2. **Clock Domain Crossing**:
   - The async FIFO safely transfers data from write to read clock domain
   - Uses Gray code pointers and multi-flop synchronizers for safe CDC

3. **Read Path**:
   - Data exits through the read interface (`o_rd_valid`, `i_rd_ready`, `o_rd_data`, `ow_rd_data`)
   - Both registered and unregistered read data outputs are provided
   - Flow control is maintained across the clock domain boundary

## Detailed Operation

### Component Instantiation

The module instantiates two key components:

1. **Skid Buffer**:
```verilog
gaxi_skid_buffer #(
    .DATA_WIDTH(DW)
) inst_gaxi_skid_buffer (
    .i_axi_aclk   (i_axi_wr_aclk),
    .i_axi_aresetn(i_axi_wr_aresetn),
    .i_wr_valid   (i_wr_valid),
    .o_wr_ready   (o_wr_ready),
    .i_wr_data    (i_wr_data),
    .o_rd_valid   (r_xfer_valid),
    .i_rd_ready   (r_xfer_ready),
    .o_rd_data    (r_xfer_data),
    .o_rd_count   (),
    .ow_count     ()
);
```

2. **Asynchronous FIFO**:
```verilog
gaxi_fifo_async #(
    .DATA_WIDTH(DW),
    .DEPTH(DEPTH),
    .N_FLOP_CROSS(N_FLOP_CROSS),
    .ALMOST_WR_MARGIN(1),
    .ALMOST_RD_MARGIN(1),
    .INSTANCE_NAME(INSTANCE_NAME)
) inst_gaxi_fifo_async (
    .i_axi_wr_aclk   (i_axi_wr_aclk),
    .i_axi_wr_aresetn(i_axi_wr_aresetn),
    .i_axi_rd_aclk   (i_axi_rd_aclk),
    .i_axi_rd_aresetn(i_axi_rd_aresetn),
    .i_wr_valid      (r_xfer_valid),
    .o_wr_ready      (r_xfer_ready),
    .i_wr_data       (r_xfer_data),
    .i_rd_ready      (i_rd_ready),
    .o_rd_valid      (o_rd_valid),
    .ow_rd_data      (ow_rd_data),
    .o_rd_data       (o_rd_data)
);
```

### Internal Signal Connections

The module uses three internal signals to connect the skid buffer to the async FIFO:

1. **r_xfer_valid**: Valid signal from skid buffer to async FIFO
2. **r_xfer_ready**: Ready signal from async FIFO to skid buffer
3. **r_xfer_data**: Data bus from skid buffer to async FIFO

These connections form the internal handshake between the two components.

### Flow Control Across Clock Domains

Flow control is maintained across the clock domain boundary through the following mechanisms:

1. **Write Side Flow Control**:
   - The skid buffer asserts `o_wr_ready` based on its own capacity and the `r_xfer_ready` signal from the async FIFO
   - This prevents data overflow at the CDC boundary

2. **Read Side Flow Control**:
   - The async FIFO asserts `o_rd_valid` based on data availability in the read clock domain
   - Downstream logic controls data flow using the `i_rd_ready` signal
   - Backpressure is propagated across the clock domain boundary safely

## Usage Considerations

### Parameter Selection

1. **Buffer Depth (`DEPTH`)**:
   - Default is 2, which provides minimal buffering
   - Increase for bursty traffic patterns or large clock frequency differences
   - Higher values consume more resources but improve performance with uneven flow

2. **Synchronizer Stages (`N_FLOP_CROSS`)**:
   - Default is 2, which provides standard metastability protection
   - Increase to 3 or more for high-reliability applications or extreme clock relationships
   - Higher values add latency but improve CDC reliability

3. **Data Width (`DATA_WIDTH`)**:
   - Set based on application requirements
   - Wider data paths consume more resources but support higher bandwidth

### Clock Domain Relationship

The module handles any clock domain relationship:

1. **Frequency Relationship**:
   - Can handle any frequency ratio between write and read clocks
   - No phase relationship required
   - Adapts automatically to the clock relationship

2. **Reset Sequencing**:
   - Both reset signals (`i_axi_wr_aresetn` and `i_axi_rd_aresetn`) should be properly synchronized to their respective clock domains
   - No specific requirement for the relative timing of these resets
   - Each domain handles its own reset independently

### Integration Examples

#### Basic Clock Domain Crossing

```systemverilog
// Instantiate async skid buffer for CDC between clk_fast and clk_slow
gaxi_skid_buffer_async #(
    .DATA_WIDTH(32),       // 32-bit data bus
    .DEPTH(4),             // Buffer depth for async FIFO
    .N_FLOP_CROSS(3)       // Extra synchronizer stages for reliability
) cdc_skid_buffer (
    // Clock and reset
    .i_axi_wr_aclk(clk_fast),
    .i_axi_wr_aresetn(rst_fast_n),
    .i_axi_rd_aclk(clk_slow),
    .i_axi_rd_aresetn(rst_slow_n),
    
    // Write interface
    .i_wr_valid(fast_valid),
    .o_wr_ready(fast_ready),
    .i_wr_data(fast_data),
    
    // Read interface
    .i_rd_ready(slow_ready),
    .o_rd_valid(slow_valid),
    .o_rd_data(slow_data),
    .ow_rd_data() // Unused unregistered output
);
```

#### AXI Stream Interface Crossing

```systemverilog
// For crossing AXI-Stream from fast to slow domain
gaxi_skid_buffer_async #(
    .DATA_WIDTH(DATA_W + 1),  // Data + TLAST
    .DEPTH(8),                // Deeper buffer for burst handling
    .N_FLOP_CROSS(3)          // Extra synchronizer stages
) axis_cdc_buffer (
    // Clock domains
    .i_axi_wr_aclk(fast_clk),
    .i_axi_wr_aresetn(fast_rstn),
    .i_axi_rd_aclk(slow_clk),
    .i_axi_rd_aresetn(slow_rstn),
    
    // Fast domain (write side)
    .i_wr_valid(axis_fast_tvalid),
    .o_wr_ready(axis_fast_tready),
    .i_wr_data({axis_fast_tlast, axis_fast_tdata}),
    
    // Slow domain (read side)
    .i_rd_ready(axis_slow_tready),
    .o_rd_valid(axis_slow_tvalid),
    .o_rd_data({axis_slow_tlast, axis_slow_tdata}),
    .ow_rd_data() // Unused
);
```

## Performance Considerations

### Latency Analysis

1. **Write-to-Read Latency**:
   - Minimum latency is determined by synchronizer depth + FIFO latency
   - Typically 2-5 cycles in the read clock domain after write
   - Latency varies based on clock relationships and parameter settings

2. **Flow Control Latency**:
   - Backpressure propagation takes multiple clock cycles to cross domains
   - The skid buffer helps absorb this latency
   - Proper buffer sizing is critical for maintaining performance

### Throughput Analysis

1. **Maximum Throughput**:
   - In steady state, can achieve full throughput (one transfer per cycle) in each domain
   - Actual throughput limited by the slower of the two clocks
   - Bursty performance determined by buffer depth

2. **Clock Ratio Impact**:
   - Large clock ratio differences benefit from increased buffer depth
   - Fast write to slow read requires deeper buffers
   - Slow write to fast read has less stringent buffering requirements

## Verification Strategies

### Key Test Scenarios

1. **Basic Operation**:
   - Write and read single data values across domains
   - Verify correct data ordering (FIFO behavior)
   - Verify that all data values correctly cross clock domains

2. **Clock Relationship Testing**:
   - Fast write clock, slow read clock
   - Slow write clock, fast read clock
   - Same frequency but asynchronous phase
   - Changing clock frequencies during operation

3. **Flow Control Testing**:
   - Backpressure from read domain
   - Write bursts across domains
   - Read bursts across domains
   - Intermittent valid/ready in both domains

4. **Reset Testing**:
   - Asynchronous reset in write domain only
   - Asynchronous reset in read domain only
   - Simultaneous reset in both domains
   - Reset during active transfers

### Formal Verification Properties

Key properties to verify:

1. **Data Integrity**:
   - All data written is eventually read
   - Data order is preserved
   - No data corruption during CDC

2. **Metastability Protection**:
   - Control signals properly synchronized
   - No timing violations at CDC boundaries

3. **Flow Control Correctness**:
   - No data loss due to overflow
   - No spurious data due to underflow

## Related Modules

- **gaxi_skid_buffer**: Synchronous skid buffer for single clock domain
- **gaxi_fifo_async**: Asynchronous FIFO for clock domain crossing
- **gaxi_fifo_sync**: Synchronous FIFO for single clock domain
- **cdc_handshake**: Alternative CDC mechanism for single-item transfers

## Summary

The `gaxi_skid_buffer_async` module provides a robust solution for transferring data between asynchronous clock domains with integrated buffering and flow control. By combining a skid buffer with an asynchronous FIFO, it offers both high performance and safe clock domain crossing. The module's parameterizable nature allows it to be tailored to specific application requirements, making it suitable for a wide range of AXI interface designs requiring clock domain crossing capabilities.
