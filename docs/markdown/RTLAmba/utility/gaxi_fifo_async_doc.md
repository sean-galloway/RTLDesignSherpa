# GAXI Asynchronous FIFO Module

## Overview

The `gaxi_fifo_async` module implements a parameterized asynchronous FIFO (First In, First Out) buffer designed for safely crossing clock domains in AXI interfaces. This robust implementation supports configurable data width and depth while providing proper clock domain crossing (CDC) protection through Gray code pointers and multi-flop synchronizers.

## Features

- Asynchronous operation across independent clock domains
- Parameterizable data width and FIFO depth
- Gray code-based pointer synchronization for metastability protection
- Configurable synchronizer stages for additional protection
- Full and empty status signals
- Almost-full and almost-empty indicators with configurable margins
- Error detection for underflow and overflow conditions
- Compatible with AXI interface timing requirements

## Module Parameters

| Parameter | Description | Default |
|-----------|-------------|---------|
| `DATA_WIDTH` | Width of the data bus | 8 |
| `DEPTH` | FIFO depth (must be an even number) | 10 |
| `N_FLOP_CROSS` | Number of flops in synchronizer chains | 2 |
| `ALMOST_WR_MARGIN` | Margin for almost-full indication | 1 |
| `ALMOST_RD_MARGIN` | Margin for almost-empty indication | 1 |
| `INSTANCE_NAME` | Name used for error reporting | "DEADF1F0" |
| `DW` | Alias for DATA_WIDTH | DATA_WIDTH |
| `D` | Alias for DEPTH | DEPTH |
| `AW` | Address width, calculated as log2(DEPTH) | $clog2(DEPTH) |
| `JCW` | Johnson Counter Width | DEPTH |
| `N` | Alias for N_FLOP_CROSS | N_FLOP_CROSS |

## Interface Ports

### Clock and Reset Signals

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_axi_wr_aclk` | input | 1 | Write domain clock |
| `i_axi_wr_aresetn` | input | 1 | Write domain active-low reset |
| `i_axi_rd_aclk` | input | 1 | Read domain clock |
| `i_axi_rd_aresetn` | input | 1 | Read domain active-low reset |

### Write Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_wr_valid` | input | 1 | Write data valid signal |
| `o_wr_ready` | output | 1 | Write ready (not full) signal |
| `i_wr_data` | input | DW | Write data input |

### Read Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_rd_ready` | input | 1 | Downstream ready to accept data |
| `o_rd_valid` | output | 1 | Read data valid (not empty) signal |
| `ow_rd_data` | output | DW | Unregistered read data output |
| `o_rd_data` | output | DW | Registered read data output |

## Architecture and Functional Description

### High-Level Block Diagram

```
                  +-------------------------+
                  |                         |
 i_wr_data ------>|                         |
                  |                         |
 i_wr_valid ----->|     Memory Array        |----> ow_rd_data
                  |                         |
 o_wr_ready <-----|    (DEPTH x DW bits)    |----> o_rd_data
                  |                         |
                  |                         |----> o_rd_valid
                  |                         |
 i_rd_ready ----->|                         |
                  |                         |
                  +-------------------------+
                       |             |
                       |             |
                  +----v----+  +-----v----+
                  |         |  |          |
                  | Write   |  | Read     |
                  | Pointer |  | Pointer  |
                  |         |  |          |
                  +----+----+  +------+---+
                       |              |
                  +----v----+   +-----v----+
                  |Johnson  |   |Johnson   |
                  |Gray     |   |Gray      |
                  |Counter  |   |Counter   |
                  +---------+   +----------+
                       |              |
                  +----v----+   +-----v----+
                  |N-Stage  |   |N-Stage   |
                  |Sync     |   |Sync      |
                  |         |   |          |
                  +---------+   +----------+
                       |              |
                  +----v----+   +-----v----+
                  |Gray to  |   |Gray to   |
                  |Binary   |   |Binary    |
                  |         |   |          |
                  +---------+   +----------+
                       |              |
                       v              v
                 To Read Domain    To Write Domain
```

### Core Components

1. **Memory Array**:
   - A dual-port memory array of size DEPTH × DATA_WIDTH
   - Write port clocked by write domain clock
   - Read port accessed asynchronously for `ow_rd_data` or clocked by read domain for `o_rd_data`

2. **Binary Counters**:
   - Write pointer counter tracking write position
   - Read pointer counter tracking read position
   - Both counters wrap around when reaching DEPTH

3. **Johnson Counters**:
   - Convert binary counters to Gray code format
   - Ensure only one bit changes at a time for safe clock domain crossing

4. **Multi-Flop Synchronizers**:
   - N-stage synchronizer chains for crossing clock domains
   - Read pointer Gray code synchronized to write domain
   - Write pointer Gray code synchronized to read domain

5. **Gray-to-Binary Converters**:
   - Convert synchronized Gray code pointers back to binary
   - Provide proper binary address and count values in destination domains

6. **FIFO Control**:
   - Generates full, empty, almost-full, and almost-empty signals
   - Manages count and status based on synchronized pointers

### Clock Domain Crossing Mechanism

The module uses a robust Gray code-based pointer synchronization scheme:

1. **Binary Counter Progression**:
   - Binary counters track actual memory addresses
   - MSB used to detect wrap-around for full/empty calculation

2. **Gray Code Transformation**:
   - Johnson counters transform binary values to Gray code
   - Ensures only one bit changes at a time during transitions

3. **Multi-Stage Synchronization**:
   - Gray code pointers pass through N-stage synchronizers
   - Each stage adds protection against metastability

4. **Pointer Comparison**:
   - Synchronized pointers compared to determine FIFO status
   - Full/empty conditions properly detected across domains

### Data Flow

1. **Write Operation**:
   - When `i_wr_valid` and `o_wr_ready` are both high, a write occurs
   - Data is written to memory at the current write pointer
   - Write pointer advances

2. **Read Operation**:
   - When `o_rd_valid` and `i_rd_ready` are both high, a read occurs
   - Data is read from memory at the current read pointer
   - Read pointer advances

3. **Status Generation**:
   - Full status determined by comparing synchronized read pointer with write pointer
   - Empty status determined by comparing synchronized write pointer with read pointer
   - Almost-full/empty determined by programmable margins

## Detailed Operation

### Initialization

Upon reset:
1. All pointers are cleared to zero
2. FIFO is marked as empty in the read domain
3. FIFO is marked as not full in the write domain
4. No reads or writes allowed during reset

### Write Domain Operation

The write domain clock (`i_axi_wr_aclk`) controls:
1. Write pointer counter increment
2. Data storage into memory array
3. Full status generation

A write operation occurs when:
```verilog
w_write = i_wr_valid && o_wr_ready;
```

When a write occurs:
1. Current write data is stored at the memory location addressed by `r_wr_addr`
2. The write pointer advances
3. The Johnson counter also advances, generating a new Gray code value

### Read Domain Operation

The read domain clock (`i_axi_rd_aclk`) controls:
1. Read pointer counter increment
2. Data retrieval from memory array (for registered output)
3. Empty status generation

A read operation occurs when:
```verilog
w_read = o_rd_valid && i_rd_ready;
```

When a read occurs:
1. Data is read from memory at the location addressed by `r_rd_addr`
2. The read pointer advances
3. The Johnson counter also advances, generating a new Gray code value

### Full and Empty Detection

The `fifo_control` module handles full and empty detection:

1. **Full Detection**:
   - Occurs in write domain
   - Compares local write pointer with synchronized read pointer
   - Full when pointers match on all address bits and MSB differs

2. **Empty Detection**:
   - Occurs in read domain
   - Compares local read pointer with synchronized write pointer
   - Empty when pointers match on all bits

3. **Almost-Full Detection**:
   - Based on remaining slots before full
   - Determined by programmable margin `ALMOST_WR_MARGIN`

4. **Almost-Empty Detection**:
   - Based on available data before empty
   - Determined by programmable margin `ALMOST_RD_MARGIN`

### Error Detection

The module includes diagnostic code to detect:
1. Writes while full
2. Reads while empty

These errors are reported with timestamp information during simulation.

## Usage Considerations

### Reset Sequencing

Both reset signals (`i_axi_wr_aresetn` and `i_axi_rd_aresetn`) should be properly synchronized to their respective clock domains. There is no specific requirement for the relative timing of these resets, but both domains should complete their reset sequence before normal operation begins.

### Parameter Selection

1. **FIFO Depth (`DEPTH`)**:
   - Should be an even number for proper operation
   - Must be large enough to accommodate the maximum expected data burst
   - Consider clock frequency differences when sizing

2. **Synchronizer Stages (`N_FLOP_CROSS`)**:
   - Default of 2 is sufficient for most applications
   - Increase for very asynchronous clocks or high reliability requirements
   - Higher values increase latency

3. **Almost-Full/Empty Margins**:
   - Set based on application flow control needs
   - Larger margins provide more time for the receiving system to respond

### Critical Timing Paths

1. **Memory Write Path**:
   - From write valid/data to memory write
   - Critical in high-frequency write domains

2. **Gray Code Synchronization**:
   - Metastability-hardened path
   - Usually not timing-critical due to multiple synchronization stages

3. **Status Generation**:
   - Full/empty status generation paths
   - Can be critical for back-pressure timing

### Integration Examples

#### Basic Usage

```systemverilog
// Instantiate async FIFO for CDC between clk_fast and clk_slow
gaxi_fifo_async #(
    .DATA_WIDTH(32),       // 32-bit data bus
    .DEPTH(16),            // 16 entries deep
    .N_FLOP_CROSS(3)       // Extra safety with 3 flops
) cdc_fifo (
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
    .ow_rd_data()  // Unused unregistered output
);
```

#### AXI Stream Interface Crossing

```systemverilog
// For crossing AXI-Stream from fast to slow domain
gaxi_fifo_async #(
    .DATA_WIDTH(DATA_W + 1),  // Data + TLAST
    .DEPTH(32),               // Deeper FIFO for burst handling
    .ALMOST_WR_MARGIN(4)      // Early back-pressure
) axis_cdc_fifo (
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
    .ow_rd_data()  // Unused
);
```

## Implementation Details

### Memory Implementation

The FIFO memory is implemented as an array of flip-flops:

```systemverilog
// The flop storage registers
logic [DW-1:0] r_mem[0:((1<<AW)-1)];
```

Data is written using a simple always block:

```systemverilog
// Memory Flops
always_ff @(posedge i_axi_wr_aclk) begin
    if (w_write && !r_wr_full) r_mem[r_wr_addr] <= i_wr_data;
end
```

The registered output adds an extra pipeline stage:

```systemverilog
// Flop stage for the flopped data
always_ff @(posedge i_axi_rd_aclk or negedge i_axi_rd_aresetn) begin
    if (!i_axi_rd_aresetn) o_rd_data <= 'b0;
    else o_rd_data <= r_mem[r_rd_addr];
end
```

### Pointer Synchronization

The module uses Johnson counters for generating Gray code and N-stage synchronizers for safe clock domain crossing:

```systemverilog
// Johnson counter for write pointer Gray code
counter_johnson #(
    .WIDTH(JCW)
) wr_ptr_counter_gray (
    .i_clk(i_axi_wr_aclk),
    .i_rst_n(i_axi_wr_aresetn),
    .i_enable(w_write && !r_wr_full),
    .o_counter_gray(r_wr_ptr_gray)
);

// N-stage synchronizer for write pointer
glitch_free_n_dff_arn #(
    .FLOP_COUNT(N_FLOP_CROSS),
    .WIDTH(JCW)
) wr_ptr_gray_cross_inst (
    .o_q(r_rdom_wr_ptr_gray),
    .i_d(r_wr_ptr_gray),
    .i_clk(i_axi_rd_aclk),
    .i_rst_n(i_axi_rd_aresetn)
);
```

### FIFO Control Logic

The FIFO control module manages the full and empty status signals:

```systemverilog
fifo_control #(
    .DEPTH(D),
    .ADDR_WIDTH(AW),
    .ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
    .ALMOST_WR_MARGIN(ALMOST_WR_MARGIN)
) fifo_control_inst (
    // ... (ports and connections)
);
```

The ready and valid signals are simply inversions of the full and empty signals:

```systemverilog
assign o_wr_ready = !r_wr_full;
assign o_rd_valid = !r_rd_empty;
```

## Verification Strategies

### Key Test Scenarios

1. **Basic Operation**:
   - Write and read single data values
   - Verify correct data ordering (FIFO behavior)

2. **Boundary Conditions**:
   - Empty to not-empty transition
   - Not-full to full transition
   - Full to not-full transition
   - Not-empty to empty transition

3. **Clock Domain Interaction**:
   - Fast write clock, slow read clock
   - Slow write clock, fast read clock
   - Burst writes followed by burst reads
   - Interleaved writes and reads

4. **Stress Testing**:
   - Fill completely, then empty completely
   - Rapid toggling between almost-full and not-almost-full
   - Rapid toggling between almost-empty and not-almost-empty

### Verification Metrics

1. **Functional Coverage**:
   - Cover all state transitions
   - Cover extremes of almost-full/empty conditions
   - Cover clock frequency ratios

2. **Code Coverage**:
   - Line coverage for all code paths
   - Toggle coverage for all signals
   - FSM state coverage

3. **Formal Verification Properties**:
   - No data loss
   - Correct pointer synchronization
   - No metastability propagation

## Performance Considerations

### Latency Analysis

1. **Write-to-Read Latency**:
   - Minimum latency is determined by synchronizer depth
   - Typically 2-3 cycles in the read clock domain after write

2. **Flow Control Latency**:
   - Full status requires 2-3 cycles to propagate to write source
   - Empty status requires 2-3 cycles to propagate to read sink

### Throughput Analysis

1. **Single Clock Domain Equivalent**:
   - Maximum theoretical throughput is 1 data item per cycle in each domain
   - Actual throughput limited by slower of the two clocks

2. **Back-Pressure Effect**:
   - Almost-full indication provides early warning
   - Proper margin setting prevents overflow/underflow

## Integration Guidelines

### Clocking Considerations

1. **Clock Domain Relationship**:
   - No phase relationship required between clocks
   - Works with any frequency ratio
   - For extreme ratios (>10:1), consider increasing synchronizer stages

2. **Reset Strategy**:
   - Both resets should be properly synchronized to their respective domains
   - No specific relationship required between reset timing

### Interface Guidelines

1. **Write Interface**:
   - Standard valid/ready handshake
   - Data held stable while valid is high
   - Transaction occurs when both valid and ready are high

2. **Read Interface**:
   - Standard valid/ready handshake
   - Data held stable while valid is high
   - Transaction occurs when both valid and ready are high

### Status Signals Usage

1. **Ready Signal (Not Full)**:
   - Can be used directly for flow control
   - Consider implementing backpressure before FIFO is completely full

2. **Valid Signal (Not Empty)**:
   - Can be used directly to indicate data availability
   - Downstream should be ready to accept data when possible

## Related Modules

- **gaxi_fifo_sync**: Synchronous version of the FIFO for single clock domain
- **gaxi_skid_buffer**: Pipeline register with flow control capabilities
- **gaxi_skid_buffer_async**: Asynchronous skid buffer using the async FIFO
- **cdc_handshake**: Simpler CDC mechanism for single-item transfers
- **counter_bin**: Binary counter used for address generation
- **counter_johnson**: Johnson counter for Gray code generation
- **fifo_control**: Full/empty detection logic
- **gray2bin**: Gray-to-binary conversion
- **glitch_free_n_dff_arn**: Multi-stage synchronizer

## Summary

The `gaxi_fifo_async` module provides a robust solution for transferring data between asynchronous clock domains. Its Gray code-based pointer synchronization scheme ensures safe operation even with completely independent clocks, while configurable parameters allow it to be tailored to specific application requirements. The module includes comprehensive status signals and error detection capabilities, making it suitable for a wide range of CDC applications, particularly in AXI interfaces where reliable data transfer across clock domains is essential.
