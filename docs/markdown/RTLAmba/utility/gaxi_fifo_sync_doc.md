# GAXI Synchronous FIFO Module

## Overview

The `gaxi_fifo_sync` module implements a parameterized synchronous FIFO (First In, First Out) buffer operating in a single clock domain. This module is designed for buffering and flow control in AXI interfaces, providing configurable depth and width to suit various application requirements.

## Features

- Synchronous operation with a single clock domain
- Parameterizable data width and FIFO depth
- Full and empty status signals
- Almost-full and almost-empty indicators with configurable margins
- Registered and unregistered read data outputs
- FIFO count output for monitoring fill level
- Error detection for underflow and overflow conditions
- Compatible with AXI interface timing requirements

## Module Parameters

| Parameter | Description | Default |
|-----------|-------------|---------|
| `DEL` | Delay parameter | 1 |
| `DATA_WIDTH` | Width of the data bus | 4 |
| `DEPTH` | FIFO depth (works with any depth) | 4 |
| `ALMOST_WR_MARGIN` | Margin for almost-full indication | 1 |
| `ALMOST_RD_MARGIN` | Margin for almost-empty indication | 1 |
| `INSTANCE_NAME` | Name used for error reporting | "DEADF1F0" |
| `DW` | Alias for DATA_WIDTH | DATA_WIDTH |
| `D` | Alias for DEPTH | DEPTH |
| `AW` | Address width, calculated as log2(DEPTH) | $clog2(DEPTH) |

## Interface Ports

### Clock and Reset Signals

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `i_axi_aclk` | input | 1 | System clock |
| `i_axi_aresetn` | input | 1 | Active-low reset |

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
| `ow_count` | output | AW | Current FIFO fill level |
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
 i_rd_ready ----->|                         |----> ow_count
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
                       v              v
                  +-----------------------+
                  |                       |
                  |    FIFO Control       |
                  |                       |
                  +-----------------------+
                      |      |      |
                      v      v      v
                 Full  Empty  Count
```

### Core Components

1. **Memory Array**:
   - A dual-port memory array of size DEPTH × DATA_WIDTH
   - Write port clocked by system clock
   - Read port accessed asynchronously for `ow_rd_data` or clocked by system clock for `o_rd_data`

2. **Binary Counters**:
   - Write pointer counter tracking write position
   - Read pointer counter tracking read position
   - Both counters wrap around when reaching DEPTH

3. **FIFO Control**:
   - Generates full, empty, almost-full, and almost-empty signals
   - Calculates and outputs the current fill level count
   - Manages status based on write and read pointers

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
   - Full status determined by comparing read pointer with write pointer
   - Empty status determined by comparing write pointer with read pointer
   - Almost-full/empty determined by programmable margins
   - Count value indicates the current FIFO fill level

## Detailed Operation

### Initialization

Upon reset:
1. All pointers are cleared to zero
2. FIFO is marked as empty
3. FIFO is marked as not full
4. No reads or writes allowed during reset

### Write Operation

The system clock (`i_axi_aclk`) controls:
1. Write pointer counter increment
2. Data storage into memory array
3. Full status generation

A write operation occurs when:
```verilog
w_write = i_wr_valid && o_wr_ready;
```

When a write occurs:
1. Current write data is stored at the memory location addressed by `r_wr_addr`
2. The write pointer advances to the next location

### Read Operation

The system clock (`i_axi_aclk`) also controls:
1. Read pointer counter increment
2. Data retrieval from memory array (for registered output)
3. Empty status generation

A read operation occurs when:
```verilog
w_read = o_rd_valid && i_rd_ready;
```

When a read occurs:
1. Data is read from memory at the location addressed by `r_rd_addr`
2. The read pointer advances to the next location

### Full and Empty Detection

The `fifo_control` module handles full and empty detection:

1. **Full Detection**:
   - Occurs when the write pointer is about to catch up to the read pointer
   - Based on comparing next write pointer with current read pointer
   - Since this is a synchronous FIFO, pointers can be compared directly

2. **Empty Detection**:
   - Occurs when read and write pointers match
   - Simple equality check in a synchronous FIFO

3. **Almost-Full Detection**:
   - Based on remaining slots before full
   - Determined by programmable margin `ALMOST_WR_MARGIN`

4. **Almost-Empty Detection**:
   - Based on available data before empty
   - Determined by programmable margin `ALMOST_RD_MARGIN`

### Count Generation

The FIFO count output provides the current fill level:

```verilog
assign ow_count = current_fifo_level; // From fifo_control module
```

This count value can be used for monitoring and flow control.

### Error Detection

The module includes diagnostic code to detect:
1. Writes while full
2. Reads while empty

These errors are reported with timestamp information during simulation.

## Usage Considerations

### Reset Requirements

The reset signal (`i_axi_aresetn`) should be properly synchronized to the clock domain. A proper reset sequence ensures that:
1. All pointers are initialized to zero
2. FIFO is initially empty
3. Status signals are in correct initial states

### Parameter Selection

1. **FIFO Depth (`DEPTH`)**:
   - Can be any positive integer (not limited to powers of two)
   - Must be large enough to accommodate the maximum expected data burst
   - Consider bandwidth requirements and latency tolerance

2. **Almost-Full/Empty Margins**:
   - Set based on application flow control needs
   - Larger margins provide more time for the system to respond
   - Typically set to accommodate worst-case response latency

### Critical Timing Paths

1. **Memory Write Path**:
   - From write valid/data to memory write
   - Critical in high-frequency applications

2. **Full/Empty Generation**:
   - Pointer comparison logic for status generation
   - Can be critical for back-pressure timing

3. **Read Data Path**:
   - From memory read to output
   - May require pipelining (registered output) for high frequencies

### Integration Examples

#### Basic Usage

```systemverilog
// Instantiate sync FIFO for buffering
gaxi_fifo_sync #(
    .DATA_WIDTH(32),       // 32-bit data bus
    .DEPTH(16),            // 16 entries deep
    .ALMOST_WR_MARGIN(2)   // Early back-pressure
) buffer_fifo (
    // Clock and reset
    .i_axi_aclk(system_clk),
    .i_axi_aresetn(system_rst_n),
    
    // Write interface
    .i_wr_valid(upstream_valid),
    .o_wr_ready(upstream_ready),
    .i_wr_data(upstream_data),
    
    // Read interface
    .i_rd_ready(downstream_ready),
    .o_rd_valid(downstream_valid),
    .ow_count(fifo_level),
    .o_rd_data(downstream_data),
    .ow_rd_data() // Unused unregistered output
);
```

#### AXI Stream Interface Buffer

```systemverilog
// For buffering AXI-Stream data
gaxi_fifo_sync #(
    .DATA_WIDTH(DATA_W + 1),  // Data + TLAST
    .DEPTH(32),               // Deeper FIFO for burst handling
    .ALMOST_WR_MARGIN(4)      // Early back-pressure
) axis_buffer_fifo (
    // Clock and reset
    .i_axi_aclk(axi_clk),
    .i_axi_aresetn(axi_rstn),
    
    // Write interface (from source)
    .i_wr_valid(axis_src_tvalid),
    .o_wr_ready(axis_src_tready),
    .i_wr_data({axis_src_tlast, axis_src_tdata}),
    
    // Read interface (to destination)
    .i_rd_ready(axis_dst_tready),
    .o_rd_valid(axis_dst_tvalid),
    .ow_count(axis_fifo_count),
    .o_rd_data({axis_dst_tlast, axis_dst_tdata}),
    .ow_rd_data() // Unused
);
```

## Implementation Details

### Memory Implementation

The FIFO memory is implemented as an array of flip-flops:

```systemverilog
// The flop storage
logic [DW-1:0] r_mem[0:((1<<AW)-1)];
```

Data is written using a simple always block:

```systemverilog
always_ff @(posedge i_axi_aclk) begin
    if (w_write && !r_wr_full) begin
        r_mem[r_wr_addr] <= i_wr_data;
    end
end
```

The registered output adds an extra pipeline stage:

```systemverilog
// Flop stage for the flopped data
always_ff @(posedge i_axi_aclk or negedge i_axi_aresetn) begin
    if (!i_axi_aresetn) o_rd_data <= 'b0;
    else o_rd_data <= r_mem[r_rd_addr];
end
```

### Pointer Management

Binary counters track write and read positions:

```systemverilog
counter_bin #(
    .WIDTH(AW + 1),
    .MAX  (D)
) write_pointer_inst (
    .i_clk(i_axi_aclk),
    .i_rst_n(i_axi_aresetn),
    .i_enable(w_write && !r_wr_full),
    .o_counter_bin(r_wr_ptr_bin),
    .ow_counter_bin_next(w_wr_ptr_bin_next)
);
```

The `counter_bin` module ensures proper wrapping behavior when reaching the maximum count.

### FIFO Control Logic

The FIFO control module manages the full and empty status signals:

```systemverilog
fifo_control #(
    .DEL(DEL),
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

3. **Flow Control Testing**:
   - Back-pressure with full FIFO
   - Stall with empty FIFO
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
   - Cover count value ranges

2. **Code Coverage**:
   - Line coverage for all code paths
   - Toggle coverage for all signals
   - FSM state coverage

3. **Formal Verification Properties**:
   - No data loss
   - Correct pointer behavior
   - Correct count reporting

## Performance Considerations

### Latency Analysis

1. **Write-to-Read Latency**:
   - Unregistered output: 0 cycles (combinatorial path from memory to output)
   - Registered output: 1 cycle (memory to registered output)

2. **Flow Control Latency**:
   - Full status immediately affects write acceptance
   - Empty status immediately affects read validity

### Throughput Analysis

1. **Maximum Throughput**:
   - Maximum theoretical throughput is 1 data item per cycle
   - Can sustain full throughput with proper flow control

2. **Back-Pressure Effect**:
   - Almost-full indication provides early warning
   - Proper margin setting prevents overflow/underflow during flow control response

## Integration Guidelines

### Clocking Considerations

1. **Clock Frequency**:
   - Single clock domain simplifies timing analysis
   - All timing paths related to a single clock

2. **Reset Strategy**:
   - Reset should be properly synchronized to the clock domain
   - Asynchronous reset, synchronous deassertion recommended

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

3. **Count Signal**:
   - Can be used for more sophisticated flow control
   - Useful for monitoring and debugging

## Related Modules

- **gaxi_fifo_async**: Asynchronous version of the FIFO for crossing clock domains
- **gaxi_skid_buffer**: Pipeline register with flow control capabilities
- **counter_bin**: Binary counter used for address generation
- **fifo_control**: Full/empty detection logic

## Summary

The `gaxi_fifo_sync` module provides a flexible synchronous FIFO solution with configurable depth and width. Operating in a single clock domain, it offers both registered and unregistered read data outputs, comprehensive status signals, and count information. The module's parameterization allows it to be tailored to specific application requirements, while its AXI-compatible interfaces make it suitable for integration in AXI-based designs where buffering and flow control are needed.
