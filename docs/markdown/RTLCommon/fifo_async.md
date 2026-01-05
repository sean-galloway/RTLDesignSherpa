<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Asynchronous FIFO - Power of 2 (`fifo_async.sv`)

## Purpose
Implements an asynchronous FIFO for safe clock domain crossing between different clock domains. **Restricted to power-of-2 depths only** due to Gray code pointer implementation.

## Ports

### Write Domain
- **`wr_clk`** - Write domain clock
- **`wr_rst_n`** - Write domain active-low reset
- **`write`** - Write enable signal
- **`wr_data[DATA_WIDTH-1:0]`** - Data to write
- **`wr_full`** - Write domain full flag
- **`wr_almost_full`** - Write domain almost full flag

### Read Domain
- **`rd_clk`** - Read domain clock  
- **`rd_rst_n`** - Read domain active-low reset
- **`read`** - Read enable signal
- **`rd_data[DATA_WIDTH-1:0]`** - Data read from FIFO
- **`rd_empty`** - Read domain empty flag
- **`rd_almost_empty`** - Read domain almost empty flag

### Parameters
- **`REGISTERED`** - 0=mux mode, 1=flop mode for read output
- **`DATA_WIDTH`** - Width of data (default: 8)
- **`DEPTH`** - FIFO depth - **must be power of 2** (default: 16)
- **`N_FLOP_CROSS`** - Number of synchronizer stages (default: 2)
- **`ALMOST_WR_MARGIN`** - Almost full threshold (default: 1)
- **`ALMOST_RD_MARGIN`** - Almost empty threshold (default: 1)

## Architecture Overview

### Clock Domain Crossing Strategy
The FIFO uses **Gray code pointers** for safe clock domain crossing:

```
Write Domain                 Read Domain
┌─────────────┐             ┌─────────────┐
│ Binary      │             │ Binary      │
│ Counter ────┼──→ Gray ────┼──→ Sync ────┼──→ Gray2Bin │
│             │   Code      │   Chain     │             │
└─────────────┘             └─────────────┘
```

### Core Components
1. **Binary-Gray counters** (`counter_bingray`) for pointer generation
2. **Multi-stage synchronizers** (`glitch_free_n_dff_arn`) for CDC
3. **Gray-to-binary converters** (`gray2bin`) for pointer comparison
4. **Shared memory array** accessible from both domains
5. **FIFO control logic** for status flag generation

## Implementation Deep Dive

### Gray Code Pointer System

#### Why Gray Codes?
Gray codes ensure **only one bit changes** per increment:
- **Binary**: 011 → 100 (3 bits change simultaneously)
- **Gray**: 010 → 110 (only 1 bit changes)
- **Benefit**: Eliminates metastability from multi-bit transitions

#### Pointer Architecture
```systemverilog
// Write domain Gray counter
counter_bingray #(.WIDTH(AW + 1)) wr_ptr_counter_gray (
    .clk(wr_clk),
    .rst_n(wr_rst_n),
    .enable(write && !wr_full),
    .counter_bin(r_wr_ptr_bin),          // Binary for addressing
    .counter_bin_next(w_wr_ptr_bin_next), // Next binary value
    .counter_gray(r_wr_ptr_gray)         // Gray for CDC
);
```

#### Pointer Width Calculation
- **Address width**: `AW = $clog2(DEPTH)`
- **Pointer width**: `AW + 1` (extra bit for wrap detection)
- **Example**: DEPTH=16 → AW=4, Pointer=5 bits

### Clock Domain Crossing

#### Synchronizer Chains
```systemverilog
// Cross read pointer to write domain
glitch_free_n_dff_arn #(
    .FLOP_COUNT(N_FLOP_CROSS),
    .WIDTH(AW + 1)
) rd_ptr_gray_cross_inst (
    .q(r_wdom_rd_ptr_gray),    // Synchronized output
    .d(r_rd_ptr_gray),         // Gray pointer input
    .clk(wr_clk),              // Destination clock
    .rst_n(wr_rst_n)           // Destination reset
);
```

#### Multi-Stage Synchronization
- **Default stages**: 2 flip-flops (N_FLOP_CROSS=2)
- **MTBF improvement**: Each stage reduces metastability probability
- **Latency trade-off**: More stages = better MTBF but higher latency

### Memory Organization

#### Dual-Port Memory
```systemverilog
logic [DW-1:0] r_mem[0:((1<<AW)-1)];  // Memory array

// Write port (write domain)
always_ff @(posedge wr_clk) begin
    if (write) begin
        r_mem[r_wr_addr] <= wr_data;
    end
end

// Read port (read domain)  
assign w_rd_data = r_mem[r_rd_addr];
```

#### Address Generation
- **Write address**: `r_wr_addr = r_wr_ptr_bin[AW-1:0]`
- **Read address**: `r_rd_addr = r_rd_ptr_bin[AW-1:0]`
- **Truncation**: Uses only lower bits for memory indexing

### Full/Empty Detection

#### Full Detection Logic
```systemverilog
// In write domain
assign wr_full = (w_wdom_ptr_xor && 
                 (wr_ptr_bin[AW-1:0] == wdom_rd_ptr_bin[AW-1:0]));

// Where:
assign w_wdom_ptr_xor = wr_ptr_bin[AW] ^ wdom_rd_ptr_bin[AW];
```

#### Empty Detection Logic
```systemverilog
// In read domain
assign rd_empty = (!w_rdom_ptr_xor_for_empty &&
                  (rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]));
```

#### Full/Empty Algorithm
- **Full condition**: MSBs differ AND LSBs equal (write caught up after wrap)
- **Empty condition**: All bits equal (pointers at same location)
- **MSB significance**: Indicates which pointer has wrapped around

## Power-of-2 Requirement

### Why Power-of-2 Only?
1. **Gray code properties**: Natural binary-Gray relationship
2. **Wraparound behavior**: Clean modulo-2^n arithmetic  
3. **Address truncation**: Simple bit slicing for memory addressing
4. **Pointer comparison**: Efficient full/empty detection

### Limitation Impact
```systemverilog
// Valid depths: 2, 4, 8, 16, 32, 64, 128, 256, ...
// Invalid depths: 3, 5, 6, 7, 9, 10, 12, 15, ...
```

## Timing Considerations

### Clock Domain Crossing Latency
- **Pointer propagation**: 2-3 clock cycles (depending on N_FLOP_CROSS)
- **Status flag delay**: Flags reflect state with synchronizer latency
- **Conservative design**: Prevents overflow/underflow despite delay

### Metastability Protection
- **Gray code transitions**: Single bit changes only
- **Multi-stage sync**: Reduces MTBF exponentially
- **Setup/hold margins**: Proper timing constraints essential

## Use Cases

### Typical Applications
- **Video processing**: Different pixel and memory clock domains
- **Networking**: Packet buffers between different rate domains
- **Audio systems**: Sample rate conversion buffers
- **Microprocessor interfaces**: CPU and peripheral clock domains

### When to Use vs. Alternatives
- **Use async FIFO when**: Clock domains are truly independent
- **Use sync FIFO when**: Single clock domain sufficient
- **Use async_div2 when**: Need non-power-of-2 depth

## Design Guidelines

### Depth Sizing
```systemverilog
// Calculate minimum depth for burst handling
// DEPTH ≥ burst_size + synchronizer_latency + margin
parameter int MIN_DEPTH = 16;  // Typical minimum for async FIFOs
```

### Clock Relationship
- **Asynchronous clocks**: No phase relationship assumed
- **Clock gating**: Avoid gating clocks used by FIFO
- **Reset deassertion**: Ensure proper reset release sequencing

### Almost Full/Empty Settings
- **Almost full**: `DEPTH - ALMOST_WR_MARGIN`
- **Almost empty**: `ALMOST_RD_MARGIN`  
- **Guideline**: Set margins > synchronizer latency

## Performance Characteristics
- **Throughput**: Up to 1 operation per clock per domain
- **Latency**: 0-1 cycles (depending on REGISTERED mode)
- **CDC latency**: 2-3 cycles for status propagation
- **Efficiency**: ~100% utilization possible

## Error Detection Features
```systemverilog
// Simulation-only error checking
always_ff @(posedge wr_clk) begin
    if (!wr_rst_n && (write && wr_full) == 1'b1) begin
        $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
    end
end
```

## WaveDrom Visualization

**High-quality waveforms showcasing Gray code CDC mechanism are available!**

Run the WaveDrom test to generate detailed timing diagrams:

```bash
# Generate Gray code waveforms (standard async FIFO implementation)
pytest val/common/test_fifo_async_wavedrom.py -v
```

**Waveform Scenarios Generated:**

1. **Write-Fill-Read-Empty Cycle**
   - Standard async FIFO operation
   - Gray code pointer progression
   - Power-of-2 depth utilization

2. **Gray Code Synchronization**
   - Efficient Gray code CDC
   - Logarithmic pointer width (vs. linear for Johnson)
   - Cross-domain pointer transitions

3. **Power-of-2 Depth Utilization**
   - Efficient addressing with power-of-2 depths
   - Full depth wraparound behavior
   - Resource-efficient pointer management

**Key Differences from Johnson Counter Variant:**

- **Pointer Width**: Logarithmic (`$clog2(DEPTH) + 1`) vs. linear (`DEPTH`) for Johnson
- **Depth Restriction**: Power-of-2 only vs. any even number for Johnson
- **Resource Efficiency**: Better for large depths (>32) vs. Johnson's flexibility for small depths

**Comparison Tests:**

- `test_fifo_async_div2_wavedrom.py` - Johnson counter CDC (flexible even depths)
- `test_fifo_sync_wavedrom.py` - Synchronous FIFO (single clock, no CDC)

## Related Modules
- **fifo_async_div2**: For non-power-of-2 depths using Johnson counters
- **fifo_sync**: For single clock domain applications
- **counter_bingray**: Binary-Gray counter implementation
- **glitch_free_n_dff_arn**: Multi-stage synchronizer

## Test and Verification

**Comprehensive Test Suite:**
- `val/common/test_fifo_buffer_async.py` - Full functional verification
- `val/common/test_fifo_async_wavedrom.py` - WaveDrom timing diagrams

**Run Tests:**
```bash
# Full functional test (basic/medium/full levels)
pytest val/common/test_fifo_buffer_async.py -v

# WaveDrom waveform generation
pytest val/common/test_fifo_async_wavedrom.py -v
```

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
