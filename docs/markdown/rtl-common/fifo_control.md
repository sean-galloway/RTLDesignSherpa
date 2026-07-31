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

# fifo_control (`fifo_control.sv`)

## Purpose
This is the shared brain that generates full/empty status flags for both FIFO variants (sync and async, the latter with either pointer encoding). All the tricky pointer arithmetic and mode-aware timing lives here.

## Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `ADDR_WIDTH` | 3 | Address width |
| `DEPTH` | 16 | FIFO depth |
| `ALMOST_WR_MARGIN` | 1 | Almost full threshold |
| `ALMOST_RD_MARGIN` | 1 | Almost empty threshold |
| `REGISTERED` | 0 | Output mode: 0=mux, 1=flop |

## Ports
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `wr_clk` | Input | 1 | Write domain clock |
| `wr_rst_n` | Input | 1 | Write domain active-low reset |
| `rd_clk` | Input | 1 | Read domain clock |
| `rd_rst_n` | Input | 1 | Read domain active-low reset |
| `wr_ptr_bin` | Input | ADDR_WIDTH+1 | Write pointer (binary, next value) |
| `wdom_rd_ptr_bin` | Input | ADDR_WIDTH+1 | Read pointer synchronized to write domain |
| `rd_ptr_bin` | Input | ADDR_WIDTH+1 | Read pointer (binary, next value) |
| `rdom_wr_ptr_bin` | Input | ADDR_WIDTH+1 | Write pointer synchronized to read domain |
| `count` | Output | ADDR_WIDTH+1 | Current FIFO occupancy count |
| `wr_full` | Output | 1 | Write domain full flag |
| `wr_almost_full` | Output | 1 | Write domain almost full flag |
| `rd_empty` | Output | 1 | Read domain empty flag |
| `rd_almost_empty` | Output | 1 | Read domain almost empty flag |

## Architecture Overview

### Dual-Domain Design
The module straddles two clock domains:
- **Write domain**: Generates full and almost_full flags
- **Read domain**: Generates empty and almost_empty flags

### Pointer Arithmetic Foundation
All the status generation boils down to **pointer comparison with wraparound detection**:

```systemverilog
// XOR the MSBs to detect wraparound condition
assign w_wdom_ptr_xor = wr_ptr_bin[AW] ^ wdom_rd_ptr_bin[AW];
assign w_rdom_ptr_xor = rd_ptr_bin[AW] ^ rdom_wr_ptr_bin[AW];
```

## Full Detection Logic

### Basic Full Condition
```systemverilog
assign w_wr_full_d = (w_wdom_ptr_xor && 
                     (wr_ptr_bin[AW-1:0] == wdom_rd_ptr_bin[AW-1:0]));
```

### Full Detection Algorithm
- **Condition 1**: The MSBs must differ (`w_wdom_ptr_xor = 1`)
- **Condition 2**: The LSBs must be equal
- **Meaning**: The write pointer has "lapped" the read pointer

### Visual Example (DEPTH=8, ADDR_WIDTH=3)
```
Pointers: [wrap_bit][address_bits]

Case 1: Not Full
wr_ptr  = 0_101  (address 5, no wrap)
rd_ptr  = 0_010  (address 2, no wrap)
→ MSBs same, not full

Case 2: Full  
wr_ptr  = 1_010  (address 2, wrapped once)
rd_ptr  = 0_010  (address 2, not wrapped)
→ MSBs differ, addresses same = FULL
```

## Almost Full Logic

### Occupancy Calculation
```systemverilog
assign w_almost_full_count = (w_wdom_ptr_xor) ?
    ((AW+1)'(D) - wdom_rd_ptr_bin[AW-1:0] + wr_ptr_bin[AW-1:0]) :
    (wr_ptr_bin[AW-1:0] - wdom_rd_ptr_bin[AW-1:0]);
```

### Two Cases Handled
1. **No wraparound** (`w_wdom_ptr_xor = 0`):
   - Count = `wr_ptr - rd_ptr`
   - Just a simple subtraction

2. **Wraparound** (`w_wdom_ptr_xor = 1`):
   - Count = `DEPTH - rd_ptr + wr_ptr`
   - Accounts for the circular buffer wrapping around

### Almost Full Threshold
```systemverilog
assign w_wr_almost_full_d = w_almost_full_count >= (AW+1)'(AFT);
// Where AFT = DEPTH - ALMOST_WR_MARGIN
```

## Empty Detection Logic - Mode Aware

### Critical Innovation: Mode-Aware Write Pointer Selection
```systemverilog
generate
    if (REGISTERED == 1) begin : gen_flop_mode
        // FLOP mode: Use previous cycle's write pointer
        logic [ADDR_WIDTH:0] r_rdom_wr_ptr_bin_delayed;
        
        always_ff @(posedge rd_clk or negedge rd_rst_n) begin
            if (!rd_rst_n) begin
                r_rdom_wr_ptr_bin_delayed <= '0;
            end else begin
                r_rdom_wr_ptr_bin_delayed <= rdom_wr_ptr_bin;
            end
        end
        
        assign w_wr_ptr_for_empty = r_rdom_wr_ptr_bin_delayed;
    end else begin : gen_mux_mode
        // MUX mode: Use current write pointer
        assign w_wr_ptr_for_empty = rdom_wr_ptr_bin;
    end
endgenerate
```

### Why Mode-Aware Detection?

#### MUX Mode (REGISTERED = 0)
- **Data availability**: Immediate (combinational read)
- **Write pointer**: Use the current value
- **Reasoning**: Data is available the moment it's written

#### FLOP Mode (REGISTERED = 1)  
- **Data availability**: Delayed by 1 cycle (registered read)
- **Write pointer**: Use the delayed value
- **Reasoning**: Data isn't available until the next clock cycle

### Empty Detection Algorithm
```systemverilog
assign w_rd_empty_d = (!w_rdom_ptr_xor_for_empty &&
                      (rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]));
```

- **Condition 1**: The MSBs must be the same (no wrap difference)
- **Condition 2**: All bits must be equal
- **Meaning**: The read pointer has caught up to the write pointer

## Almost Empty Logic

### Standard Timing (Mode-Independent)
Almost empty uses standard timing regardless of FIFO mode:

```systemverilog
assign w_almost_empty_count = (w_rdom_ptr_xor) ?
    ((AW+1)'(D) - rd_ptr_bin[AW-1:0] + rdom_wr_ptr_bin[AW-1:0]) :
    (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0]);

assign w_rd_almost_empty_d = w_almost_empty_count <= (AW+1)'(AET);
// Where AET = ALMOST_RD_MARGIN
```

## Count Generation

### Occupancy Count Logic
```systemverilog
// Combinational occupancy...
logic [AW:0] w_count, r_count;
assign w_count = (w_rdom_ptr_xor) ?
    (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0] + (AW+1)'(D)) :
    (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0]);

// ...but the exported count is REGISTERED in flop mode (r_count is w_count
// delayed one rd_clk); mux mode exports the combinational value directly.
assign count = (REGISTERED == 1) ? r_count : w_count;
```

### Count Interpretation
- **Range**: 0 to DEPTH
- **Zero**: FIFO empty
- **DEPTH**: FIFO full
- **Uses**: Flow control, occupancy monitoring

## Flag Registration

### Write Domain Flags
```systemverilog
always_ff @(posedge wr_clk, negedge wr_rst_n) begin
    if (!wr_rst_n) begin
        wr_full <= 'b0;
        wr_almost_full <= 'b0;
    end else begin
        wr_full <= w_wr_full_d;
        wr_almost_full <= w_wr_almost_full_d;
    end
end
```

### Read Domain Flags
```systemverilog
always_ff @(posedge rd_clk, negedge rd_rst_n) begin
    if (!rd_rst_n) begin
        rd_empty <= 'b1;          // Reset to empty
        rd_almost_empty <= 'b0;
    end else begin
        rd_empty <= w_rd_empty_d;
        rd_almost_empty <= w_rd_almost_empty_d;
    end
end
```

### Reset Behavior
- **Full flags**: Reset to 0 (not full)
- **Empty flags**: Reset to 1 (empty)
- **Almost flags**: Reset to 0

## Width Casting Fix

### Type Width Matching
```systemverilog
// The occupancy count needs AW+1 bits, and D (= DEPTH) must be cast to AW+1
// bits -- NOT AW bits. AW'(D) TRUNCATES: for depth=16, AW=4, AW'(16) = 4'b0000
// (wrong!), whereas (AW+1)'(16) = 5'b10000 (correct). The count register is
// widened to [AW:0] to hold the full range 0..DEPTH.
logic [AW:0] w_almost_full_count;

assign w_almost_full_count = (w_wdom_ptr_xor) ?
    ((AW+1)'(D) - wdom_rd_ptr_bin[AW-1:0] + wr_ptr_bin[AW-1:0]) :
    (wr_ptr_bin[AW-1:0] - wdom_rd_ptr_bin[AW-1:0]);
```

That `(AW+1)'(D)` cast (with the widened `[AW:0]` count) is the only thing
standing between you and a truncated wraparound occupancy. Cast to `AW'(D)`
instead and you reintroduce the truncation bug: e.g. DEPTH=16 with wr=2, rd=14
should give occupancy 16-14+2 = 4, but `AW'(16)` = 0 yields 0-14+2 (garbage).

## Key Design Insights

### Wraparound Handling
- **MSB significance**: The extra bit is your wraparound detector
- **Circular arithmetic**: Proper modulo DEPTH calculations
- **Comparison logic**: XOR-based wraparound detection

### Timing Considerations
- **Synchronizer delay**: Accounted for in the conservative design
- **Mode awareness**: Different timing for different output modes
- **Flag updates**: Registered for clean transitions

### Conservative Design
- **Over-reporting**: Flags may assert slightly early
- **Safety margin**: Prevents overflow/underflow
- **Synchronizer latency**: Built into the safety margins

## Applications
- **All FIFO variants**: Shared by `fifo_sync` and `fifo_async` (binary or Johnson pointers). The former `fifo_async_div2` is retired — `fifo_async` with `USE_JOHNSON=1` replaces it.
- **Status monitoring**: Provides comprehensive FIFO state
- **Flow control**: Enables back-pressure and rate matching
- **Debug/verification**: The count output earns its keep during debug

## Performance Impact
- **Minimal overhead**: Efficient pointer arithmetic
- **Low latency**: Single cycle flag updates
- **Resource efficient**: Shared across multiple FIFO types

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
