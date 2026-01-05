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

# FIFO Control Logic (`fifo_control.sv`)

## Purpose
Centralized control logic module that generates full/empty status flags for all FIFO variants (sync, async, async_div2). Handles the complex pointer arithmetic and mode-aware timing considerations.

## Ports

### Clock and Reset
- **`wr_clk`** - Write domain clock
- **`wr_rst_n`** - Write domain active-low reset
- **`rd_clk`** - Read domain clock
- **`rd_rst_n`** - Read domain active-low reset

### Pointer Inputs
- **`wr_ptr_bin[ADDR_WIDTH:0]`** - Write pointer (binary, next value)
- **`wdom_rd_ptr_bin[ADDR_WIDTH:0]`** - Read pointer synchronized to write domain
- **`rd_ptr_bin[ADDR_WIDTH:0]`** - Read pointer (binary, next value)
- **`rdom_wr_ptr_bin[ADDR_WIDTH:0]`** - Write pointer synchronized to read domain

### Status Outputs
- **`count[ADDR_WIDTH:0]`** - Current FIFO occupancy count
- **`wr_full`** - Write domain full flag
- **`wr_almost_full`** - Write domain almost full flag
- **`rd_empty`** - Read domain empty flag
- **`rd_almost_empty`** - Read domain almost empty flag

### Parameters
- **`ADDR_WIDTH`** - Address width (default: 3)
- **`DEPTH`** - FIFO depth (default: 16)
- **`ALMOST_WR_MARGIN`** - Almost full threshold (default: 1)
- **`ALMOST_RD_MARGIN`** - Almost empty threshold (default: 1)
- **`REGISTERED`** - Output mode: 0=mux, 1=flop (default: 0)

## Architecture Overview

### Dual-Domain Design
The module operates across two clock domains:
- **Write domain**: Generates full and almost_full flags
- **Read domain**: Generates empty and almost_empty flags

### Pointer Arithmetic Foundation
All status generation relies on **pointer comparison with wraparound detection**:

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
- **Condition 1**: MSBs must differ (`w_wdom_ptr_xor = 1`)
- **Condition 2**: LSBs must be equal
- **Meaning**: Write pointer has "lapped" the read pointer

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
    (AW'(D) - wdom_rd_ptr_bin[AW-1:0] + wr_ptr_bin[AW-1:0]) :
    (wr_ptr_bin[AW-1:0] - wdom_rd_ptr_bin[AW-1:0]);
```

### Two Cases Handled
1. **No wraparound** (`w_wdom_ptr_xor = 0`):
   - Count = `wr_ptr - rd_ptr`
   - Simple subtraction

2. **Wraparound** (`w_wdom_ptr_xor = 1`):
   - Count = `DEPTH - rd_ptr + wr_ptr`
   - Accounts for circular buffer wraparound

### Almost Full Threshold
```systemverilog
assign w_wr_almost_full_d = w_almost_full_count >= AW'(AFT);
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
- **Write pointer**: Use current value
- **Reasoning**: Data is immediately available when written

#### FLOP Mode (REGISTERED = 1)  
- **Data availability**: Delayed by 1 cycle (registered read)
- **Write pointer**: Use delayed value
- **Reasoning**: Data isn't available until next clock cycle

### Empty Detection Algorithm
```systemverilog
assign w_rd_empty_d = (!w_rdom_ptr_xor_for_empty &&
                      (rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]));
```

- **Condition 1**: MSBs must be same (no wrap difference)
- **Condition 2**: All bits must be equal
- **Meaning**: Read pointer has caught up to write pointer

## Almost Empty Logic

### Standard Timing (Mode-Independent)
Almost empty calculation uses standard timing regardless of FIFO mode:

```systemverilog
assign w_almost_empty_count = (w_rdom_ptr_xor) ?
    (AW'(D) - rd_ptr_bin[AW-1:0] + rdom_wr_ptr_bin[AW-1:0]) :
    (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0]);

assign w_rd_almost_empty_d = w_almost_empty_count <= AW'(AET);
// Where AET = ALMOST_RD_MARGIN
```

## Count Generation

### Occupancy Count Logic
```systemverilog
assign count = (w_rdom_ptr_xor) ?
    (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0] + AW'(D)) :
    (rdom_wr_ptr_bin[AW-1:0] - rd_ptr_bin[AW-1:0]);
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
// Fixed: Cast D to AW-bit width to match other operands
assign w_almost_full_count = (w_wdom_ptr_xor) ?
    (AW'(D) - wdom_rd_ptr_bin[AW-1:0] + wr_ptr_bin[AW-1:0]) :
    (wr_ptr_bin[AW-1:0] - wdom_rd_ptr_bin[AW-1:0]);
```

The `AW'(D)` casting ensures all operands have matching bit widths, preventing synthesis warnings.

## Key Design Insights

### Wraparound Handling
- **MSB significance**: Extra bit detects wraparound events
- **Circular arithmetic**: Proper modulo DEPTH calculations
- **Comparison logic**: XOR-based wraparound detection

### Timing Considerations
- **Synchronizer delay**: Accounted for in conservative design
- **Mode awareness**: Different timing for different output modes
- **Flag updates**: Registered for clean transitions

### Conservative Design
- **Over-reporting**: Flags may assert slightly early
- **Safety margin**: Prevents overflow/underflow
- **Synchronizer latency**: Built into safety margins

## Use Cases
- **All FIFO variants**: Shared by sync, async, and async_div2
- **Status monitoring**: Provides comprehensive FIFO state
- **Flow control**: Enables back-pressure and rate matching
- **Debug/verification**: Count output aids in debugging

## Performance Impact
- **Minimal overhead**: Efficient pointer arithmetic
- **Low latency**: Single cycle flag updates
- **Resource efficient**: Shared across multiple FIFO types

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
