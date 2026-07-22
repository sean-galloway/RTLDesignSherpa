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

# Count Trailing Zeros Module

## Overview
The `count_trailing_zeros` module implements a trailing zero counter that determines how many consecutive zero bits appear at the end (LSB side) of a data word. It is the mirror image of `count_leading_zeros` and is the natural primitive for alignment checks, lowest-set-bit extraction, and picking the least significant pending request out of a vector.

The scan starts at `data[0]` and proceeds upward, stopping at the first set bit:

```
data = 32'h0000_0001 -> ctz =  0   (bit 0 is already set)
data = 32'h8000_0000 -> ctz = 31   (31 zeros below the MSB)
data = 32'h0000_0000 -> ctz = WIDTH
```

For the complementary count from the MSB downward, use
**[count_leading_zeros](count_leading_zeros.md)**.

### Choosing Between CLZ and CTZ

| Question you are asking | Module |
|-------------------------|--------|
| How big is this value? (normalization, log2, minimum bit width) | `count_leading_zeros` |
| How is this value aligned? (address alignment, burst size, power-of-two stride) | `count_trailing_zeros` |
| Which is the highest priority request set? | `count_leading_zeros` |
| Which is the lowest index request set? | `count_trailing_zeros` |

Never emulate one by bit-reversing the input to the other. Both modules exist; picking
the right one costs no extra logic and keeps intent visible in the netlist.

## Module Declaration
```systemverilog
module count_trailing_zeros #(
    parameter int WIDTH = 32
) (
    input  logic [      WIDTH-1:0] data,
    output logic [$clog2(WIDTH):0] ctz
);
```

## Parameters

### WIDTH
- **Type**: `int`
- **Default**: `32`
- **Description**: Bit width of the input data
- **Range**: Any positive integer >= 1
- **Common Values**: 8, 16, 32, 64 for standard data widths
- **Impact**: Determines output width and algorithm complexity

`WIDTH` is the only parameter.

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `data` | WIDTH | `logic` | Input data word to analyze |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `ctz` | `$clog2(WIDTH)+1` | `logic` | Count of trailing zeros |

### Output Width Explanation
The output width `$clog2(WIDTH)+1` ensures it can represent all possible counts:
- **Range**: 0 to WIDTH (inclusive)
- **Example**: For WIDTH=32, output is 6 bits (0-32 requires 6 bits)
- **Special Case**: All zeros input produces CTZ = WIDTH

## Algorithm Implementation

### Function-Based Approach
```systemverilog
function automatic [$clog2(WIDTH):0] ctz_func;
    input [WIDTH-1:0] input_data;
    logic found;
    begin
        ctz_func = 0;
        found = 1'b0;
        // Scan from the LSB upward.
        for (int i = 0; i < WIDTH; i++) begin
            if (!input_data[i] && !found) begin
                ctz_func += 1;
            end else begin
                found = 1'b1;  // Stop counting when first '1' found
            end
        end
    end
endfunction
```

### Bit Scanning Process
The algorithm scans from LSB to MSB:
1. **Initialize**: `ctz_func = 0`, `found = 0`
2. **Scan Loop**: For each bit position i from 0 to WIDTH-1:
   - If `data[i] == 0` AND no '1' found yet: increment count
   - If `data[i] == 1`: set found flag, stop counting
3. **Result**: Final count is the number of zeros below the lowest set bit

### Why LSB-to-MSB Scanning?
"Trailing" refers to the bits that trail the word when it is written out, which is the
LSB side. The loop therefore starts at `data[0]` and walks up:
- **Bit Order**: `data[0]` is LSB, `data[WIDTH-1]` is MSB
- **Termination**: The `found` flag latches at the lowest set bit, so all bits above it
  are ignored - only the contiguous run below it is counted
- **Count Logic**: `ctz = position_of_lowest_set_one`, and `ctz = WIDTH` when no bit is set

## Examples and Truth Tables

### 8-bit Examples (WIDTH=8)
The count is set by the **lowest** set bit; bits above it never affect the result.

| Input (data) | Binary | Lowest set bit | Trailing Zeros | CTZ Output |
|--------------|---------|----------------|----------------|------------|
| 8'b00000000 | 00000000 | None | 8 | 8 |
| 8'b00000001 | 00000001 | Bit 0 | 0 | 0 |
| 8'b00000010 | 00000010 | Bit 1 | 1 | 1 |
| 8'b00000100 | 00000100 | Bit 2 | 2 | 2 |
| 8'b00001000 | 00001000 | Bit 3 | 3 | 3 |
| 8'b00010000 | 00010000 | Bit 4 | 4 | 4 |
| 8'b00100000 | 00100000 | Bit 5 | 5 | 5 |
| 8'b01000000 | 01000000 | Bit 6 | 6 | 6 |
| 8'b10000000 | 10000000 | Bit 7 | 7 | 7 |
| 8'b11111111 | 11111111 | Bit 0 | 0 | 0 |
| 8'b10101010 | 10101010 | Bit 1 | 1 | 1 |
| 8'b00110000 | 00110000 | Bit 4 | 4 | 4 |

### 32-bit Examples
| Input | Hex | Trailing Zeros | CTZ |
|-------|-----|----------------|-----|
| 32'h00000000 | 0x00000000 | 32 | 32 |
| 32'h00000001 | 0x00000001 | 0 | 0 |
| 32'h00000080 | 0x00000080 | 7 | 7 |
| 32'h00008000 | 0x00008000 | 15 | 15 |
| 32'h00800000 | 0x00800000 | 23 | 23 |
| 32'h80000000 | 0x80000000 | 31 | 31 |
| 32'hFFFFFFFF | 0xFFFFFFFF | 0 | 0 |

### Relationship to CLZ
For a single-bit input `data == (1 << k)`, the two modules are complementary:

```
ctz = k
clz = WIDTH - 1 - k
ctz + clz = WIDTH - 1
```

That identity holds **only** for one-hot inputs. For general data the two counts are
independent, because CLZ is decided by the highest set bit and CTZ by the lowest. For
example `8'b00110000` gives `clz = 2` and `ctz = 4`, which sum to 6, not 7.

## Applications

### 1. Address Alignment Detection
```systemverilog
// Determine the largest power-of-two boundary an address is aligned to
logic [31:0] address;
logic [5:0]  alignment_log2;

count_trailing_zeros #(.WIDTH(32)) align_ctz (
    .data(address),
    .ctz(alignment_log2)
);

// alignment_log2 = 0  -> byte aligned only
// alignment_log2 = 2  -> 4-byte aligned
// alignment_log2 = 6  -> 64-byte aligned (cache line)
// alignment_log2 = 32 -> address is zero, aligned to everything
```

### 2. Maximum Burst Size for a DMA Transfer
```systemverilog
// A burst may not cross its natural alignment boundary, so the alignment of the
// start address caps the burst size.
logic [31:0] start_addr;
logic [5:0]  addr_align;
logic [5:0]  max_burst_log2;

count_trailing_zeros #(.WIDTH(32)) burst_ctz (
    .data(start_addr),
    .ctz(addr_align)
);

// Clamp against the protocol maximum (e.g. 4KB = 12)
assign max_burst_log2 = (addr_align > 6'd12) ? 6'd12 : addr_align;
```

### 3. Lowest-Index Request Arbitration
```systemverilog
// Fixed priority arbiter favouring the lowest requester index
logic [15:0] request_vector;
logic [4:0]  trailing_zeros;
logic [3:0]  granted_index;
logic        any_request;

count_trailing_zeros #(.WIDTH(16)) req_ctz (
    .data(request_vector),
    .ctz(trailing_zeros)
);

assign any_request  = (trailing_zeros != 16);
assign granted_index = any_request ? trailing_zeros[3:0] : 4'b0;

// Example: request_vector = 16'b0000_0100_1000_0000
// Lowest set bit is bit 7
// CTZ = 7, so requester 7 is granted
```

### 4. Isolating and Clearing the Lowest Set Bit
```systemverilog
// Iterate over set bits one at a time (software-style "x & -x" in hardware)
logic [31:0] pending;
logic [5:0]  next_index;
logic [31:0] lowest_bit_mask;
logic [31:0] pending_next;

count_trailing_zeros #(.WIDTH(32)) pend_ctz (
    .data(pending),
    .ctz(next_index)
);

assign lowest_bit_mask = pending & (~pending + 32'd1);  // isolates bit next_index
assign pending_next    = pending & ~lowest_bit_mask;    // clears it
```

### 5. Power-of-Two Detection
```systemverilog
// A non-zero value is a power of two exactly when its only set bit is the lowest one
logic [31:0] value;
logic [5:0]  value_ctz;
logic        is_power_of_two;

count_trailing_zeros #(.WIDTH(32)) pow2_ctz (
    .data(value),
    .ctz(value_ctz)
);

assign is_power_of_two = (value != 0) && (value == (32'd1 << value_ctz));

// value = 64   -> ctz = 6,  1<<6 = 64   -> true
// value = 96   -> ctz = 5,  1<<5 = 32   -> false
// value = 0    -> false by the explicit guard
```

## Advanced Implementations

### 1. Hierarchical Implementation
```systemverilog
// Divide and conquer approach for large widths
module count_trailing_zeros_hierarchical #(
    parameter int WIDTH = 64
) (
    input  logic [WIDTH-1:0]       data,
    output logic [$clog2(WIDTH):0] ctz
);

localparam int HALF_WIDTH = WIDTH/2;

logic [$clog2(HALF_WIDTH):0] ctz_upper, ctz_lower;
logic lower_all_zeros;

// Count in lower half
count_trailing_zeros #(.WIDTH(HALF_WIDTH)) lower_ctz (
    .data(data[HALF_WIDTH-1:0]),
    .ctz(ctz_lower)
);

// Count in upper half
count_trailing_zeros #(.WIDTH(HALF_WIDTH)) upper_ctz (
    .data(data[WIDTH-1:HALF_WIDTH]),
    .ctz(ctz_upper)
);

assign lower_all_zeros = (ctz_lower == HALF_WIDTH);

// Combine results
assign ctz = lower_all_zeros ? (HALF_WIDTH + ctz_upper) : ctz_lower;

endmodule
```

### 2. LUT-Based Implementation (Small Widths)
```systemverilog
// Optimized for small widths using a wildcard case statement.
// casez is required so that '?' is treated as a don't-care.
module count_trailing_zeros_lut #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0]       data,
    output logic [$clog2(WIDTH):0] ctz
);

always_comb begin
    casez (data)
        8'b???????1: ctz = 0;
        8'b??????10: ctz = 1;
        8'b?????100: ctz = 2;
        8'b????1000: ctz = 3;
        8'b???10000: ctz = 4;
        8'b??100000: ctz = 5;
        8'b?1000000: ctz = 6;
        8'b10000000: ctz = 7;
        default:     ctz = 8;   // all zeros
    endcase
end

endmodule
```

### 3. Mask-Based Implementation
```systemverilog
// Isolate the lowest set bit, then one-hot encode its position.
// Often maps well to carry-chain logic on FPGAs.
logic [WIDTH-1:0] w_lowest_one;

assign w_lowest_one = data & (~data + 1'b1);
// w_lowest_one is one-hot (or all zero), so a plain one-hot encoder yields ctz
```

## Performance Analysis

### Resource Utilization
| WIDTH | LUTs (Typical) | Delay Levels | Max Frequency |
|-------|----------------|--------------|---------------|
| 8 | 15-20 | 3-4 | 500+ MHz |
| 16 | 30-40 | 4-5 | 400+ MHz |
| 32 | 60-80 | 5-6 | 300+ MHz |
| 64 | 120-150 | 6-7 | 250+ MHz |

### Timing Characteristics
- **Combinational Delay**: O(log(WIDTH)) for tree implementations
- **Critical Path**: Through the priority encoding logic
- **Scalability**: Linear increase in logic for the function implementation

## Verification Strategy

### Test Scenarios
1. **Boundary Cases**: All zeros, all ones, single bit patterns
2. **Random Patterns**: Comprehensive random testing
3. **Systematic Sweep**: Test all possible trailing zero counts
4. **Corner Cases**: Maximum width values, alternating patterns
5. **Cross-Check**: For one-hot inputs, confirm `ctz + clz == WIDTH-1` against
   `count_leading_zeros`

### Coverage Model
```systemverilog
covergroup ctz_cg;
    cp_trailing_zeros: coverpoint ctz {
        bins zero_ctz  = {0};
        bins low_ctz   = {[1:WIDTH/4]};
        bins mid_ctz   = {[WIDTH/4+1:3*WIDTH/4]};
        bins high_ctz  = {[3*WIDTH/4+1:WIDTH-1]};
        bins all_zeros = {WIDTH};
    }

    cp_data_patterns: coverpoint data {
        bins all_zeros   = {'0};
        bins all_ones    = {'1};
        bins single_bit[] = {1, 2, 4, 8, 16, 32}; // For appropriate WIDTH
        bins lsb_set     = {1};
        bins msb_set     = {1 << (WIDTH-1)};
        bins mixed[]     = {[1:2**(WIDTH-1)-1]};
    }
endgroup
```

### Assertions
```systemverilog
// CTZ should never exceed WIDTH
property ctz_bounds;
    ctz <= WIDTH;
endproperty

// All zeros should give CTZ = WIDTH
property all_zeros_case;
    (data == '0) |-> (ctz == WIDTH);
endproperty

// LSB set should give CTZ = 0
property lsb_set_case;
    data[0] |-> (ctz == 0);
endproperty

// Relationship between CTZ and the lowest '1' position
property ctz_correctness;
    logic [WIDTH-1:0] shifted;
    assign shifted = data >> ctz;
    (data != '0) |-> shifted[0];
endproperty

// CTZ must select exactly the isolated lowest set bit
property ctz_isolates_lowest;
    (data != '0) |-> ((data & (~data + 1)) == (1 << ctz));
endproperty

assert property (ctz_bounds);
assert property (all_zeros_case);
assert property (lsb_set_case);
assert property (ctz_correctness);
assert property (ctz_isolates_lowest);
```

## Synthesis Optimization

### Area vs. Speed Trade-offs
```systemverilog
// For area optimization: Use the iterative function approach
// For speed optimization: Use the hierarchical or LUT approach
// For power optimization: Add enable signals and clock gating
```

## Common Use Cases Summary
1. **CPU/DSP Cores**: Instruction implementation (CTZ / FFS instruction)
2. **Memory Controllers**: Address alignment and burst-size derivation
3. **DMA Engines**: Legal transfer size given a start address
4. **Schedulers and Arbiters**: Lowest-index pending request selection
5. **Allocators**: Free-list and bitmap scanning
6. **Interrupt Controllers**: Lowest pending interrupt vector

## Related Modules and Functions
- **[count_leading_zeros](count_leading_zeros.md)** - the MSB-down counterpart. See the
  selection table at the top of this page before choosing between them.
- Population count (number of '1' bits)
- Find first set (FFS) / Find last set (FLS)
- Priority encoders
- Barrel shifters

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
