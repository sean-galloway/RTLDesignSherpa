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

# Count Leading Zeros

## Overview

The `count_leading_zeros` module counts how many consecutive zero bits sit at the beginning (MSB side) of a data word. This is fundamental computer arithmetic — you'll find it inside floating-point normalization, priority encoders, and half the bit-manipulation tricks in the book.

The scan starts at `data[WIDTH-1]` and proceeds downward, stopping at the first set bit:

```
data = 32'h8000_0000 -> clz =  0   (MSB is already set)
data = 32'h0000_0001 -> clz = 31   (31 zeros above the LSB)
data = 32'h0000_0000 -> clz = WIDTH
```

For the complementary count from the LSB upward, use
**[count_trailing_zeros](count_trailing_zeros.md)**.

> **History - do not reintroduce input reversal.** Earlier revisions of this module
> scanned from bit 0 upward, which computes *trailing* zeros, not leading zeros,
> despite the module name. Callers compensated by bit-reversing their input before
> connecting it. Both the module and every caller have been corrected: the module now
> performs a true MSB-down scan, and callers pass their operand straight in. Any
> reversal generate block or `w_*_reversed` wire feeding this module is stale and must
> not be re-added. If you actually want the LSB-up count, instantiate
> `count_trailing_zeros` instead of reversing the input.

## Module Interface
```systemverilog
module count_leading_zeros #(
    parameter int WIDTH = 32
) (
    input  logic [      WIDTH-1:0] data,
    output logic [$clog2(WIDTH):0] clz
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `WIDTH` | `int` | `32` | Bit width of the input data |

`WIDTH` can be any positive integer ≥ 1; 8, 16, 32, and 64 are the common values for standard data widths. It determines the output width and algorithm complexity, and it's the only parameter.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| `data` | WIDTH | Input data word to analyze |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| `clz` | `$clog2(WIDTH)+1` | Count of leading zeros |

The output width `$clog2(WIDTH)+1` ensures the port can represent all possible counts:
- **Range**: 0 to WIDTH (inclusive)
- **Example**: For WIDTH=32, output is 6 bits (0-32 requires 6 bits)
- **Special Case**: All zeros input produces CLZ = WIDTH

## Functional Description

### Function-Based Approach

```systemverilog
function automatic [$clog2(WIDTH):0] clz_func;
    input [WIDTH-1:0] input_data;
    logic found;
    begin
        clz_func = 0;
        found = 1'b0;
        // Scan from the MSB downward.
        for (int i = WIDTH - 1; i >= 0; i--) begin
            if (!input_data[i] && !found) begin
                clz_func += 1;
            end else begin
                found = 1'b1;  // Stop counting when first '1' found
            end
        end
    end
endfunction
```

### Bit Scanning Process

The algorithm scans from MSB to LSB:
1. **Initialize**: `clz_func = 0`, `found = 0`
2. **Scan Loop**: For each bit position i from WIDTH-1 down to 0:
   - If `data[i] == 0` AND no '1' found yet: increment count
   - If `data[i] == 1`: set found flag, stop counting
3. **Result**: Final count is the number of zeros above the highest set bit

### Why MSB-to-LSB Scanning?

"Leading" refers to the bits that lead the word when it is written out, which is the
MSB side. The loop therefore starts at `data[WIDTH-1]` and walks down:
- **Bit Order**: `data[0]` is LSB, `data[WIDTH-1]` is MSB
- **Termination**: The `found` flag latches at the highest set bit, so all zeros below
  it are ignored - only the contiguous run above it is counted
- **Count Logic**: `clz = (WIDTH-1) - position_of_highest_set_one`, and `clz = WIDTH`
  when no bit is set

Because the scan direction already matches the definition, the input must be fed in
directly. Reversing `data` before connecting it turns this module back into a trailing
zero counter - see the history note above.

## Examples and Truth Tables

### 8-bit Examples (WIDTH=8)

The count is set by the **highest** set bit; bits below it never affect the result.

| Input (data) | Binary | Highest set bit | Leading Zeros | CLZ Output |
|--------------|---------|--------------|---------------|------------|
| 8'b00000000 | 00000000 | None | 8 | 8 |
| 8'b00000001 | 00000001 | Bit 0 | 7 | 7 |
| 8'b00000010 | 00000010 | Bit 1 | 6 | 6 |
| 8'b00000100 | 00000100 | Bit 2 | 5 | 5 |
| 8'b00001000 | 00001000 | Bit 3 | 4 | 4 |
| 8'b00010000 | 00010000 | Bit 4 | 3 | 3 |
| 8'b00100000 | 00100000 | Bit 5 | 2 | 2 |
| 8'b01000000 | 01000000 | Bit 6 | 1 | 1 |
| 8'b10000000 | 10000000 | Bit 7 | 0 | 0 |
| 8'b11111111 | 11111111 | Bit 7 | 0 | 0 |
| 8'b10101010 | 10101010 | Bit 7 | 0 | 0 |
| 8'b00010101 | 00010101 | Bit 4 | 3 | 3 |
| 8'b00110000 | 00110000 | Bit 5 | 2 | 2 |

### 32-bit Examples

| Input | Hex | Leading Zeros | CLZ |
|-------|-----|---------------|-----|
| 32'h00000000 | 0x00000000 | 32 | 32 |
| 32'h00000001 | 0x00000001 | 31 | 31 |
| 32'h00000080 | 0x00000080 | 24 | 24 |
| 32'h00008000 | 0x00008000 | 16 | 16 |
| 32'h00800000 | 0x00800000 | 8 | 8 |
| 32'h80000000 | 0x80000000 | 0 | 0 |
| 32'hFFFFFFFF | 0xFFFFFFFF | 0 | 0 |

## Usage Examples

### 1. Floating-Point Normalization

```systemverilog
// IEEE 754 floating-point normalization
logic [31:0] mantissa_raw;
logic [5:0] shift_amount;
logic [31:0] normalized_mantissa;

count_leading_zeros #(.WIDTH(32)) norm_clz (
    .data(mantissa_raw),
    .clz(shift_amount)
);

// Normalize mantissa by shifting left
assign normalized_mantissa = mantissa_raw << shift_amount;

// Adjust exponent accordingly
logic [7:0] adjusted_exponent;
assign adjusted_exponent = raw_exponent - shift_amount;
```

### 2. Priority Encoder

```systemverilog
// Find highest priority request
logic [15:0] request_vector;
logic [4:0]  leading_zeros;
logic [3:0]  highest_priority;
logic any_request;

count_leading_zeros #(.WIDTH(16)) priority_enc (
    .data(request_vector),
    .clz(leading_zeros)
);

assign any_request = (leading_zeros != 16);
assign highest_priority = any_request ? (15 - leading_zeros) : 4'b0;

// Example: request_vector = 16'b0000_0100_1000_0000
// Highest set bit is bit 10
// CLZ = 5 (five leading zeros above bit 10)
// highest_priority = 15 - 5 = 10
```

### 3. Bit Width Calculation

```systemverilog
// Determine minimum bits needed to represent a number
logic [31:0] number;
logic [5:0] min_bits_needed;

count_leading_zeros #(.WIDTH(32)) bit_width_calc (
    .data(number),
    .clz(leading_zeros)
);

assign min_bits_needed = (number == 0) ? 1 : (32 - leading_zeros);

// Examples:
// number = 0      → min_bits = 1
// number = 1      → min_bits = 1  
// number = 255    → min_bits = 8
// number = 256    → min_bits = 9
// number = 65535  → min_bits = 16
```

### 4. Log2 Calculation

```systemverilog
// Calculate floor(log2(x)) for x > 0
logic [31:0] input_value;
logic [4:0] log2_result;
logic valid;

count_leading_zeros #(.WIDTH(32)) log2_calc (
    .data(input_value),
    .clz(leading_zeros)
);

assign valid = (input_value != 0);
assign log2_result = valid ? (31 - leading_zeros) : 5'b0;

// Examples:
// input = 1    → log2 = 0
// input = 2    → log2 = 1
// input = 4    → log2 = 2
// input = 7    → log2 = 2 (floor)
// input = 8    → log2 = 3
```

### 5. Data Compression - Run Length Encoding

```systemverilog
// Count leading zeros for compression
logic [63:0] data_block;
logic [6:0] zero_run_length;

count_leading_zeros #(.WIDTH(64)) rle_counter (
    .data(data_block),
    .clz(zero_run_length)
);

// Use in compression algorithm
if (zero_run_length > THRESHOLD) begin
    // Encode as zero run
    compressed_data = {RLE_CODE, zero_run_length};
end else begin
    // Encode as literal data
    compressed_data = {LITERAL_CODE, data_block};
end
```

1. **CPU/DSP Cores**: Instruction implementation (CLZ instruction)
2. **Floating-Point Units**: Mantissa normalization
3. **Network Processors**: Longest prefix matching
4. **Compression Engines**: Run-length encoding optimization
5. **Memory Controllers**: Priority arbitration
6. **Graphics Processors**: Texture coordinate processing
7. **Cryptographic Units**: Bit manipulation operations

## Advanced Variants

### 1. Pipeline Version for High Speed

```systemverilog
module count_leading_zeros_pipelined #(
    parameter int WIDTH = 32,
    parameter int STAGES = 2
) (
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic [WIDTH-1:0]       data,
    output logic [$clog2(WIDTH):0] clz
);

// Stage 1: Partial counting
logic [WIDTH-1:0] data_s1;
logic [$clog2(WIDTH):0] partial_clz_s1;

always_ff @(posedge clk) begin
    data_s1 <= data;
    // Count leading zeros in upper half
    partial_clz_s1 <= clz_upper_half(data);
end

// Stage 2: Complete counting
always_ff @(posedge clk) begin
    if (partial_clz_s1 == WIDTH/2) begin
        // All upper bits are zero, count in lower half
        clz <= WIDTH/2 + clz_lower_half(data_s1);
    end else begin
        // Found '1' in upper half
        clz <= partial_clz_s1;
    end
end

endmodule
```

### 2. Hierarchical Implementation

```systemverilog
// Divide and conquer approach for large widths
module count_leading_zeros_hierarchical #(
    parameter int WIDTH = 64
) (
    input  logic [WIDTH-1:0]       data,
    output logic [$clog2(WIDTH):0] clz
);

localparam int HALF_WIDTH = WIDTH/2;

logic [$clog2(HALF_WIDTH):0] clz_upper, clz_lower;
logic upper_all_zeros;

// Count in upper half
count_leading_zeros #(.WIDTH(HALF_WIDTH)) upper_clz (
    .data(data[WIDTH-1:HALF_WIDTH]),
    .clz(clz_upper)
);

// Count in lower half
count_leading_zeros #(.WIDTH(HALF_WIDTH)) lower_clz (
    .data(data[HALF_WIDTH-1:0]),
    .clz(clz_lower)
);

assign upper_all_zeros = (clz_upper == HALF_WIDTH);

// Combine results
assign clz = upper_all_zeros ? (HALF_WIDTH + clz_lower) : clz_upper;

endmodule
```

### 3. LUT-Based Implementation (Small Widths)

```systemverilog
// Optimized for small widths using a wildcard case statement.
// casez is required so that '?' is treated as a don't-care.
module count_leading_zeros_lut #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0]       data,
    output logic [$clog2(WIDTH):0] clz
);

always_comb begin
    casez (data)
        8'b00000000: clz = 8;
        8'b00000001: clz = 7;
        8'b0000001?: clz = 6;
        8'b000001??: clz = 5;
        8'b00001???: clz = 4;
        8'b0001????: clz = 3;
        8'b001?????: clz = 2;
        8'b01??????: clz = 1;
        8'b1???????: clz = 0;
        default:     clz = 0;
    endcase
end

endmodule
```

## Timing Characteristics

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
- **Scalability**: Linear increase in logic for function implementation

## Testing

### Test Scenarios

1. **Boundary Cases**: All zeros, all ones, single bit patterns
2. **Random Patterns**: Comprehensive random testing
3. **Systematic Sweep**: Test all possible leading zero counts
4. **Corner Cases**: Maximum width values, alternating patterns

### Coverage Model

```systemverilog
covergroup clz_cg;
    cp_leading_zeros: coverpoint clz {
        bins zero_clz = {0};
        bins low_clz = {[1:WIDTH/4]};
        bins mid_clz = {[WIDTH/4+1:3*WIDTH/4]};
        bins high_clz = {[3*WIDTH/4+1:WIDTH-1]};
        bins all_zeros = {WIDTH};
    }
    
    cp_data_patterns: coverpoint data {
        bins all_zeros = {'0};
        bins all_ones = {'1};
        bins single_bit[] = {1, 2, 4, 8, 16, 32}; // For appropriate WIDTH
        bins msb_set = {1 << (WIDTH-1)};
        bins mixed[] = {[1:2**(WIDTH-1)-1]};
    }
endgroup
```

### Assertions

```systemverilog
// CLZ should never exceed WIDTH
property clz_bounds;
    clz <= WIDTH;
endproperty

// All zeros should give CLZ = WIDTH
property all_zeros_case;
    (data == '0) |-> (clz == WIDTH);
endproperty

// MSB set should give CLZ = 0
property msb_set_case;
    data[WIDTH-1] |-> (clz == 0);
endproperty

// Relationship between CLZ and first '1' position
property clz_correctness;
    logic [WIDTH-1:0] shifted;
    assign shifted = data << clz;
    (data != '0) |-> shifted[WIDTH-1];
endproperty

assert property (clz_bounds);
assert property (all_zeros_case);
assert property (msb_set_case);
assert property (clz_correctness);
```

## Design Notes

### Tool-Specific Attributes

```systemverilog
// Xilinx: Prevent SRL inference for better timing
(* SRL_STYLE = "register" *) logic [WIDTH-1:0] data_reg;

// Intel/Altera: Use specific LUT implementation
// synthesis attribute LUT_SIZE of clz_func is 6;
```

### Area vs. Speed Trade-offs

```systemverilog
// For area optimization: Use iterative approach
// For speed optimization: Use tree-based or LUT approach
// For power optimization: Add enable signals and clock gating
```

## Related Modules

- **[count_trailing_zeros](count_trailing_zeros.md)** - the LSB-up counterpart. Use CLZ
  when you care about the magnitude of a value (normalization, log2, bit width); use
  CTZ when you care about alignment or the lowest pending request.
- Population count (number of '1' bits)
- Find first set (FFS) / Find last set (FLS)
- Priority encoders
- Barrel shifters

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
