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

# BF16 Adder

A pipelined BF16 (Brain Float 16) floating-point adder with IEEE 754-compliant special case handling, Round-to-Nearest-Even rounding, and flush-to-zero support for subnormal numbers.

## Overview

The `math_bf16_adder` module implements full BF16 addition and subtraction with configurable pipeline stages for frequency/latency tradeoffs. It follows industry-standard practices used in AI/ML accelerators for efficient 16-bit floating-point operations.

**Key Features:**
- **BF16 format** - Same exponent range as FP32, reduced mantissa precision
- **Configurable pipeline** - 4 optional pipeline stages for frequency optimization
- **IEEE 754 special cases** - Zero, infinity, NaN handling
- **RNE rounding** - Round-to-Nearest-Even for unbiased results
- **FTZ mode** - Flush-to-Zero for subnormal inputs and outputs
- **Status flags** - Overflow, underflow, and invalid operation indicators
- **Valid handshaking** - Input/output valid signals for pipeline control

## Module Declaration

```systemverilog
module math_bf16_adder #(
    parameter int PIPE_STAGE_1 = 0,  // After exponent diff + swap
    parameter int PIPE_STAGE_2 = 0,  // After alignment shifter
    parameter int PIPE_STAGE_3 = 0,  // After mantissa add/sub
    parameter int PIPE_STAGE_4 = 0   // After normalize
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [15:0] i_a,            // BF16 operand A
    input  logic [15:0] i_b,            // BF16 operand B
    input  logic        i_valid,        // Input valid
    output logic [15:0] ow_result,      // BF16 sum/difference
    output logic        ow_overflow,    // Overflow to infinity
    output logic        ow_underflow,   // Underflow to zero
    output logic        ow_invalid,     // Invalid operation (NaN)
    output logic        ow_valid        // Output valid
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| PIPE_STAGE_1 | 0 | Register after exponent compare and operand swap |
| PIPE_STAGE_2 | 0 | Register after mantissa alignment |
| PIPE_STAGE_3 | 0 | Register after mantissa add/subtract |
| PIPE_STAGE_4 | 0 | Register after normalization |

**Latency Formula:** `1 + PIPE_STAGE_1 + PIPE_STAGE_2 + PIPE_STAGE_3 + PIPE_STAGE_4` cycles

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_clk | Input | 1 | Clock signal |
| i_rst_n | Input | 1 | Active-low asynchronous reset |
| i_a | Input | 16 | BF16 addend A |
| i_b | Input | 16 | BF16 addend B |
| i_valid | Input | 1 | Input operands are valid |
| ow_result | Output | 16 | BF16 sum (A + B) |
| ow_overflow | Output | 1 | 1 if result overflowed to infinity |
| ow_underflow | Output | 1 | 1 if result underflowed to zero |
| ow_invalid | Output | 1 | 1 if operation was invalid (inf - inf) |
| ow_valid | Output | 1 | Output result is valid |

## BF16 Format

```
BF16: [15]=sign, [14:7]=exponent (8 bits, bias=127), [6:0]=mantissa (7 bits)

Special values:
  +0:    0x0000 (sign=0, exp=0, mant=0)
  -0:    0x8000 (sign=1, exp=0, mant=0)
  +inf:  0x7F80 (sign=0, exp=255, mant=0)
  -inf:  0xFF80 (sign=1, exp=255, mant=0)
  NaN:   0x7FC0 (exp=255, mant!=0, canonical quiet NaN)
```

## Architecture

### Block Diagram

```
                    +-----------------------------------------------------+
                    |              math_bf16_adder                        |
                    |                                                     |
    i_a[15:0] ------+--+-- sign_a, exp_a, mant_a                         |
                    |  |                                                  |
    i_b[15:0] ------+--+-- sign_b, exp_b, mant_b                         |
                    |  |                                                  |
    i_valid --------+--+                                                  |
                    |  |                                                  |
                    |  v                                                  |
                    | +--------------------------------------------------+|
                    | | Stage A: Unpack + Special Cases + Compare + Swap ||
                    | |   - Exponent difference calculation              ||
                    | |   - Magnitude comparison and operand swap        ||
                    | |   - Effective operation determination            ||
                    | +--------------------------------------------------+|
                    |                     | [PIPE_STAGE_1]                |
                    |                     v                               |
                    | +--------------------------------------------------+|
                    | | Stage B: Mantissa Alignment                      ||
                    | |   - shifter_barrel (right shift smaller operand) ||
                    | |   - Sticky bit computation                       ||
                    | +--------------------------------------------------+|
                    |                     | [PIPE_STAGE_2]                |
                    |                     v                               |
                    | +--------------------------------------------------+|
                    | | Stage C: Mantissa Add/Subtract                   ||
                    | |   - 12-bit addition or subtraction               ||
                    | |   - Overflow detection                           ||
                    | +--------------------------------------------------+|
                    |                     | [PIPE_STAGE_3]                |
                    |                     v                               |
                    | +--------------------------------------------------+|
                    | | Stage D: Normalization                           ||
                    | |   - count_leading_zeros for shift amount         ||
                    | |   - shifter_barrel for normalization             ||
                    | |   - Exponent adjustment                          ||
                    | +--------------------------------------------------+|
                    |                     | [PIPE_STAGE_4]                |
                    |                     v                               |
                    | +--------------------------------------------------+|
                    | | Stage E: Rounding + Result Assembly              ||
                    | |   - RNE rounding with guard/round/sticky         ||
                    | |   - Special case priority selection              ||
                    | +--------------------------------------------------+|
                    |                                                     |
    ow_result[15:0] <-----------------------------------------------------+
    ow_overflow <---------------------------------------------------------+
    ow_underflow <--------------------------------------------------------+
    ow_invalid <----------------------------------------------------------+
    ow_valid <------------------------------------------------------------+
                    +-----------------------------------------------------+
```

### Processing Pipeline

1. **Stage A: Unpack + Compare + Swap**
   - Parse sign, exponent, mantissa from both inputs
   - Detect special cases (zero, subnormal, infinity, NaN)
   - Compare magnitudes and swap so larger operand is always "L"
   - Determine effective operation (add or subtract based on signs)

2. **Stage B: Mantissa Alignment**
   - Extend mantissas with implied bit and guard bits (11 bits)
   - Right-shift smaller mantissa by exponent difference
   - Compute sticky bit from shifted-out bits

3. **Stage C: Mantissa Add/Subtract**
   - Add or subtract aligned mantissas (12-bit operation)
   - Detect addition overflow (sum >= 2.0)

4. **Stage D: Normalization**
   - Count leading zeros for subtraction results
   - Shift to normalize (implied 1 at correct position)
   - Adjust exponent accordingly

5. **Stage E: Rounding + Result Assembly**
   - Apply RNE rounding using guard/round/sticky bits
   - Handle rounding overflow
   - Select result based on special case priority

## Functionality

### Exponent Comparison and Swap

```systemverilog
// Compare magnitudes: larger operand becomes "L", smaller becomes "S"
wire [8:0]  w_exp_diff_raw = {1'b0, w_exp_a} - {1'b0, w_exp_b};
wire        w_a_larger     = w_exp_a_larger && (~w_exp_equal || w_mant_a_larger);

// Absolute exponent difference for alignment shift
wire [7:0]  w_exp_diff     = w_a_larger ? (w_exp_a - w_exp_b) : (w_exp_b - w_exp_a);
```

### Mantissa Alignment

```systemverilog
// Extend mantissas: {implied_1, mant[6:0], guard, round, sticky} = 11 bits
wire [10:0] w_mant_l_ext = {r1_l_is_normal, r1_mant_l, 3'b000};
wire [10:0] w_mant_s_ext = {r1_s_is_normal, r1_mant_s, 3'b000};

// Right-shift smaller mantissa using barrel shifter
shifter_barrel #(.WIDTH(11)) u_align_shifter (
    .data        (w_mant_s_ext),
    .ctrl        (SHIFT_RIGHT_LOGIC),
    .shift_amount(w_shift_amt),
    .data_out    (w_mant_s_aligned)
);
```

### Round-to-Nearest-Even

```systemverilog
// Extract rounding bits from normalized mantissa
wire [6:0] w_mant_final_raw = r4_mant_normalized[9:3];
wire       w_guard_bit      = r4_mant_normalized[2];
wire       w_round_bit      = r4_mant_normalized[1];
wire       w_sticky_bit     = r4_mant_normalized[0] | r4_norm_sticky;

// RNE: Round up if guard && (round || sticky || LSB)
wire w_round_up = w_guard_bit && (w_round_bit || w_sticky_bit || w_mant_final_raw[0]);
```

### Special Case Priority

```systemverilog
always_comb begin
    // Default: normal result
    ow_result = {w_final_sign, w_exp_out, w_mant_out};

    // Priority order (highest to lowest):
    if (r4_any_nan || r4_inf_minus_inf) begin
        // 1. NaN: any NaN input, or inf - inf
        ow_result  = {1'b0, 8'hFF, 7'h40};  // Canonical qNaN
        ow_invalid = r4_inf_minus_inf;
    end else if (r4_any_inf) begin
        // 2. Infinity: inf input (not inf-inf case)
        ow_result = {inf_sign, 8'hFF, 7'h00};
    end else if (r4_sum_is_zero) begin
        // 3. Exact zero from subtraction
        ow_result = {1'b0, 8'h00, 7'h00};  // +0 per IEEE 754 RNE
    end else if (w_final_overflow) begin
        // 4. Overflow to infinity
        ow_result   = {w_final_sign, 8'hFF, 7'h00};
        ow_overflow = 1'b1;
    end else if (r4_exp_underflow) begin
        // 5. Underflow to zero (FTZ)
        ow_result    = {w_final_sign, 8'h00, 7'h00};
        ow_underflow = 1'b1;
    end
end
```

## Usage Examples

### Basic Addition (Combinational)

```systemverilog
logic [15:0] a, b, sum;
logic overflow, underflow, invalid, valid;

math_bf16_adder u_adder (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_a(a),
    .i_b(b),
    .i_valid(1'b1),
    .ow_result(sum),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_invalid(invalid),
    .ow_valid(valid)
);

// Example: 1.0 + 1.0 = 2.0
// 1.0 in BF16: 0x3F80 (sign=0, exp=127, mant=0)
// 2.0 in BF16: 0x4000 (sign=0, exp=128, mant=0)
initial begin
    a = 16'h3F80;  // 1.0
    b = 16'h3F80;  // 1.0
    #1;
    // sum should be 0x4000 (2.0)
end
```

### Pipelined Configuration

```systemverilog
// 4-stage pipeline for high frequency
math_bf16_adder #(
    .PIPE_STAGE_1(1),
    .PIPE_STAGE_2(1),
    .PIPE_STAGE_3(1),
    .PIPE_STAGE_4(1)
) u_adder_pipelined (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_a(a),
    .i_b(b),
    .i_valid(in_valid),
    .ow_result(sum),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_invalid(invalid),
    .ow_valid(out_valid)  // Valid 5 cycles after in_valid
);
```

### Subtraction via Sign Manipulation

```systemverilog
// To compute A - B, negate B's sign and add
logic [15:0] a_minus_b;
logic [15:0] b_negated;

assign b_negated = {~b[15], b[14:0]};  // Flip sign bit

math_bf16_adder u_subtractor (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_a(a),
    .i_b(b_negated),
    .i_valid(1'b1),
    .ow_result(a_minus_b),
    // ...
);
```

### With Status Checking

```systemverilog
always_ff @(posedge clk) begin
    if (out_valid) begin
        if (invalid)
            $display("Invalid operation: inf - inf");
        else if (overflow)
            $display("Overflow: result is infinity");
        else if (underflow)
            $display("Underflow: result is zero");
    end
end
```

## Pipeline Latency Configurations

| Configuration | Latency | Use Case |
|---------------|---------|----------|
| [0,0,0,0] | 1 cycle | Area-constrained, low frequency |
| [1,0,0,0] | 2 cycles | Balance input timing |
| [0,0,0,1] | 2 cycles | Balance output timing |
| [1,1,1,1] | 5 cycles | Maximum frequency |

## Performance Characteristics

### Resource Utilization (Estimated)

| Component | LUTs (est.) |
|-----------|-------------|
| Unpack + compare | ~40 |
| Alignment shifter | ~50 |
| Mantissa adder | ~30 |
| CLZ + normalize | ~60 |
| Rounding logic | ~20 |
| Result MUX | ~30 |
| Pipeline regs (per stage) | ~50 |
| **Total (comb)** | ~230 LUTs |
| **Total (4-stage)** | ~430 LUTs |

### Timing Characteristics

| Stage | Logic Depth |
|-------|-------------|
| Exponent compare | ~3 gates |
| Alignment shift | ~4 gates (log2) |
| Mantissa add | ~5 gates |
| CLZ + normalize | ~6 gates |
| Rounding | ~3 gates |
| **Total (comb)** | ~20-25 gates |

## Design Considerations

### Flush-to-Zero (FTZ)

Subnormal numbers are flushed to zero:
- **Input subnormals** - Treated as zero (effective zero)
- **Output subnormals** - Not generated (result goes to zero)

This simplifies hardware and matches AI accelerator conventions.

### Invalid Operation (inf - inf)

When adding +inf and -inf (or -inf and +inf):
- Result is canonical quiet NaN (0x7FC0)
- `ow_invalid` flag is asserted

### Sign of Zero

The sign of zero follows IEEE 754:
- **x - x = +0** (in RNE rounding mode)
- **-0 + -0 = -0**
- **+0 + -0 = +0**

### Rounding Mode

Only Round-to-Nearest-Even (RNE) is supported. This is standard for BF16 in AI applications.

## Dependencies

This module instantiates:
- **shifter_barrel** - Used for alignment shifting and normalization
- **count_leading_zeros** - Used for determining normalization shift amount

## Common Pitfalls

**Anti-Pattern 1:** Ignoring valid signals
```systemverilog
// WRONG: Capturing result without checking valid
result <= ow_result;  // May capture invalid data during pipeline fill

// RIGHT: Only capture when valid
if (ow_valid)
    result <= ow_result;
```

**Anti-Pattern 2:** Forgetting pipeline latency
```systemverilog
// WRONG: Expecting immediate result with pipeline
i_a <= operand_a;
i_b <= operand_b;
i_valid <= 1'b1;
@(posedge clk);
sum <= ow_result;  // Result not ready yet!

// RIGHT: Account for latency
// With [1,1,1,1] config, wait 5 cycles for result
```

**Anti-Pattern 3:** Not handling special flags
```systemverilog
// WRONG: Using result without checking flags
accumulator <= accumulator + ow_result;  // May be NaN or infinity!

// RIGHT: Check flags first
if (ow_valid && !ow_invalid && !ow_overflow)
    accumulator <= accumulator + ow_result;
```

## Related Modules

- **math_bf16_multiplier** - BF16 multiplication
- **math_bf16_fma** - Fused Multiply-Add with FP32 accumulator
- **shifter_barrel** - Used internally for mantissa alignment
- **count_leading_zeros** - Used internally for normalization

## References

- Google Brain Float (BF16) specification
- IEEE 754-2019 Standard for Floating-Point Arithmetic
- Intel BFloat16 documentation
- NVIDIA TensorFloat documentation
- Muller, J.M. et al. "Handbook of Floating-Point Arithmetic." Birkhauser, 2018.

## Navigation

- **[<- Back to RTLCommon Index](index.md)**
- **[<- Back to Main Documentation Index](../../index.md)**
