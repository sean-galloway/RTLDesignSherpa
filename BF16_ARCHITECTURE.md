# BF16 Multiplier Architecture Specification

High-performance BF16 (Brain Float 16) arithmetic units optimized for AI/ML inference and training workloads. This implementation targets 1.6GHz operation on TSMC 5nm with 40% timing margin, using Dadda reduction with 4:2 compressors and Han-Carlson prefix adders.

## Overview

The BF16 multiplier family implements IEEE-754-like floating-point multiplication optimized for neural network operations. The architecture follows industry conventions established by Google TPU, NVIDIA Tensor Cores, and AMD Matrix Cores.

**Key Features:**
- **1.6GHz target frequency** on TSMC 5nm (conservative, 40% margin)
- **3-stage Dadda tree** with 4:2 compressors (vs 4 stages with CSA)
- **Han-Carlson prefix adders** (16-bit for multiplier CPA, 48-bit for FMA)
- **FP32 accumulation** support for training accuracy
- **Relaxed IEEE semantics** (FTZ subnormals, no exception flags)
- **Round-to-Nearest-Even** (RNE) rounding

**Architecture Components:**

| Module | Purpose | Critical Path |
|--------|---------|---------------|
| `math_adder_han_carlson_016` | 16-bit prefix adder (multiplier CPA) | 5 logic levels |
| `math_adder_han_carlson_048` | 48-bit prefix adder (FMA addition) | 7 logic levels |
| `math_multiplier_dadda_4to2_008` | 8x8 mantissa multiply | 3 reduction stages |
| `math_bf16_mantissa_mult` | Mantissa multiplier wrapper | ~270ps |
| `math_bf16_exponent_adder` | Exponent add with bias | ~50ps |
| `math_bf16_multiplier` | Complete BF16 multiplier | ~375ps |
| `math_bf16_fma` | FMA with FP32 accumulator | ~500ps |

## BF16 Format Specification

BF16 (Brain Float 16) is a 16-bit floating-point format that truncates FP32:

```
BF16 Format (16 bits):
[15]     - Sign bit (1 bit)
[14:7]   - Exponent (8 bits, bias = 127)
[6:0]    - Mantissa (7 bits explicit, 1 bit implied)

FP32 Format (32 bits):
[31]     - Sign bit (1 bit)
[30:23]  - Exponent (8 bits, bias = 127)
[22:0]   - Mantissa (23 bits explicit, 1 bit implied)

Conversion: BF16 = FP32[31:16] (simple truncation)
```

**Special Values:**

| Value | Sign | Exponent | Mantissa | Description |
|-------|------|----------|----------|-------------|
| +0 | 0 | 0x00 | 0x00 | Positive zero |
| -0 | 1 | 0x00 | 0x00 | Negative zero |
| +Inf | 0 | 0xFF | 0x00 | Positive infinity |
| -Inf | 1 | 0xFF | 0x00 | Negative infinity |
| NaN | X | 0xFF | != 0 | Not a Number |
| Subnormal | X | 0x00 | != 0 | Flushed to zero (FTZ) |

**Design Decisions (Industry Standard):**
- Subnormals flushed to zero (simplifies datapath)
- No signaling NaN propagation
- No IEEE exception flags
- Round-to-Nearest-Even (RNE) by default

## Module Declarations

### Han-Carlson Prefix Adder (16-bit)

```systemverilog
module math_adder_han_carlson_016 #(
    parameter int N = 16
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic         i_cin,     // Carry input
    output logic [N-1:0] ow_sum,    // Sum output
    output logic         ow_cout    // Carry output
);
```

### Han-Carlson Prefix Adder (48-bit)

Used for the wide mantissa addition in the FMA unit.

```systemverilog
module math_adder_han_carlson_048 #(
    parameter int N = 48
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic         i_cin,     // Carry input
    output logic [N-1:0] ow_sum,    // Sum output
    output logic         ow_cout    // Carry output
);
```

### Dadda 4:2 Multiplier (8-bit)

```systemverilog
module math_multiplier_dadda_4to2_008 #(
    parameter int N = 8
) (
    input  logic [N-1:0]   i_multiplier,    // 8-bit unsigned
    input  logic [N-1:0]   i_multiplicand,  // 8-bit unsigned
    output logic [2*N-1:0] ow_product       // 16-bit unsigned
);
```

### BF16 Multiplier

```systemverilog
module math_bf16_multiplier (
    input  logic [15:0] i_a,           // BF16 operand A
    input  logic [15:0] i_b,           // BF16 operand B
    output logic [15:0] ow_result,     // BF16 product
    output logic        ow_overflow,   // Overflow to infinity
    output logic        ow_underflow,  // Underflow to zero
    output logic        ow_invalid     // Invalid operation (NaN)
);
```

### BF16 FMA with FP32 Accumulator

```systemverilog
module math_bf16_fma (
    input  logic [15:0] i_a,           // BF16 operand A
    input  logic [15:0] i_b,           // BF16 operand B
    input  logic [31:0] i_c,           // FP32 addend/accumulator
    output logic [31:0] ow_result,     // FP32 result = (a * b) + c
    output logic        ow_overflow,   // Overflow
    output logic        ow_underflow,  // Underflow
    output logic        ow_invalid     // Invalid operation (NaN)
);
```

## Architecture Details

### Block Diagrams

Visual representations of the BF16 arithmetic units:

**BF16 Multiplier:**

![BF16 Multiplier Block Diagram](bf16_multiplier_diagram.jpg)

**BF16 FMA:**

![BF16 FMA Block Diagram](bf16_fma_diagram.jpg)

### Han-Carlson Prefix Adder

The Han-Carlson adder is a **sparsity-2 hybrid** combining Kogge-Stone and Brent-Kung characteristics:

**Structure:**
1. **Stage 1**: Parallel prefix on even positions only (span-1)
2. **Stages 2-4**: Brent-Kung style tree on even positions
3. **Stage 5**: Fill odd positions from even neighbors (ripple)

**Comparison with Other Prefix Adders:**

| Architecture | Logic Levels (16-bit) | Prefix Cells | Wiring Tracks | 5nm Suitability |
|-------------|----------------------|--------------|---------------|-----------------|
| Kogge-Stone | 4 | 64 | 8 | Poor (routing) |
| Sklansky | 4 | 30 | 1 | Poor (fanout to 9) |
| **Han-Carlson** | **5** | **39** | **4** | **Excellent** |
| Brent-Kung | 6 | 26 | 1 | Good (too slow) |
| Ladner-Fischer | 4 | 47 | 2-4 | Good |

**Why Han-Carlson for 5nm:**
- **Wire delay dominates**: At 5nm, 1mm wire = ~1,200ps delay
- **Routing congestion**: Kogge-Stone's 8 wiring tracks create congestion
- **Constant fanout**: Han-Carlson maintains fanout of 2 (vs exponential for Sklansky)
- **Area efficiency**: 40% fewer cells than Kogge-Stone

**Implementation:**

```systemverilog
// Stage 0: Initial P and G computation
assign w_p0[i] = i_a[i] ^ i_b[i];  // Propagate
assign w_g0[i] = i_a[i] & i_b[i];  // Generate

// Stage 1: Span-1 prefix (even positions only)
// Even positions: combine with previous bit
math_prefix_cell u_pf_s1 (
    .i_g_hi(w_g0[i]),   .i_p_hi(w_p0[i]),
    .i_g_lo(w_g0[i-1]), .i_p_lo(w_p0[i-1]),
    .ow_g(w_g1[i]),     .ow_p(w_p1[i])
);

// Stages 2-4: Brent-Kung style on even positions
// Stage 5: Gray cells fill odd positions
math_prefix_cell_gray u_pf_s5 (
    .i_g_hi(w_g4[i]), .i_p_hi(w_p4[i]),
    .i_g_lo(w_g4[i-1]),
    .ow_g(w_g5[i])    // Only G output needed
);

// Final sum
assign ow_sum[i] = w_p0[i] ^ w_g5[i-1];
```

### Dadda Tree with 4:2 Compressors

The Dadda reduction tree uses **4:2 compressors** instead of 3:2 CSA cells:

**4:2 Compressor Characteristics:**
- **Inputs**: X1, X2, X3, X4, Cin (5 inputs)
- **Outputs**: Sum, Carry, Cout (3 outputs)
- **Key property**: Cout independent of Cin (enables efficient chaining)
- **Critical path**: 3 XOR delays (vs 4 for two cascaded full adders)

**Reduction Schedule (8x8):**

| Stage | Target Height | Compressors Used | Delay |
|-------|--------------|------------------|-------|
| Initial | 8 | - | - |
| Stage 1 | 6 | ~6 (4:2) | 3 XOR |
| Stage 2 | 4 | ~6 (4:2) | 3 XOR |
| Stage 3 | 2 | ~6 (4:2 + FA/HA) | 3 XOR |
| **Total** | **2** | **~18 compressors** | **9 XOR** |

**Comparison: 4:2 vs 3:2 Compressors:**

| Metric | 3:2 CSA (Traditional) | 4:2 Compressor |
|--------|----------------------|----------------|
| Reduction stages (8x8) | 4 | 3 |
| XOR delays per stage | 2 | 3 |
| Total XOR delays | 8 | 9 |
| Stage count reduction | Baseline | 25% fewer |
| Practical speed | Similar | Often faster (fewer stages) |

**Implementation:**

```systemverilog
// 4:2 compressor using two cascaded full adders
// Cout is independent of Cin for efficient chaining
math_compressor_4to2 u_c4to2 (
    .i_x1(pp[0]), .i_x2(pp[1]),
    .i_x3(pp[2]), .i_x4(pp[3]),
    .i_cin(1'b0),
    .ow_sum(sum),
    .ow_carry(carry),   // Goes to column + 1
    .ow_cout(cout)      // Goes to column + 1 (independent of cin)
);
```

### BF16 Multiplication Flow

```
1. Field Extraction
   sign_a = i_a[15]
   exp_a  = i_a[14:7]
   mant_a = i_a[6:0]

2. Special Case Detection
   - Zero: exp=0, mant=0
   - Subnormal: exp=0, mant!=0 (flushed to zero)
   - Infinity: exp=FF, mant=0
   - NaN: exp=FF, mant!=0

3. Sign Computation
   sign_result = sign_a ^ sign_b

4. Mantissa Multiplication (8x8)
   mant_a_ext = {is_normal_a, mant_a}  // Add implied 1
   mant_b_ext = {is_normal_b, mant_b}
   product[15:0] = mant_a_ext * mant_b_ext  // Dadda 4:2 tree

5. Normalization Detection
   needs_norm = product[15]  // Product >= 2.0

6. Exponent Addition
   exp_result = exp_a + exp_b - 127 + needs_norm

7. Rounding (RNE)
   round_up = guard & (round | sticky | LSB)
   mant_rounded = mant + round_up

8. Special Case Handling
   Priority: NaN > Inf > Zero > Normal

9. Result Assembly
   result = {sign_result, exp_result, mant_result}
```

### BF16 FMA Flow

The FMA computes `result = (a * b) + c` where a and b are BF16 inputs and c is an FP32 accumulator. The result is FP32.

```
1. Field Extraction (BF16 operands a, b)
   sign_a = i_a[15]
   exp_a  = i_a[14:7]
   mant_a = i_a[6:0]
   (Same for b)

2. Field Extraction (FP32 addend c)
   sign_c = i_c[31]
   exp_c  = i_c[30:23]
   mant_c = i_c[22:0]

3. Special Case Detection
   BF16 (a, b):
   - Zero: exp=0, mant=0
   - Subnormal: exp=0, mant!=0 (flushed to zero)
   - Infinity: exp=FF, mant=0
   - NaN: exp=FF, mant!=0

   FP32 (c):
   - Zero: exp=0, mant=0
   - Subnormal: exp=0, mant!=0 (flushed to zero)
   - Infinity: exp=FF, mant=0
   - NaN: exp=FF, mant!=0

4. BF16 Product (a * b)
   sign_prod = sign_a ^ sign_b
   mant_a_ext = {is_normal_a, mant_a}  // 8 bits with implied 1
   mant_b_ext = {is_normal_b, mant_b}
   prod_mant[15:0] = mant_a_ext * mant_b_ext  // Dadda 4:2 tree
   prod_exp = exp_a + exp_b - 127 + needs_norm

5. Addend Alignment
   exp_diff = prod_exp - exp_c  // Signed difference

   If prod_exp > exp_c:
     mant_larger = prod_mant_48
     mant_smaller = c_mant_48 >> exp_diff
     sign_larger = sign_prod
   Else:
     mant_larger = c_mant_48
     mant_smaller = prod_mant_48 >> |exp_diff|
     sign_larger = sign_c

6. Wide Addition (48-bit Han-Carlson)
   effective_sub = sign_larger ^ sign_smaller

   If effective_sub:
     // Two's complement subtraction: A + (~B + 1)
     adder_b = ~mant_smaller
     cin = 1  // The +1 for two's complement
   Else:
     adder_b = mant_smaller
     cin = 0

   {cout, sum[47:0]} = mant_larger + adder_b + cin

7. Result Sign and Absolute Value
   For subtraction (effective_sub = 1):
     If cout = 0: result is negative (A < B)
       result_sign = ~sign_larger
       sum_abs = -sum  // Second Han-Carlson: ~sum + 1
     Else:
       result_sign = sign_larger
       sum_abs = sum
   For addition:
     result_sign = sign_larger
     sum_abs = sum

8. Normalization
   lz_count = CLZ(sum_abs[47:0])  // Count leading zeros
   mant_normalized = sum_abs << lz_count
   exp_adjusted = exp_result_pre - lz_count + 24

9. Rounding (RNE)
   mant_23 = mant_normalized[47:25]
   guard   = mant_normalized[24]
   round   = mant_normalized[23]
   sticky  = |mant_normalized[22:0]

   round_up = guard & (round | sticky | mant_23[0])
   mant_rounded = mant_23 + round_up

   If mant_rounded overflows:
     mant_final = mant_rounded >> 1
     exp_final = exp_adjusted + 1

10. Special Case Priority
    NaN input or invalid op (0*inf, inf-inf) -> qNaN
    Product is infinity -> infinity (with sign)
    Addend is infinity -> infinity (with sign)
    Overflow -> infinity
    Underflow or zero -> signed zero
    Product is zero -> return c
    Addend is zero -> return product as FP32

11. Result Assembly (FP32)
    result = {result_sign, exp_final[7:0], mant_final[22:0]}
```

**Invalid Operations:**
- Zero times infinity: `(0 * inf)` or `(inf * 0)`
- Infinity minus infinity: `(+inf) + (-inf)` when product and addend have opposite signs

## TSMC 5nm Static Timing Analysis

### Process Characteristics

| Parameter | HP Cells | HD Cells |
|-----------|----------|----------|
| FO4 inverter delay | 10-12ps | 15-20ps |
| NAND2/NOR2 delay | 12-18ps | 20-25ps |
| XOR gate delay | 25-35ps | 35-50ps |
| Wire delay (1mm) | ~1,200ps | ~1,200ps |
| Wire delay (100nm) | ~4ps | ~4ps |

**Reference Commercial Frequencies:**
- Apple M1: 3.2GHz (195ps cycle) - TSMC 5nm
- AMD Zen 4: 5.7GHz (175ps cycle) - TSMC 5nm
- 1.6GHz target: 625ps cycle (conservative)

### BF16 Multiplier Critical Path Analysis

**Target: 1.6GHz (625ps cycle)**

| Component | Estimate | Notes |
|-----------|----------|-------|
| AND gates (PP gen) | ~15ps | Single gate level, 64 parallel |
| 3-stage 4:2 reduction | ~270ps | 9 XOR @ 30ps each |
| Han-Carlson 16-bit CPA | ~75ps | 5 prefix levels @ 15ps |
| Output buffering | ~15ps | Drive external loads |
| **Total critical path** | **~375ps** | **60% of 625ps budget** |
| **Timing margin** | **~250ps** | **40% margin** |

**Critical Path Detail:**

```
i_a[6:0] → mant_a_ext[7] → PP[7][7] → 4:2 Stage 1 →
→ 4:2 Stage 2 → 4:2 Stage 3 → Han-Carlson CPA →
→ Normalization MUX → Rounding adder → ow_result[14:7]
```

### Han-Carlson Adder Timing

| Stage | Operation | Delay |
|-------|-----------|-------|
| Stage 0 | P/G generation (XOR, AND) | ~15ps |
| Stage 1 | Span-1 prefix (even only) | ~15ps |
| Stage 2 | Span-4 prefix | ~15ps |
| Stage 3 | Span-8 prefix | ~15ps |
| Stage 4 | Span-16 prefix | ~15ps |
| Stage 5 | Odd fill (gray cells) | ~15ps |
| Sum | Final XOR | ~15ps |
| **Total** | | **~90-105ps** |

**Effective delay ~75ps** due to parallel operations and optimized synthesis.

### Dadda 4:2 Tree Timing

| Stage | Operation | Delay |
|-------|-----------|-------|
| PP Generation | 64 AND gates (parallel) | ~15ps |
| Reduction 1 | 4:2 compressors (8→6) | ~90ps |
| Reduction 2 | 4:2 compressors (6→4) | ~90ps |
| Reduction 3 | 4:2 compressors (4→2) | ~90ps |
| **Total reduction** | | **~270ps** |

### BF16 FMA Critical Path

The FMA uses structural Han-Carlson adders for both the main addition and negation:

| Component | Estimate | Notes |
|-----------|----------|-------|
| BF16 multiply | ~270ps | Dadda tree portion |
| Alignment shifter | ~30ps | Barrel shifter |
| 48-bit Han-Carlson add | ~120ps | 7 prefix levels @ ~17ps |
| Negate (conditional) | ~120ps | Second Han-Carlson for |w_sum| |
| CLZ + normalization | ~40ps | Leading zero count |
| Rounding | ~20ps | RNE logic |
| **Total** | **~500ps** | 80% of 625ps |

Note: The FMA uses two 48-bit Han-Carlson adders:
1. `u_wide_adder` - Main addition/subtraction (uses cin for two's complement)
2. `u_negate_adder` - Computes absolute value when result is negative

### Area Estimates

| Module | Gates (approx) | Area (5nm) |
|--------|---------------|------------|
| Han-Carlson 16-bit | ~120 | ~0.5 um^2 |
| Han-Carlson 48-bit | ~400 | ~1.5 um^2 |
| Dadda 4:2 8x8 | ~400 | ~1.5 um^2 |
| BF16 mantissa mult | ~450 | ~1.7 um^2 |
| BF16 exponent add | ~100 | ~0.4 um^2 |
| BF16 multiplier | ~700 | ~2.5 um^2 |
| BF16 FMA | ~2,000 | ~7.0 um^2 |

**Comparison to FP32:**
- FP32 mantissa: 24x24 = 576 PP (vs 64 for BF16)
- BF16 is ~8x smaller due to quadratic scaling with mantissa width

## Usage Examples

### Basic BF16 Multiplication

```systemverilog
logic [15:0] a, b, result;
logic overflow, underflow, invalid;

math_bf16_multiplier u_mult (
    .i_a(a),
    .i_b(b),
    .ow_result(result),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_invalid(invalid)
);

// Example: 1.5 * 2.0 = 3.0
// BF16(1.5) = 0x3FC0, BF16(2.0) = 0x4000, BF16(3.0) = 0x4040
initial begin
    a = 16'h3FC0;  // 1.5
    b = 16'h4000;  // 2.0
    #1;
    assert(result == 16'h4040);  // 3.0
end
```

### FMA for Neural Network MAC

```systemverilog
module nn_mac_unit (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] weight,      // BF16 weight
    input  logic [15:0] activation,  // BF16 activation
    input  logic        clear,       // Clear accumulator
    output logic [31:0] accumulator  // FP32 accumulator
);

    logic [31:0] fma_result;
    logic [31:0] acc_in;

    assign acc_in = clear ? 32'h0 : accumulator;

    math_bf16_fma u_fma (
        .i_a(weight),
        .i_b(activation),
        .i_c(acc_in),
        .ow_result(fma_result),
        .ow_overflow(),
        .ow_underflow(),
        .ow_invalid()
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            accumulator <= 32'h0;
        else
            accumulator <= fma_result;
    end

endmodule
```

### Systolic Array Element

```systemverilog
module systolic_pe (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] weight_in,
    input  logic [15:0] activation_in,
    input  logic [31:0] partial_sum_in,
    output logic [15:0] weight_out,
    output logic [15:0] activation_out,
    output logic [31:0] partial_sum_out
);

    logic [31:0] fma_result;

    // Pass through weight and activation (systolic flow)
    always_ff @(posedge clk) begin
        weight_out <= weight_in;
        activation_out <= activation_in;
    end

    // FMA: partial_sum_out = weight * activation + partial_sum_in
    math_bf16_fma u_fma (
        .i_a(weight_in),
        .i_b(activation_in),
        .i_c(partial_sum_in),
        .ow_result(fma_result),
        .ow_overflow(),
        .ow_underflow(),
        .ow_invalid()
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            partial_sum_out <= 32'h0;
        else
            partial_sum_out <= fma_result;
    end

endmodule
```

## Design Considerations

### Advantages

- **Optimal for AI workloads**: BF16 maintains FP32 dynamic range with reduced precision
- **8x smaller than FP32**: Due to 7-bit vs 23-bit mantissa (quadratic scaling)
- **Simple FP32 conversion**: BF16 = FP32[31:16] (truncation)
- **Industry standard**: Compatible with TPU, Tensor Core, AMX conventions
- **High frequency**: Conservative 1.6GHz leaves room for system integration

### Limitations

- **7-bit mantissa precision**: Only ~3 decimal digits (vs ~7 for FP32)
- **Training may need FP32 accumulation**: Gradient updates require higher precision
- **Subnormal handling simplified**: FTZ may lose small gradient information
- **No IEEE exception flags**: Requires software bounds checking

### When to Use BF16

**Appropriate Use Cases:**
- Neural network inference (forward pass)
- Neural network training (with FP32 accumulation)
- Transformer attention computation
- Convolution operations
- Matrix multiplication (GEMM)

**Consider Alternatives When:**
- High precision required (scientific computing) -> FP32/FP64
- Integer quantization acceptable -> INT8/INT4
- Memory is primary constraint -> FP8 (emerging)

## Dependencies

**Existing Modules (rtl/common/):**
- `math_adder_half.sv` - Half adder primitive
- `math_adder_full.sv` - Full adder primitive
- `math_compressor_4to2.sv` - 4:2 compressor
- `math_prefix_cell.sv` - Black prefix cell (G,P -> G,P)
- `math_prefix_cell_gray.sv` - Gray prefix cell (G,P + G -> G)
- `count_leading_zeros.sv` - CLZ for normalization

**Generated Modules:**
- `math_adder_han_carlson_016.sv` - 16-bit prefix adder for multiplier CPA
- `math_adder_han_carlson_048.sv` - 48-bit prefix adder for FMA addition
- `math_multiplier_dadda_4to2_008.sv`
- `math_bf16_mantissa_mult.sv`
- `math_bf16_exponent_adder.sv`
- `math_bf16_multiplier.sv`
- `math_bf16_fma.sv`

## Generation

```bash
# Generate all BF16 modules
cd /path/to/rtldesignsherpa
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common

# Verify synthesis - multiplier
verilator --lint-only --top-module math_bf16_multiplier \
    rtl/common/math_bf16_multiplier.sv \
    rtl/common/math_bf16_mantissa_mult.sv \
    rtl/common/math_bf16_exponent_adder.sv \
    rtl/common/math_multiplier_dadda_4to2_008.sv \
    rtl/common/math_adder_han_carlson_016.sv \
    rtl/common/math_compressor_4to2.sv \
    rtl/common/math_adder_full.sv \
    rtl/common/math_adder_half.sv \
    rtl/common/math_prefix_cell.sv \
    rtl/common/math_prefix_cell_gray.sv

# Verify synthesis - FMA
verilator --lint-only --top-module math_bf16_fma \
    rtl/common/math_bf16_fma.sv \
    rtl/common/math_adder_han_carlson_048.sv \
    rtl/common/math_multiplier_dadda_4to2_008.sv \
    rtl/common/math_adder_han_carlson_016.sv \
    rtl/common/math_compressor_4to2.sv \
    rtl/common/math_adder_full.sv \
    rtl/common/math_adder_half.sv \
    rtl/common/math_prefix_cell.sv \
    rtl/common/math_prefix_cell_gray.sv \
    rtl/common/count_leading_zeros.sv
```

## References

### Academic

- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza 34, 1965.
- Han, T. & Carlson, D. "Fast Area-Efficient VLSI Adders." IEEE ARITH, 1987.
- Prasad, K. & Parhi, K. "Low-power 4-2 and 5-2 compressors." Asilomar, 2001.
- Townsend, W. et al. "A Comparison of Dadda and Wallace Multiplier Delays." IEEE, 2003.

### Industry

- Kalamkar, D. et al. "A Study of BFLOAT16 for Deep Learning Training." arXiv, 2019.
- Burgess, N. et al. "Bfloat16 Processing for Neural Networks." IEEE ARITH, 2019.
- NVIDIA Tensor Core Architecture White Paper
- Google TPU Architecture (ISCA 2017)

### Process Technology

- Sicard, E. & Trojman, L. "Introducing 5-nm FinFET technology in Microwind." 2021.
- Stillmaker, A. & Baas, B. "Scaling equations for CMOS device performance." IEEE, 2017.

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-11-24 | Initial architecture specification |

## Navigation

- **[Back to Repository Root](README.md)**
- **[RTL Common Documentation](docs/markdown/RTLCommon/index.md)**
- **[BF16 Research Notes](bf16-research.md)**
