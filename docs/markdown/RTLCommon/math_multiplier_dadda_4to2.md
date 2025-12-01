# Dadda Multiplier with 4:2 Compressors

An area-optimized 8x8 unsigned multiplier using Dadda reduction with 4:2 compressors, providing fast parallel multiplication with ~25% fewer reduction stages than traditional 3:2 CSA-based Dadda trees.

## Overview

The `math_multiplier_dadda_4to2_008` module implements an 8-bit unsigned multiplier optimized for BF16 mantissa multiplication. It uses 4:2 compressors instead of 3:2 carry-save adders (CSAs), enabling faster column height reduction with fewer stages.

**Key Features:**
- **8x8 unsigned multiply** - 16-bit product output
- **4:2 compressor-based** - Faster height reduction than 3:2 CSA
- **Dadda scheduling** - Optimal reduction order for minimum area
- **Han-Carlson final CPA** - Fast carry-propagate addition
- **Purely combinational** - Single-cycle operation

## Module Declaration

```systemverilog
module math_multiplier_dadda_4to2_008 #(
    parameter int N = 8
) (
    input  logic [N-1:0]   i_multiplier,
    input  logic [N-1:0]   i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 8 | Operand width (fixed at 8 for this variant) |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_multiplier | Input | 8 | Multiplier operand (unsigned) |
| i_multiplicand | Input | 8 | Multiplicand operand (unsigned) |
| ow_product | Output | 16 | Full-precision product (unsigned) |

## Architecture

### Three-Stage Pipeline

1. **Partial Product Generation** - 64 AND gates create 8x8 bit matrix
2. **Dadda Reduction** - 4:2 compressors reduce columns to 2 rows
3. **Final CPA** - Han-Carlson adder produces final product

### Partial Product Matrix

For 8x8 multiplication, partial products form a diamond pattern:

```
Column:    0  1  2  3  4  5  6  7  8  9 10 11 12 13 14
Height:    1  2  3  4  5  6  7  8  7  6  5  4  3  2  1

           pp00
        pp01 pp10
     pp02 pp11 pp20
  pp03 pp12 pp21 pp30
pp04 pp13 pp22 pp31 pp40
  ...           ...
                 pp77

Maximum column height = 8 (columns 7)
```

### Dadda Reduction with 4:2 Compressors

**4:2 Compressor Advantage:**
- Reduces 5 inputs to 3 outputs (vs 3:2 for standard CSA)
- Effectively removes 2 bits from column height per compressor
- Cout independent of Cin enables parallel carry chains

**Dadda Height Sequence:**
```
d(j) = {2, 3, 4, 6, 9, 13, 19, 28, ...}
Rule: d(j+1) = floor(1.5 * d(j))
```

**Reduction Stages for 8-bit (max height = 8):**
```
Start:  height 8
Stage 1: reduce to 6 (columns > 6 get 4:2 compressors)
Stage 2: reduce to 4
Stage 3: reduce to 3
Stage 4: reduce to 2 (final for CPA)
```

### Reduction Example (Column 7)

```
Initial height: 8 bits
  pp07, pp16, pp25, pp34, pp43, pp52, pp61, pp70

Stage 1: Reduce 8 -> 6
  4:2 compressor: (pp07, pp16, pp25, pp34, cin) -> sum1, carry1, cout1
  Remaining: sum1, pp43, pp52, pp61, pp70 + carry1, cout1 from col 6
  Height after: 6 (might be more with carries from col 6)

Stage 2: Reduce to 4
  Continue with 4:2 and 3:2 compressors as needed

...

Final: 2 rows for CPA input
```

### Component Instantiation

```systemverilog
// Partial products (64 AND gates)
wire w_pp_0_0 = i_multiplier[0] & i_multiplicand[0];
wire w_pp_0_1 = i_multiplier[0] & i_multiplicand[1];
// ... 64 total

// 4:2 Compressors for reduction
math_compressor_4to2 u_c4to2_07_000 (
    .i_x1(w_pp_0_7), .i_x2(w_pp_1_6),
    .i_x3(w_pp_2_5), .i_x4(w_pp_3_4),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_000),
    .ow_carry(w_c4to2_carry_07_000),
    .ow_cout(w_c4to2_cout_07_000)
);

// Half adders for 2-input reduction
math_adder_half u_ha_01_000 (
    .i_a(w_pp_0_1), .i_b(w_pp_1_0),
    .ow_sum(w_ha_sum_01_000),
    .ow_carry(w_ha_carry_01_000)
);

// Full adders for 3-input reduction
math_adder_full u_fa_02_000 (
    .i_a(w_pp_0_2), .i_b(w_pp_1_1), .i_c(w_pp_2_0),
    .ow_sum(w_fa_sum_02_000),
    .ow_carry(w_fa_carry_02_000)
);

// Final CPA
math_adder_han_carlson_016 u_final_cpa (
    .i_a(w_cpa_a),
    .i_b(w_cpa_b),
    .i_cin(1'b0),
    .ow_sum(ow_product),
    .ow_cout(w_cpa_cout)
);
```

## Timing Characteristics

| Metric | Value |
|--------|-------|
| Partial Product Gen | 1 gate level (AND) |
| Dadda Reduction | ~4 stages of 4:2 compressors |
| Final CPA | 5-6 levels (Han-Carlson 16-bit) |
| **Total Depth** | ~13-15 gate levels |

### Critical Path

```
i_multiplier[7] -> pp_7_7 -> Stage 1 4:2 -> Stage 2 4:2 ->
Stage 3 4:2 -> Stage 4 HA/FA -> CPA -> ow_product[15]
```

## Usage Examples

### Basic 8x8 Multiplication

```systemverilog
logic [7:0] a, b;
logic [15:0] product;

math_multiplier_dadda_4to2_008 u_mult (
    .i_multiplier(a),
    .i_multiplicand(b),
    .ow_product(product)
);

// Example: 12 * 13 = 156
initial begin
    a = 8'd12;
    b = 8'd13;
    #1;
    assert(product == 16'd156);
end
```

### In BF16 Mantissa Multiplier

```systemverilog
// BF16 mantissa with implied leading 1
wire [7:0] w_mant_a_ext = {i_a_is_normal, i_mant_a};  // 1.mantissa
wire [7:0] w_mant_b_ext = {i_b_is_normal, i_mant_b};  // 1.mantissa

wire [15:0] w_product;

math_multiplier_dadda_4to2_008 u_mant_mult (
    .i_multiplier(w_mant_a_ext),
    .i_multiplicand(w_mant_b_ext),
    .ow_product(w_product)
);

// Product is in format: 1x.xxxxxx_xxxxxxxx or 01.xxxxxx_xxxxxxxx
wire w_needs_norm = w_product[15];  // If MSB set, product >= 2.0
```

### With Pipeline Register

```systemverilog
logic [7:0] a_reg, b_reg;
logic [15:0] product_comb, product_reg;

// Input register
always_ff @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

// Multiplier (combinational)
math_multiplier_dadda_4to2_008 u_mult (
    .i_multiplier(a_reg),
    .i_multiplicand(b_reg),
    .ow_product(product_comb)
);

// Output register
always_ff @(posedge clk) begin
    product_reg <= product_comb;
end
```

## Performance Characteristics

### Resource Utilization

| Component | Count |
|-----------|-------|
| AND gates (partial products) | 64 |
| 4:2 Compressors | ~12-15 |
| Full Adders (3:2) | ~8-12 |
| Half Adders | ~4-6 |
| Han-Carlson 16-bit CPA | 1 |
| **Total LUTs (est.)** | ~120-140 |

### Comparison: 4:2 vs 3:2 Dadda

| Metric | 3:2 CSA Dadda | 4:2 Compressor Dadda |
|--------|---------------|----------------------|
| Reduction stages | 4-5 | 3-4 |
| Total adders/compressors | ~50 | ~35 |
| Logic depth | ~17-20 | ~13-15 |
| Area (LUTs) | ~130 | ~130 |

**Advantage:** 4:2 compressors reduce stage count by ~25% with similar area.

### Design Optimization Priorities

This module is optimized with the following priorities:
1. **Area** - Dadda scheduling minimizes total compressor count
2. **Wire complexity** - Regular structure from systematic reduction
3. **Logic depth** - 4:2 compressors reduce critical path stages

## Design Considerations

### Advantages

- **Fast** - O(log N) depth for reduction + CPA
- **Area-efficient** - Dadda scheduling minimizes hardware
- **Regular structure** - Easy to synthesize and optimize
- **Full precision** - No truncation of result

### Limitations

- **Unsigned only** - Requires sign handling for signed operands
- **Fixed width** - N=8 is hardcoded in this variant
- **Combinational** - May need pipelining for high frequency

### Signed Multiplication

For signed multiplication, use absolute values and fix sign:

```systemverilog
// Convert to unsigned
wire [7:0] a_abs = a[7] ? (~a + 1'b1) : a;
wire [7:0] b_abs = b[7] ? (~b + 1'b1) : b;
wire       sign_result = a[7] ^ b[7];

// Multiply unsigned
math_multiplier_dadda_4to2_008 u_mult (
    .i_multiplier(a_abs),
    .i_multiplicand(b_abs),
    .ow_product(product_unsigned)
);

// Fix sign
wire [15:0] product_signed = sign_result ? (~product_unsigned + 1'b1)
                                         : product_unsigned;
```

## Auto-Generated Code

This module is auto-generated by Python scripts:
- **Generator:** `bin/rtl_generators/bf16/dadda_4to2_multiplier.py`
- **Regenerate:** `PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common`

**Do not edit the generated .sv file manually.** Modify the generator script instead.

## Related Modules

- **math_compressor_4to2** - 4:2 compressor building block
- **math_adder_full** - Full adder (3:2 compressor)
- **math_adder_half** - Half adder
- **math_adder_han_carlson_016** - Final CPA
- **math_bf16_mantissa_mult** - BF16 wrapper using this multiplier
- **math_multiplier_dadda_tree_008** - Alternative 3:2 CSA version

## References

- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza 34, 1965.
- Weinberger, A. "4:2 Carry-Save Adder Module." IBM Technical Disclosure Bulletin, 1981.
- Oklobdzija, V.G. "A Method for Speed Optimized Partial Product Reduction." IEEE Trans. Computers, 1996.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
