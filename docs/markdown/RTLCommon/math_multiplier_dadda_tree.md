# Dadda Tree Multipliers

Area-optimized fast parallel multipliers using scheduled partial product reduction with carry-save adders. These modules provide efficient unsigned integer multiplication for 8×8, 16×16, and 32×32 operations with O(log N) logic depth and ~10% smaller area than Wallace trees.

## Overview

The Dadda tree multiplier family implements high-speed multiplication using an **optimized schedule** of 3:2 compressors (carry-save adders). Unlike Wallace trees which reduce immediately, Dadda trees follow a calculated reduction sequence that minimizes hardware while maintaining similar or better speed.

**Key Features:**
- **O(log N) depth** with optimal scheduling
- **10% smaller area** than equivalent Wallace tree
- **Similar or faster** critical path (fewer logic stages)
- **Structured reduction** - follows mathematical optimization
- **Fixed-width variants** - Optimized for 8, 16, and 32-bit operands
- **Purely combinational** - single-cycle multiplication

**Architecture:**
1. **Partial Product Generation** - AND gates create N×N matrix
2. **Dadda Reduction Schedule** - Optimized CSA stages reduce to 2 rows
3. **Final Addition** - Output assignment (drives external adder if needed)

## Module Declarations

### 8-bit Dadda Tree Multiplier

```systemverilog
module math_multiplier_dadda_tree_008 #(
    parameter int N = 8
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

### 16-bit Dadda Tree Multiplier

```systemverilog
module math_multiplier_dadda_tree_016 #(
    parameter int N = 16
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

### 32-bit Dadda Tree Multiplier

```systemverilog
module math_multiplier_dadda_tree_032 #(
    parameter int N = 32
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 8/16/32 | Bit width (fixed per variant) |

**Note:** The `N` parameter is present but fixed per module variant. It is not intended for user modification.

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_multiplier | Input | N | Multiplier operand (unsigned) |
| i_multiplicand | Input | N | Multiplicand operand (unsigned) |
| ow_product | Output | 2N | Product result (unsigned) |

**Signal Types:**
- **Unsigned only** - All operands and results are unsigned integers
- **Full precision** - Output is full 2N-bit product (no truncation)

## Functionality

### Dadda Reduction Algorithm

The Dadda tree uses an **optimized reduction schedule** rather than immediate reduction:

**Step 1: Calculate Reduction Schedule**
```
Define target heights: d(j) = {2, 3, 4, 6, 9, 13, 19, 28, ...}
Where: d(j+1) = ⌊1.5 × d(j)⌋
```

**Step 2: Partial Product Generation**
```
For N×N multiplication:
- Generate N² partial products: PP[i][j] = multiplier[i] & multiplicand[j]
- Arrange in diagonal columns (like manual multiplication)
```

**Step 3: Scheduled Reduction**
```
For each stage k (from high to low in d-sequence):
    For each column:
        While column height > d(k):
            Use Full Adder (3→2 reduction)
        If column height == d(k) and can compress:
            Use Half Adder (2→2 compression)
        Otherwise:
            Pass through to next stage
```

**Step 4: Final Addition**
```
Assign reduced sum and carry vectors to output
```

**Key Difference from Wallace:** Dadda **waits** to reduce until column height exceeds target, resulting in fewer but larger reduction stages.

### Dadda Sequence Example

**For 8-bit multiplication:**

```
Initial heights (15 columns): [1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1]

Dadda sequence (reverse): 28 → 19 → 13 → 9 → 6 → 4 → 3 → 2

Stage 1: Reduce to height 6
  - Only reduce columns with height > 6
  - Columns 3-11 need reduction

Stage 2: Reduce to height 4
  - Reduce columns with height > 4
  - More columns processed

Stage 3: Reduce to height 3
Stage 4: Reduce to height 2
  - Final stage, all columns reduced to 2 rows
```

### 8-bit Implementation Structure

```systemverilog
// Partial Products (64 AND gates for 8×8)
wire w_pp_0_0 = i_multiplier[0] & i_multiplicand[0];
wire w_pp_0_1 = i_multiplier[0] & i_multiplicand[1];
// ... 64 total partial products
wire w_pp_7_7 = i_multiplier[7] & i_multiplicand[7];

// Dadda Reduction Stage 1 (reduce to height 6)
math_adder_half HA__01_2 (
    .i_a(w_pp_0_1),
    .i_b(w_pp_1_0),
    .ow_sum(w_sum_01_2),
    .ow_carry(w_carry_01_2)
);

math_adder_carry_save CSA_02_4 (
    .i_a(w_pp_0_2),
    .i_b(w_pp_1_1),
    .i_c(w_pp_2_0),
    .ow_sum(w_sum_02_4),
    .ow_carry(w_carry_02_4)
);

// Carry from previous stage feeds next stage
math_adder_half HA__02_2 (
    .i_a(w_carry_01_2),
    .i_b(w_sum_02_4),
    .ow_sum(w_sum_02_2),
    .ow_carry(w_carry_02_2)
);

// Stage 2: Further reduction
math_adder_carry_save CSA_03_6 (
    .i_a(w_pp_0_3),
    .i_b(w_pp_1_2),
    .i_c(w_pp_2_1),
    .ow_sum(w_sum_03_6),
    .ow_carry(w_carry_03_6)
);

// ... many more stages following Dadda schedule

// Final addition stage
wire w_sum_00 = w_pp_0_0;
wire w_sum_01 = w_sum_01_2;
// ... assign final sum and carry vectors

assign ow_product[0]  = w_sum_00;
assign ow_product[1]  = w_sum_01;
// ... through ow_product[15]
```

### Reduction Comparison: Dadda vs Wallace

**For 8×8 multiplication:**

| Stage | Dadda Target Height | Wallace Height | Adders Used |
|-------|---------------------|----------------|-------------|
| Initial | 8 (max column) | 8 | 0 |
| After 1 | 6 | ~5-6 | Dadda: ~18, Wallace: ~21 |
| After 2 | 4 | ~4 | Dadda: ~12, Wallace: ~14 |
| After 3 | 3 | ~3 | Dadda: ~8, Wallace: ~9 |
| After 4 | 2 | 2 | Dadda: ~6, Wallace: ~7 |
| **Total** | **~44 adders** | **~51 adders** | **Dadda 14% fewer** |

**Result:** Dadda uses fewer adders while maintaining same O(log N) depth.

## Usage Examples

### Basic 8×8 Multiplication

```systemverilog
logic [7:0] a, b;
logic [15:0] product;

math_multiplier_dadda_tree_008 u_mult (
    .i_multiplier(a),
    .i_multiplicand(b),
    .ow_product(product)
);

// Example: 12 × 13 = 156
initial begin
    a = 8'd12;
    b = 8'd13;
    #1;  // Allow combinational delay
    assert(product == 16'd156);
end
```

### 16×16 Multiplication with Pipeline

```systemverilog
logic [15:0] a, b;
logic [31:0] product_comb, product_reg;
logic clk, rst_n;

// Dadda tree multiplier (combinational)
math_multiplier_dadda_tree_016 u_mult (
    .i_multiplier(a),
    .i_multiplicand(b),
    .ow_product(product_comb)
);

// Output register for timing closure
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        product_reg <= '0;
    else
        product_reg <= product_comb;
end
```

### Multiply-Accumulate (MAC) Unit

```systemverilog
module mac_unit (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] a, b,
    input  logic        accumulate,  // 1=accumulate, 0=clear
    output logic [31:0] result
);

    logic [31:0] product;
    logic [31:0] accumulator;

    // Dadda tree multiplier
    math_multiplier_dadda_tree_016 u_mult (
        .i_multiplier(a),
        .i_multiplicand(b),
        .ow_product(product)
    );

    // Accumulator
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            accumulator <= '0;
        else if (accumulate)
            accumulator <= accumulator + product;
        else
            accumulator <= product;  // Clear and load
    end

    assign result = accumulator;

endmodule
```

### FIR Filter Tap

```systemverilog
module fir_tap #(
    parameter int DATA_WIDTH = 16,
    parameter int COEFF_WIDTH = 16
) (
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic [DATA_WIDTH-1:0]     data_in,
    input  logic [COEFF_WIDTH-1:0]    coefficient,
    input  logic [31:0]               partial_sum_in,
    output logic [31:0]               partial_sum_out
);

    logic [31:0] product;

    // Multiply coefficient by data
    math_multiplier_dadda_tree_016 u_mult (
        .i_multiplier(coefficient),
        .i_multiplicand(data_in),
        .ow_product(product)
    );

    // Add to partial sum (pipeline stage)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            partial_sum_out <= '0;
        else
            partial_sum_out <= partial_sum_in + product;
    end

endmodule
```

### Parameterized Multiplier Selector

```systemverilog
module flexible_multiplier #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0]   i_multiplier,
    input  logic [WIDTH-1:0]   i_multiplicand,
    output logic [2*WIDTH-1:0] ow_product
);

    generate
        if (WIDTH == 8) begin : gen_8bit
            math_multiplier_dadda_tree_008 u_mult (
                .i_multiplier(i_multiplier),
                .i_multiplicand(i_multiplicand),
                .ow_product(ow_product)
            );
        end else if (WIDTH == 16) begin : gen_16bit
            math_multiplier_dadda_tree_016 u_mult (
                .i_multiplier(i_multiplier),
                .i_multiplicand(i_multiplicand),
                .ow_product(ow_product)
            );
        end else if (WIDTH == 32) begin : gen_32bit
            math_multiplier_dadda_tree_032 u_mult (
                .i_multiplier(i_multiplier),
                .i_multiplicand(i_multiplicand),
                .ow_product(ow_product)
            );
        end else begin : gen_default
            // Fallback: behavioral multiplication
            assign ow_product = i_multiplier * i_multiplicand;
        end
    endgenerate

endmodule
```

## Timing Characteristics

| Metric | 8-bit | 16-bit | 32-bit |
|--------|-------|--------|--------|
| **Logic Depth** | ~13-15 levels | ~17-20 levels | ~22-28 levels |
| **Typical Delay (ns)** | ~6.5-7.5 | ~8.5-10.5 | ~11-14 |
| **Max Frequency** | ~130-150 MHz | ~95-115 MHz | ~70-90 MHz |

**Logic Depth Breakdown:**
- Partial product generation: 1 level (AND gates)
- Dadda reduction stages: O(log₁.₅ N) levels (fewer stages than Wallace)
- Final addition: Typically external adder

**Critical Path:**
```
i_multiplier[N-1] → PP[N-1][N-1] → Stage 1 CSA → Stage 2 CSA → ...
→ Final stage → ow_product[2N-1]
```

**Speed Advantage:** Dadda trees often achieve **5-10% faster** critical path than Wallace despite using fewer gates.

## Performance Characteristics

### Resource Utilization

| Width | Full Adders | Half Adders | AND Gates | Estimated LUTs |
|-------|-------------|-------------|-----------|----------------|
| 8-bit | ~35 | ~13 | 64 | ~108 |
| 16-bit | ~160 | ~52 | 256 | ~468 |
| 32-bit | ~670 | ~220 | 1024 | ~1890 |

**Area Comparison:**

| Architecture | 8-bit LUTs | 16-bit LUTs | 32-bit LUTs | Area Efficiency |
|--------------|------------|-------------|-------------|-----------------|
| Array Multiplier | ~80 | ~320 | ~1280 | Smallest (2× slower) |
| **Dadda Tree** | **~108** | **~468** | **~1890** | **Best balance** |
| Wallace Tree | ~120 | ~520 | ~2100 | 10% larger |
| Booth Radix-4 | ~95 | ~410 | ~1650 | Smaller (signed focus) |

**Key Advantage:** Dadda achieves **10-15% area savings** over Wallace with similar or better speed.

### Multiplier Architecture Selection

| Requirement | Best Choice | Reasoning |
|-------------|-------------|-----------|
| **High-speed unsigned** | **Dadda Tree** | Fastest + smallest CSA tree |
| Signed multiplication | Booth Radix-4 | Fewer partial products |
| Minimal area | Array Multiplier | Sequential, low gates |
| Variable width | Behavioral (`*`) | Synthesis optimizes |
| Very high frequency | Pipelined Dadda | Split into stages |

## Design Considerations

### Advantages

✅ **Smallest fast multiplier** - 10% smaller than Wallace, same speed
✅ **Optimized structure** - Mathematically proven reduction schedule
✅ **Better synthesis** - Fewer stages often synthesize faster
✅ **Pure combinational** - Easy to pipeline where needed
✅ **Scalable** - Algorithm extends to any bit width

### Limitations

⚠️ **Complex design** - Reduction schedule requires calculation
⚠️ **Unsigned only** - Requires sign handling for signed operands
⚠️ **Fixed width** - Not parameterizable (instantiate specific variant)
⚠️ **Irregular structure** - Not as regular as array multipliers

### When to Use Dadda Tree

**Appropriate Use Cases:**
- Production designs requiring fast multiplication
- Area-constrained high-speed applications
- DSP functions (filters, FFT, correlation)
- Unsigned integer arithmetic
- **Default choice** for most multiplication needs

**Consider Alternatives When:**
- Operands are signed → Booth multiplier (fewer PPs)
- Very low area required → Array multiplier
- Variable width needed → Behavioral `*` operator
- Ultra-high frequency → Multi-stage pipelined multiplier

### Dadda vs Wallace Decision

**Choose Dadda When:**
- Production code (better area-speed balance)
- Area matters
- Targeting ASIC (fewer gates = lower cost)

**Choose Wallace When:**
- Educational purposes (simpler to understand)
- Existing design uses it (consistency)
- Specific timing requirements favor it

**In Practice:** Dadda is preferred for almost all production designs.

### Signed Multiplication

Dadda trees output **unsigned products only**. For signed multiplication:

**Option 1: Sign Extension and Correction**
```systemverilog
logic [N-1:0] a, b;
logic [2*N-1:0] product_unsigned, product_signed;
logic sign_bit;

// Compute absolute values
assign a_abs = a[N-1] ? (~a + 1'b1) : a;
assign b_abs = b[N-1] ? (~b + 1'b1) : b;
assign sign_bit = a[N-1] ^ b[N-1];

// Multiply unsigned
math_multiplier_dadda_tree_008 u_mult (
    .i_multiplier(a_abs),
    .i_multiplicand(b_abs),
    .ow_product(product_unsigned)
);

// Apply sign
assign product_signed = sign_bit ? (~product_unsigned + 1'b1) : product_unsigned;
```

**Option 2: Use Booth Multiplier** (More efficient for native signed)

### Pipelining for High Frequency

**2-Stage Pipeline:**
```systemverilog
// Stage 1: Register inputs
always_ff @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

// Stage 2: Multiply and register output
math_multiplier_dadda_tree_016 u_mult (
    .i_multiplier(a_reg),
    .i_multiplicand(b_reg),
    .ow_product(product_comb)
);

always_ff @(posedge clk) begin
    product_reg <= product_comb;
end
```

**4-Stage Pipeline** (for maximum frequency):
Split Dadda tree into pipeline stages based on reduction schedule.

## Common Pitfalls

❌ **Anti-Pattern 1: Expecting width parameterization**

```systemverilog
// WRONG: N parameter is fixed
math_multiplier_dadda_tree_008 #(.N(10)) u_mult (...);  // Won't work!

// RIGHT: Use appropriate fixed variant
math_multiplier_dadda_tree_016 u_mult (...);  // Use 16-bit
```

❌ **Anti-Pattern 2: Using for signed without conversion**

```systemverilog
// WRONG: Signed inputs treated as unsigned
logic signed [7:0] a = -5, b = 3;
logic signed [15:0] product;
math_multiplier_dadda_tree_008 u_mult (
    .i_multiplier(a),      // Treated as 251 (unsigned)!
    .i_multiplicand(b),    // Treated as 3
    .ow_product(product)   // = 753, not -15!
);

// RIGHT: Convert to unsigned, multiply, fix sign
// (See "Signed Multiplication" section)
```

❌ **Anti-Pattern 3: Not considering final adder**

```systemverilog
// NOTE: Check if implementation needs final carry-propagate adder
// Some Dadda trees output final sum directly
// Others output sum + carry that need final addition

// If separate sum/carry:
assign final_product = sum_vector + {carry_vector[2*N-2:0], 1'b0};
```

❌ **Anti-Pattern 4: Ignoring timing at high frequencies**

```systemverilog
// WRONG: 32×32 Dadda at 400 MHz without pipeline
// Critical path ~12-14ns, can't meet 2.5ns period!

// RIGHT: Add pipeline stages
// Target: 1 stage per 5-6ns of delay
```

## Related Modules

- **math_multiplier_wallace_tree_*.sv** - 10% larger, similar speed
- **math_adder_carry_save.sv** - 3:2 compressor building block
- **math_adder_full.sv** - Full adder primitive
- **math_adder_half.sv** - Half adder primitive

## Algorithm Reference: Dadda Sequence

The Dadda reduction sequence is defined as:

```
d(0) = 2           (final stage: 2 rows)
d(1) = 3           (next-to-last stage: 3 rows)
d(j+1) = ⌊1.5 × d(j)⌋  (recursive definition)

Sequence: 2, 3, 4, 6, 9, 13, 19, 28, 42, 63, 94, 141, ...
```

**For N×N multiplication:**
1. Find maximum column height (usually N for middle columns)
2. Start from d(j) ≥ max_height
3. Work backwards through sequence until d(0) = 2

**Example (8×8):**
- Max height = 8
- Start: d(5) = 13 (first ≥ 8)
- Stages: 13 → 9 → 6 → 4 → 3 → 2 (skip 13, start at 9)

## References

- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza 34, 1965.
- Wallace, C.S. "A Suggestion for a Fast Multiplier." IEEE Trans. Electronic Computers, 1964.
- Oklobdzija, V.G. "High-Speed VLSI Arithmetic Units: Adders and Multipliers." Springer, 2002.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
