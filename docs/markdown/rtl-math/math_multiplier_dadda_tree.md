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

# Dadda Tree Multipliers

Area-optimized fast parallel multipliers using scheduled partial product reduction with carry-save adders. These modules provide unsigned integer multiplication for 8×8, 16×16, and 32×32 operations. The reduction tree has logarithmic depth and uses the minimum number of compressors for that depth; the final carry-propagate adder is a Brent-Kung parallel-prefix adder, which is also logarithmic depth, so end-to-end delay is O(log N).

## Overview

The Dadda tree multiplier family implements high-speed multiplication using an **optimized schedule** of 3:2 compressors (carry-save adders). Unlike Wallace trees, which compress everything they can as early as they can, Dadda trees defer compression: each stage only reduces columns down to a precomputed target height. This reaches height 2 in the same number of stages as Wallace while instantiating measurably fewer compressors.

**Key Features:**
- **Logarithmic reduction depth** - 4 stages for 8-bit, 6 for 16-bit, 8 for 32-bit
- **Minimum compressor count** for that depth - 42 cells for 8×8 versus Wallace's 61
- **Structured reduction** - follows the canonical Dadda target-height sequence
- **Fixed-width variants** - generated for 8, 16, and 32-bit operands
- **Purely combinational** - single-cycle multiplication
- **Self-contained** - includes its own final adder; no external adder required

**Architecture:**
1. **Partial Product Generation** - AND gates create the N×N matrix
2. **Dadda Reduction Schedule** - scheduled CSA stages reduce every column to height 2
3. **Final Addition** - an on-chip Brent-Kung parallel-prefix carry-propagate adder sums the two surviving rows into `ow_product`

**Note on the final adder:** these modules are complete multipliers. The reduction tree stops at column height 2, the two remaining rows are packed into the 2N-bit vectors `w_cpa_row0` / `w_cpa_row1`, and those are summed internally by a single `math_adder_brent_kung_{2N}` instance named `u_final_cpa`. Earlier revisions of this module used a ripple carry-propagate adder in that position, and revisions before that collapsed every column to height 1 with no final adder at all; neither is the case now, and no external adder is needed.

The CPA width is the **product** width, not the operand width: the 8-bit multiplier instantiates `math_adder_brent_kung_016`, the 16-bit one `math_adder_brent_kung_032`, and the 32-bit one `math_adder_brent_kung_064`. Carry-in is tied to `1'b0`, and the adder's carry-out is left unread on `w_cpa_carry_unused` - an N x N product is strictly less than 2**(2N), so the top column can never carry out.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 8/16/32 | Bit width (fixed per variant) |

**Note:** The `N` parameter is present but fixed per module variant. It is not intended for user modification.

## Ports

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

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_multiplier | Input | N | Multiplier operand (unsigned) |
| i_multiplicand | Input | N | Multiplicand operand (unsigned) |
| ow_product | Output | 2N | Product result (unsigned) |

**Signal Types:**
- **Unsigned only** - All operands and results are unsigned integers
- **Full precision** - Output is full 2N-bit product (no truncation)

## Functional Description

### Dadda Reduction Algorithm

The Dadda tree uses an **optimized reduction schedule** rather than immediate reduction:

**Step 1: Calculate Reduction Schedule**
```
Define target heights: d(1) = 2, d(j+1) = ⌊1.5 × d(j)⌋
Sequence: 2, 3, 4, 6, 9, 13, 19, 28, 42, ...
```
Pick the smallest sequence entry that is greater than or equal to the tallest
column, then walk the sequence downwards. Each reduction stage takes every
column to at or below the next target height.

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
Every column is now at height 2. Pack the two surviving rows into two
2N-bit vectors and sum them with a Brent-Kung parallel-prefix
carry-propagate adder to produce the 2N-bit product.
```

**Key Difference from Wallace:** Dadda **waits** to reduce until a column exceeds the stage target, so it spends the fewest compressors that still reach height 2 in the same number of stages Wallace needs.

### Dadda Sequence Example

**For 8-bit multiplication:**

```
Initial heights (15 columns): [1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1]

Tallest column is 8, so the first target is the sequence entry above it: 9
is not needed because stage targets are applied downwards from 6.

Stage targets: 6 → 4 → 3 → 2

Stage 1: Reduce to height 6
Stage 2: Reduce to height 4
Stage 3: Reduce to height 3
Stage 4: Reduce to height 2
  - All 15 columns now at height 2; hand off to the final adder
```

The longer sequences apply to the wider variants:

| Variant | Tallest column | Stage targets | Stages |
|---------|----------------|---------------|--------|
| 8-bit | 8 | 6 → 4 → 3 → 2 | 4 |
| 16-bit | 16 | 13 → 9 → 6 → 4 → 3 → 2 | 6 |
| 32-bit | 32 | 28 → 19 → 13 → 9 → 6 → 4 → 3 → 2 | 8 |

### 8-bit Implementation Structure

Generated signals are named `w_sum_{column}_{op}` / `w_carry_{column}_{op}`, and
instances are named `CSA_{column}_{op}` or `HA__{column}_{op}`, where `op` is the
operation index within that column. Excerpts below are taken verbatim from
`rtl/math/math_multiplier_dadda_tree_008.sv`.

```systemverilog
// Partial Products (64 AND gates for 8×8)
wire w_pp_0_0 = i_multiplier[0] & i_multiplicand[0];
wire w_pp_0_1 = i_multiplier[0] & i_multiplicand[1];
// ... 64 total partial products
wire w_pp_7_7 = i_multiplier[7] & i_multiplicand[7];

// Dadda reduction stage 1: max column height 6
// Column 6 has height 7, so exactly one 2:2 compression brings it to 6.
wire w_sum_06_01, w_carry_06_01;
math_adder_half HA__06_01 (
    .i_a(w_pp_0_6),
    .i_b(w_pp_1_5),
    .ow_sum(w_sum_06_01),
    .ow_carry(w_carry_06_01)
);

// Column 7 has height 8 and needs a 3:2 plus a 2:2 to reach 6.
wire w_sum_07_01, w_carry_07_01;
math_adder_carry_save CSA_07_01 (
    .i_a(w_pp_0_7),
    .i_b(w_pp_1_6),
    .i_c(w_pp_2_5),
    .ow_sum(w_sum_07_01),
    .ow_carry(w_carry_07_01)
);
wire w_sum_07_02, w_carry_07_02;
math_adder_half HA__07_02 (
    .i_a(w_pp_3_4),
    .i_b(w_pp_4_3),
    .ow_sum(w_sum_07_02),
    .ow_carry(w_carry_07_02)
);

// ... stages 2 and 3 follow the same pattern with targets 4 and 3

// Dadda reduction stage 4: max column height 2
// Later stages consume sums and carries produced by earlier stages.
wire w_sum_04_03, w_carry_04_03;
math_adder_carry_save CSA_04_03 (
    .i_a(w_sum_04_01),
    .i_b(w_carry_03_01),
    .i_c(w_sum_04_02),
    .ow_sum(w_sum_04_03),
    .ow_carry(w_carry_04_03)
);
```

Once every column is at height 2, the two surviving rows are packed into a pair
of 16-bit vectors and handed to one Brent-Kung prefix adder. There are no
`math_adder_full` or `math_adder_half` instances in this stage at all - every
half and full adder in the file belongs to the reduction tree:

```systemverilog
    // Final addition stage: two reduced rows into a Brent-Kung CPA
    wire [15:0] w_cpa_row0 = {
        1'b0,
        w_pp_7_7,
        // ... one bit per column, taken from the surviving row
        w_pp_2_0,
        w_pp_0_1,
        w_pp_0_0
    };
    wire [15:0] w_cpa_row1 = {
        1'b0,
        w_carry_13_01,
        w_sum_13_01,
        // ... one bit per column, taken from the other surviving row
        w_sum_02_01,
        w_pp_1_0,
        1'b0
    };

    /* verilator lint_off UNUSEDSIGNAL */
    wire w_cpa_carry_unused;
    /* verilator lint_on UNUSEDSIGNAL */
    math_adder_brent_kung_016 #(
        .N(16)
    ) u_final_cpa (
        .i_a(w_cpa_row0),
        .i_b(w_cpa_row1),
        .i_c(1'b0),
        .ow_sum(ow_product),
        .ow_carry(w_cpa_carry_unused)
    );
```

The prefix adder drives `ow_product` directly, so there is no per-bit
`assign ow_product[i]` fan-out stage either.

### Reduction Comparison: Dadda vs Wallace

Both trees reach column height 2 in the **same number of stages**. The
difference is entirely in how many compressors they spend getting there.
The following counts are instance counts from the generated RTL.

**For 8×8 multiplication:**

| | Dadda | Wallace |
|---|-------|---------|
| Reduction stages / layers | 4 | 4 |
| Reduction 3:2 compressors | 35 | 36 |
| Reduction half adders | 7 | 25 |
| **Total reduction cells** | **42** | **61** |
| Final CPA | `math_adder_brent_kung_016` | `math_adder_brent_kung_016` |

The 8×8 figure of 35 full adders and 7 half adders is exactly the textbook
Dadda count.

**Across all widths:**

| Width | Stages | Reduction CSAs | Reduction HAs | Final CPA |
|-------|--------|----------------|---------------|-----------|
| 8-bit | 4 | 35 | 7 | `math_adder_brent_kung_016` |
| 16-bit | 6 | 195 | 15 | `math_adder_brent_kung_032` |
| 32-bit | 8 | 899 | 31 | `math_adder_brent_kung_064` |

**Result:** Dadda reaches height 2 in the same depth as Wallace while spending
19 fewer cells at 8×8.

Wallace used to buy something back for that extra hardware. When both
multipliers ended in a ripple CPA, Wallace's eager compression flattened the
low-order columns to height 1 early, so its ripple spanned only 11 columns
against Dadda's 14 - a shorter serial carry chain that partly offset the larger
tree. **That offset no longer exists.** Both multipliers now feed a full-width
Brent-Kung prefix adder over all 2N columns, and a prefix adder's depth is
logarithmic in its width regardless of how many low-order inputs happen to be
zero. The two designs therefore have an *identical* final adder, in both cell
count and delay.

What remains is the pure statement of the tradeoff: Wallace spends more
compressor cells than Dadda to reach the same reduction depth, and now gets
nothing in return. Dadda is the better choice on both axes.

### Algorithm Reference: Dadda Sequence

The Dadda reduction sequence is defined as:

```
d(1) = 2           (final stage: 2 rows)
d(j+1) = ⌊1.5 × d(j)⌋  (recursive definition)

Sequence: 2, 3, 4, 6, 9, 13, 19, 28, 42, 63, 94, 141, ...
```

**For N×N multiplication:**
1. Find maximum column height (N for the middle column)
2. Find the largest sequence entry strictly below max_height - that is the first
   stage target
3. Work downwards through the sequence until the target is 2

**Example (8×8):**
- Max height = 8
- Largest sequence entry below 8 is 6, so that is the first target
- Stage targets: 6 → 4 → 3 → 2 (four stages)

This matches the generated RTL, whose stage comments read
`Dadda reduction stage 1: max column height 6` through
`stage 4: max column height 2`.

## Timing

| Metric | 8-bit | 16-bit | 32-bit |
|--------|-------|--------|--------|
| **Logic Depth** | ~13-15 levels | ~17-20 levels | ~22-28 levels |
| **Typical Delay (ns)** | ~6.5-7.5 | ~8.5-10.5 | ~11-14 |
| **Max Frequency** | ~130-150 MHz | ~95-115 MHz | ~70-90 MHz |

**Logic Depth Breakdown:**
- Partial product generation: 1 level (AND gates)
- Dadda reduction stages: logarithmic - 4 / 6 / 8 stages for 8 / 16 / 32-bit
- Final addition: on-chip **Brent-Kung** parallel-prefix carry-propagate adder, O(log N) levels

**Critical Path:**
```
a middle-column partial product (the tallest column feeds the most CSA
levels; corner PPs like PP[N-1][N-1] join late and are NOT critical)
→ Stage 1 CSA → ... → Stage K CSA
→ Brent-Kung prefix network (~2·log2(2N) levels) → ow_product[2N-1]
```

**Important:** both halves of the datapath are logarithmic. The reduction tree
is log-depth, and the final adder is a Brent-Kung parallel-prefix adder, which
is also log-depth, so the **end-to-end delay of these modules is O(log N)**.
There is no serial carry chain anywhere in the design. The 32-bit variant, for
example, follows an 8-stage tree with a 64-bit prefix network rather than the
61-deep ripple it used to carry.

### Resource Utilization

Instance counts below are exact, taken from the generated RTL. "3:2 cells"
counts `math_adder_carry_save` and "half adders" counts `math_adder_half`;
every one of them lives in the reduction tree. The final CPA is a single
prefix-adder instance and contributes no discrete adder cells, so
`math_adder_full` does not appear in these files at all.

| Width | 3:2 cells (tree) | Half adders (tree) | Final CPA | AND Gates | Total adder cells |
|-------|------------------|--------------------|-----------|-----------|-------------------|
| 8-bit | 35 | 7 | 1 × `math_adder_brent_kung_016` | 64 | 42 |
| 16-bit | 195 | 15 | 1 × `math_adder_brent_kung_032` | 256 | 210 |
| 32-bit | 899 | 31 | 1 × `math_adder_brent_kung_064` | 1024 | 930 |

**Area Comparison (measured cell counts, Dadda versus Wallace):**

Both families now instantiate the same Brent-Kung CPA at the same width, so the
adder-cell totals below compare reduction trees on equal terms.

| Width | Dadda total cells | Wallace total cells | Dadda saving |
|-------|-------------------|---------------------|--------------|
| 8-bit | 42 | 61 | 31% |
| 16-bit | 210 | 274 | 23% |
| 32-bit | 930 | 1116 | 17% |

Totals count every instantiated discrete adder cell in the corresponding
generated `.sv` file, all of which are in the reduction tree. The shared
Brent-Kung CPA is identical in both families and is excluded from the totals;
adding it back shifts both columns by the same amount. LUT and gate-level area will differ by
technology and synthesis settings; these are structural counts, not synthesis
results.

**Key Advantage:** for the same reduction depth, Dadda instantiates
substantially fewer compressor cells than Wallace.

## Usage Example

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

## Design Notes

### Advantages

- **Smallest fast multiplier** - 17-31% fewer adder cells than Wallace at the same reduction depth, with an identical final adder
- **Optimized structure** - Mathematically proven reduction schedule
- **Fewer cells to synthesize** - same stage count as Wallace, less hardware in each stage
- **Pure combinational** - Easy to pipeline where needed
- **Scalable** - Algorithm extends to any bit width

### Limitations

- **Complex design** - Reduction schedule requires calculation
- **Unsigned only** - Requires sign handling for signed operands
- **Fixed width** - Not parameterizable (instantiate specific variant)
- **Irregular structure** - Not as regular as array multipliers

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

### Multiplier Architecture Selection

| Requirement | Best Choice | Reasoning |
|-------------|-------------|-----------|
| **High-speed unsigned** | **Dadda Tree** | Log-depth tree with the fewest compressors |
| Signed multiplication | Booth Radix-4 | Fewer partial products |
| Minimal area | Array Multiplier | Sequential, low gates |
| Variable width | Behavioral (`*`) | Synthesis optimizes |
| Very high frequency | Pipelined Dadda | Split into stages |

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

### Common Pitfalls

**Anti-Pattern 1: Expecting width parameterization**

```systemverilog
// WRONG: N parameter is fixed
math_multiplier_dadda_tree_008 #(.N(10)) u_mult (...);  // Won't work!

// RIGHT: Use appropriate fixed variant
math_multiplier_dadda_tree_016 u_mult (...);  // Use 16-bit
```

**Anti-Pattern 2: Using for signed without conversion**

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

**Anti-Pattern 3: Adding a redundant external adder**

```systemverilog
// WRONG: ow_product is already the final summed product.
// Bolting on another adder both wastes area and computes garbage.
math_multiplier_dadda_tree_008 u_mult (..., .ow_product(p));
assign final_product = p + {carry_vector[14:0], 1'b0};  // No!

// RIGHT: use ow_product directly.
math_multiplier_dadda_tree_008 u_mult (..., .ow_product(final_product));
```

These modules contain their own final carry-propagate adder. They do not expose
separate sum and carry vectors.

**Anti-Pattern 4: Ignoring timing at high frequencies**

```systemverilog
// WRONG: 32×32 Dadda at 400 MHz without pipeline
// Critical path ~12-14ns, can't meet 2.5ns period!

// RIGHT: Add pipeline stages
// Target: 1 stage per 5-6ns of delay
```

## Related Modules

- **math_multiplier_wallace_tree_*.sv** - same reduction depth, 17-31% more adder cells, identical final CPA
- **math_adder_brent_kung_016/032/064.sv** - logarithmic-depth parallel-prefix adder used as the final CPA here (8/16/32-bit multipliers use the 016/032/064 widths respectively)
- **math_adder_carry_save.sv** - 3:2 compressor building block; the only compressor these files use
- **math_adder_half.sv** - Half adder primitive, used in the reduction tree only

## Testing

From the test suite (`val/math/test_math_multiplier_dadda.py`):

Run levels come from the standard grid: `REG_LEVEL=GATE|FUNC|FULL` selects the
parameter set, `TEST_LEVEL` the per-test depth. Run the whole area with
`make -C val/math run-all-func-parallel`, never bare pytest for suites.

## References

- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza 34, 1965.
- Wallace, C.S. "A Suggestion for a Fast Multiplier." IEEE Trans. Electronic Computers, 1964.
- Oklobdzija, V.G. "High-Speed VLSI Arithmetic Units: Adders and Multipliers." Springer, 2002.

## Navigation

- **[← Back to Math Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
