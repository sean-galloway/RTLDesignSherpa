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

# Wallace Tree Multipliers

## Overview

Fast parallel multipliers built on tree-based partial product reduction with carry-save adders. The family covers unsigned integer multiplication for 8×8, 16×16, and 32×32 operations, and the recipe is the same at every width: AND gates build the N×N partial-product matrix, a tree of 3:2 compressors (carry-save adders) works through it in parallel, and a Brent-Kung parallel-prefix adder sums the two surviving rows. The reduction is built with maximal parallelism—everything that can compress in a given layer does compress, rather than following a schedule. The tree is logarithmic in depth, the final adder is log depth too, so end-to-end delay is O(log N).

**Key Features:**
- **Logarithmic reduction depth** - 4 layers for 8-bit, 6 for 16-bit, 8 for 32-bit
- **Maximal parallelism** - every group of 3 in a column compresses in the same layer
- **Structural implementation** - explicit full adder and half adder instantiation
- **Fixed-width variants** - generated for 8, 16, and 32-bit operands
- **Purely combinational** - single-cycle multiplication
- **Self-contained** - includes its own final adder; no external adder required

**Architecture:**
1. **Partial Product Generation** - AND gates create the N×N matrix
2. **Wallace Reduction Layers** - parallel CSA layers reduce every column to height 2
3. **Final Addition** - an on-chip Brent-Kung parallel-prefix carry-propagate adder sums the two surviving rows into `ow_product`

**A note on the final adder, because this trips people up:** these modules are complete multipliers. The reduction tree stops at column height 2, the two remaining rows are packed into the 2N-bit vectors `w_cpa_row0` / `w_cpa_row1`, and a single `math_adder_brent_kung_{2N}` instance named `u_final_cpa` sums them internally. Earlier revisions of this module used a ripple carry-propagate adder in that position, and revisions before that collapsed every column to height 1 with no final adder at all. Neither is the case now, and no external adder is needed.

The CPA width is the **product** width, not the operand width: the 8-bit multiplier instantiates `math_adder_brent_kung_016`, the 16-bit one `math_adder_brent_kung_032`, and the 32-bit one `math_adder_brent_kung_064`. Carry-in is tied to `1'b0`, and the adder's carry-out goes unread on `w_cpa_carry_unused`—an N x N product is strictly less than 2**(2N), so the top column can never carry out.

**Two variants are generated.** `math_multiplier_wallace_tree_NNN` builds its reduction tree from `math_adder_full`; `math_multiplier_wallace_tree_csa_NNN` builds it from `math_adder_carry_save`. Both cells are 3:2 compressors, so the two trees come out structurally identical—same instance counts, same topology. The final CPA is the same `math_adder_brent_kung_{2N}` instance in **both** variants. Both are standalone top-level multipliers with the same port list. Pick either.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 8/16/32 | Bit width (fixed per variant) |

**Note:** `N` is present but fixed per module variant. It's not intended for user modification.

## Ports

### Module Declarations

#### 8-bit Wallace Tree Multiplier

```systemverilog
module math_multiplier_wallace_tree_008 #(
    parameter int N = 8
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

#### 16-bit Wallace Tree Multiplier

```systemverilog
module math_multiplier_wallace_tree_016 #(
    parameter int N = 16
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

#### 32-bit Wallace Tree Multiplier

```systemverilog
module math_multiplier_wallace_tree_032 #(
    parameter int N = 32
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

### Port List

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_multiplier | Input | N | Multiplier operand (unsigned) |
| i_multiplicand | Input | N | Multiplicand operand (unsigned) |
| ow_product | Output | 2N | Product result (unsigned) |

**Signal Types:**
- **Unsigned only** - All operands and results are unsigned integers
- **Full precision** - Output is full 2N-bit product (no truncation)

## Functional Description

### Wallace Tree Algorithm

The Wallace tree plays an aggressive reduction game:

**Stage 1: Partial Product Generation**
```
For N×N multiplication:
- Generate N² partial products: PP[i][j] = multiplier[i] & multiplicand[j]
- Arrange in diagonal columns (like manual multiplication)
```

**Stage 2: Wallace Reduction Layers**

Reduction proceeds in **layers**. Within a single layer, every column is
partitioned into groups of 3, and all groups across all columns compress
**simultaneously**. Layers repeat until every column is at height 2.

```
While any column has height > 2:            // one iteration = one layer
    For each column, partition its bits into groups of 3:
        - group of 3 bits -> 3:2 compressor (sum stays, carry goes left)
        - group of 2 bits -> half adder     (sum stays, carry goes left)
        - group of 1 bit  -> passes through to the next layer untouched
```

Because the partitioning is done per layer rather than per opportunity, a
column of height 8 becomes ceil(8/3) = 3 sums plus carries arriving from the
column to its right, and so on down the layers.

**Stage 3: Final Addition**
```
Every column is now at height 2. Pack the two surviving rows into two
2N-bit vectors and sum them with a Brent-Kung parallel-prefix
carry-propagate adder to produce the 2N-bit product.
```

**Key characteristic:** Wallace compresses **everything it can as early as it
can**. That's the entire distinction from Dadda, which defers compression
using per-stage target heights. Both reach height 2 in the same number of
layers; Wallace simply spends more compressors getting there.

### 8-bit Example Structure

Generated signals are named `w_sum_{column}_{layer}_{op}` /
`w_carry_{column}_{layer}_{op}`, and instances are named
`FA_{column}_{layer}_{op}` (or `CSA_...` in the `_csa_` variant) and
`HA_{column}_{layer}_{op}`. The excerpts below are taken verbatim from
`rtl/math/math_multiplier_wallace_tree_008.sv`.

```systemverilog
// Partial Products (64 AND gates for 8×8)
wire w_pp_0_0 = i_multiplier[0] & i_multiplicand[0];
wire w_pp_0_1 = i_multiplier[0] & i_multiplicand[1];
// ... 64 total partial products
wire w_pp_7_7 = i_multiplier[7] & i_multiplicand[7];

// Wallace reduction layer 1
// Column 1 holds only 2 bits, so it gets a half adder.
wire w_sum_01_1_01, w_carry_01_1_01;
math_adder_half HA_01_1_01 (
    .i_a(w_pp_0_1),
    .i_b(w_pp_1_0),
    .ow_sum(w_sum_01_1_01),
    .ow_carry(w_carry_01_1_01)
);

// Column 2 holds 3 bits: one full group, one 3:2 compressor.
wire w_sum_02_1_01, w_carry_02_1_01;
math_adder_full FA_02_1_01 (
    .i_a(w_pp_0_2),
    .i_b(w_pp_1_1),
    .i_c(w_pp_2_0),
    .ow_sum(w_sum_02_1_01),
    .ow_carry(w_carry_02_1_01)
);

// Column 3 likewise; every one of these fires in the same layer.
wire w_sum_03_1_01, w_carry_03_1_01;
math_adder_full FA_03_1_01 (
    .i_a(w_pp_0_3),
    .i_b(w_pp_1_2),
    .i_c(w_pp_2_1),
    .ow_sum(w_sum_03_1_01),
    .ow_carry(w_carry_03_1_01)
);

// ... layers 2, 3, 4 repeat the same grouping on the surviving rows
```

In the `_csa_` variant the identical structure is emitted with
`math_adder_carry_save` standing in for `math_adder_full`:

```systemverilog
// math_multiplier_wallace_tree_csa_008.sv, same position in layer 1
wire w_sum_02_1_01, w_carry_02_1_01;
math_adder_carry_save CSA_02_1_01 (
    .i_a(w_pp_0_2),
    .i_b(w_pp_1_1),
    .i_c(w_pp_2_0),
    .ow_sum(w_sum_02_1_01),
    .ow_carry(w_carry_02_1_01)
);
```

Once every column is at height 2, the two surviving rows are packed into a pair
of 16-bit vectors and handed to one Brent-Kung prefix adder. There are no
`math_adder_full` or `math_adder_half` instances in this stage at all—every
half and full adder in the file belongs to the reduction tree:

```systemverilog
    // Final addition stage: two reduced rows into a Brent-Kung CPA
    wire [15:0] w_cpa_row0 = {
        w_carry_14_4_01,
        w_carry_13_4_01,
        // ... one bit per column, taken from the surviving row
        w_sum_02_2_01,
        w_sum_01_1_01,
        w_pp_0_0
    };
    wire [15:0] w_cpa_row1 = {
        w_sum_15_4_01,
        w_sum_14_4_01,
        // ... one bit per column, taken from the other surviving row
        w_sum_05_4_01,
        1'b0,
        1'b0,
        1'b0,
        1'b0,
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

Wallace's eager compression has already flattened columns 0-4 to height 1, and
that shows up as the five `1'b0` entries at the bottom of `w_cpa_row1`. It no
longer buys any delay, though: the prefix adder still spans all 16 columns,
and its depth is logarithmic in that width whether or not the low-order
inputs are constant zero. The prefix adder drives `ow_product` directly, so
there's no per-bit `assign ow_product[i]` fan-out stage either.

### Reduction Pattern

Layer counts and instance counts, measured from the generated RTL:

| Width | Layers | Reduction 3:2 compressors | Reduction half adders | Final CPA |
|-------|--------|---------------------------|-----------------------|-----------|
| 8-bit | 4 | 36 | 25 | `math_adder_brent_kung_016` |
| 16-bit | 6 | 196 | 78 | `math_adder_brent_kung_032` |
| 32-bit | 8 | 900 | 216 | `math_adder_brent_kung_064` |

**For 8×8 multiplication:** 64 partial products across 15 columns reduce to 2
rows in 4 layers, then a single 16-bit Brent-Kung prefix CPA sums them.

**Number of layers:** measured, this is **4 layers for 8-bit, 6 for 16-bit, and
8 for 32-bit**—count the `// Wallace reduction layer N` comments in the
generated RTL if you want to check.

Don't trust a closed form here. The often-quoted `log₁.₅(N)` is wrong: it
describes reduction from N rows down to 1, and this tree stops at 2.
Correcting it to `log₁.₅(N/2)` fixes 8-bit and 16-bit but still under-predicts
32-bit—it gives 7 where the generator emits 8:

| N | `log₁.₅(N)` | `log₁.₅(N/2)` | measured |
|---|---------------|-----------------|----------|
| 8 | 6 | 4 | **4** |
| 16 | 7 | 6 | **6** |
| 32 | 9 | 7 | **8** |

: Layer-count formulas against the generated RTL

Both formulas assume every column shrinks by a clean 3:2 every layer. It
doesn't. A column whose height isn't a multiple of 3 leaves a remainder that
passes through untouched, and carries arriving from the column below can raise
a column between layers. Those two effects cost an extra layer by the time N
reaches 32. Take the layer count from the RTL, not from a formula.

### The `_csa_` Variant

**math_multiplier_wallace_tree_csa_008/016/032.sv** are **standalone top-level
multipliers**, not internal sub-components. Each declares the same module
interface as the plain variant:

```systemverilog
module math_multiplier_wallace_tree_csa_008 #(
    parameter int N = 8
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

The only difference is which cell builds the reduction tree:

| | Plain variant | `_csa_` variant |
|---|---------------|-----------------|
| Reduction tree cell | `math_adder_full` | `math_adder_carry_save` |
| Final CPA cell | `math_adder_brent_kung_{16,32,64}` | `math_adder_brent_kung_{16,32,64}` |
| Tree topology | identical | identical |
| Instance counts | identical | identical |

Both cells are 3:2 compressors, so the trees are structurally identical. The
plain variant is **not** built out of the `_csa_` variant—they're two
independent generated modules, and neither instantiates the other. Instantiate
whichever one you prefer.

## Timing Characteristics
| Metric | 8-bit | 16-bit | 32-bit |
|--------|-------|--------|--------|
| **Logic Depth** | ~14-16 levels | ~18-22 levels | ~24-30 levels |
| **Typical Delay (ns)** | ~7-8 | ~9-11 | ~12-15 |
| **Max Frequency** | ~125 MHz | ~90-110 MHz | ~65-80 MHz |

**Logic Depth Breakdown:**
- Partial product generation: 1 level (AND gates)
- Wallace reduction layers: logarithmic - 4 / 6 / 8 layers for 8 / 16 / 32-bit
- Final addition: on-chip **Brent-Kung** parallel-prefix carry-propagate adder, O(log N) levels

**Critical Path:**
```
i_multiplier[N-1] → PP generation → Layer 1 → Layer 2 → ... → Layer K
→ Brent-Kung prefix network (~2·log2(2N) levels) → ow_product[2N-1]
```

One thing worth stating plainly: both halves of the datapath are logarithmic.
The reduction tree is log-depth, and the final adder is a Brent-Kung
parallel-prefix adder, which is also log-depth, so the **end-to-end delay of
these modules is O(log N)**. There is no serial carry chain anywhere in the
design. The 32-bit variant, for example, follows an 8-layer tree with a
64-bit prefix network rather than the 54-deep ripple it used to carry.

**Note:** Actual timing depends heavily on synthesis optimization and target technology.

## Usage Examples

### Basic 8×8 Multiplication

```systemverilog
logic [7:0] a, b;
logic [15:0] product;

math_multiplier_wallace_tree_008 u_mult (
    .i_multiplier(a),
    .i_multiplicand(b),
    .ow_product(product)
);

// Example: 15 × 17 = 255
initial begin
    a = 8'd15;
    b = 8'd17;
    #1;  // Allow combinational delay
    assert(product == 16'd255);
end
```

### 16×16 Multiplication with Pipeline Register

```systemverilog
logic [15:0] a, b;
logic [31:0] product_comb, product_reg;
logic clk, rst_n;

// Wallace tree multiplier (combinational)
math_multiplier_wallace_tree_016 u_mult (
    .i_multiplier(a),
    .i_multiplicand(b),
    .ow_product(product_comb)
);

// Optional output register for pipelining
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        product_reg <= '0;
    else
        product_reg <= product_comb;
end
```

### 32×32 Multiplication for DSP

```systemverilog
module dsp_multiply (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [31:0] coeff,      // Filter coefficient
    input  logic [31:0] sample,     // Input sample
    input  logic        valid_in,
    output logic [63:0] product,
    output logic        valid_out
);

    logic [63:0] product_comb;
    logic [63:0] product_pipe;
    logic        valid_pipe;

    // Wallace tree multiplier
    math_multiplier_wallace_tree_032 u_mult (
        .i_multiplier(coeff),
        .i_multiplicand(sample),
        .ow_product(product_comb)
    );

    // Pipeline register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            product_pipe <= '0;
            product      <= '0;
            valid_pipe   <= 1'b0;
            valid_out    <= 1'b0;
        end else begin
            product_pipe <= product_comb;
            product      <= product_pipe;  // 2 stages, like the valid chain --
                                           // a 1-stage product with a 2-stage
                                           // valid shows the NEXT input's result
            valid_pipe   <= valid_in;
            valid_out    <= valid_pipe;
        end
    end

endmodule
```

### Multi-Stage Pipelined Multiplier

```systemverilog
// Split Wallace tree into pipeline stages for higher frequency
module pipelined_multiplier (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] a, b,
    output logic [31:0] product
);

    // Stage 1: Partial product generation
    logic [15:0][15:0] pp_stage1;
    genvar i, j;
    generate
        for (i = 0; i < 16; i++) begin : gen_pp
            for (j = 0; j < 16; j++) begin
                always_ff @(posedge clk)
                    pp_stage1[i][j] <= a[i] & b[j];
            end
        end
    endgenerate

    // Stage 2-3: Wallace reduction (using tree, registered)
    // ... intermediate pipeline stages

    // Final stage: Assign product
    // ... final adder and output register

endmodule
```

## Design Notes

### Advantages

- **Log-depth end to end** - the tree collapses N rows to 2 in O(log N) layers, versus O(N) for an array multiplier, and the Brent-Kung prefix CPA that follows is O(log N) as well
- **Highly parallel** - Exploits 3:2 compression at all levels
- **No sequential logic** - Pure combinational (easy to pipeline)
- **Unsigned friendly** - Natural fit for unsigned operands
- **Scalable** - Algorithm extends to any bit width

### Limitations

- **Large area** - More adder cells than Dadda tree at the same depth (61 versus 42 at 8×8, 1116 versus 930 at 32×32), with no offsetting delay advantage
- **Irregular structure** - Complex synthesis, harder to hand-layout
- **Unsigned only** - Requires additional logic for signed multiplication
- **Fixed width** - Not parameterizable (must instantiate specific variant)
- **Long critical path** - May require pipelining for high-frequency designs

### When to Use Wallace Tree

**Appropriate Use Cases:**
- High-speed DSP applications (FIR filters, FFT butterfly)
- Single-cycle multiplication requirements
- FPGA designs with abundant LUT resources
- Unsigned integer multiplication

**Consider Alternatives When:**
- Area is critical → Use Dadda tree (17-31% fewer adder cells at the same depth)
- Operands are signed → Use Booth multiplier
- Low frequency → Use array multiplier (much smaller)
- Variable width needed → Use parameterized array/Booth

### Resource Utilization

Instance counts below are exact, taken from the generated RTL. "3:2 cells"
counts the reduction-tree compressors (`math_adder_full` in the plain variant,
`math_adder_carry_save` in the `_csa_` variant). Every discrete adder cell in
these files lives in the reduction tree; the final CPA is a single prefix-adder
instance and contributes none.

| Width | 3:2 cells (tree) | Half adders (tree) | Final CPA | AND Gates | Total adder cells |
|-------|------------------|--------------------|-----------|-----------|-------------------|
| 8-bit | 36 | 25 | 1 × `math_adder_brent_kung_016` | 64 | 61 |
| 16-bit | 196 | 78 | 1 × `math_adder_brent_kung_032` | 256 | 274 |
| 32-bit | 900 | 216 | 1 × `math_adder_brent_kung_064` | 1024 | 1116 |

### Comparison to Other Multiplier Architectures

| Architecture | Area (relative) | Delay (relative, lower = faster) | Best Use Case |
|--------------|-----------------|------------------|---------------|
| **Wallace Tree** | **1.2×** | **1.0×** | **High-speed, clearest teaching structure** |
| Dadda Tree | 1.0× | ~1.0× | Same depth, fewer compressors |
| Array Multiplier | 0.8× | 2.5× | Low-speed, minimal area |
| Booth (radix-4) | 0.9× | 1.5× | Signed, reduced partial products |

### Wallace Tree vs Dadda Tree

For 8×8, both reach column height 2 in **4 layers/stages—the same depth**.
What differs is what that depth costs:

| | Wallace | Dadda |
|---|---------|-------|
| Layers / stages to height 2 | 4 | 4 |
| Reduction compressors | 36 | 35 |
| Reduction half adders | 25 | 7 |
| **Total reduction cells** | **61** | **42** |
| Final CPA | `math_adder_brent_kung_016` | `math_adder_brent_kung_016` |

Wallace compresses everything it can as early as it can. Dadda defers, using
per-stage target heights to spend the fewest compressors for the same depth.
**That is the entire distinction between the two.**

Wallace used to get something back for its extra 19 cells. When both
multipliers ended in a ripple CPA, eager compression flattened the low-order
columns early, so Wallace's final ripple spanned only 11 columns against
Dadda's 14—a shorter serial carry chain that partly paid for the bigger tree.
**That offset is gone.** Both now feed a full-width Brent-Kung prefix adder
over all 2N columns, and a prefix adder's depth is logarithmic in its width
regardless of how many low-order inputs are constant zero. The final adder is
now *identical* in the two families, in both cell count and delay, so the extra
19 cells buy nothing.

**Measured totals across widths** (adder cells in the reduction tree; the
shared Brent-Kung CPA is identical in both and excluded):

| Width | Wallace total cells | Dadda total cells |
|-------|---------------------|-------------------|
| 8-bit | 61 | 42 |
| 16-bit | 274 | 210 |
| 32-bit | 1116 | 930 |

Both use CSA trees; they differ in reduction strategy:

| Aspect | Wallace Tree | Dadda Tree |
|--------|--------------|------------|
| **Strategy** | Compress everything as early as possible | Defer; compress only down to a per-stage target height |
| **Layers / stages to height 2** | 4 / 6 / 8 (8/16/32-bit) | 4 / 6 / 8 - **the same** |
| **Reduction cells (8×8)** | 61 | 42 |
| **Final CPA (8×8)** | `math_adder_brent_kung_016` | `math_adder_brent_kung_016` - **the same** |
| **Total adder cells (8×8)** | 61 | 42 |
| **Design** | Simpler (greedy grouping) | More complex (scheduled targets) |

Dadda uses **fewer compressors for the same depth**—not fewer stages. The
stage counts are identical.

**Recommendation:** Use Dadda tree for production designs (fewer cells at equal
depth). Wallace remains the clearer teaching example, but with both families
now ending in the same Brent-Kung prefix adder, it no longer has a delay
advantage to trade against its larger tree.

### Area-Speed Tradeoffs

**For High-Speed Requirements:**
- Either tree works—they have the same reduction depth and the same final adder
- Consider pipelining for even higher frequency
- If you pick Wallace, accept the larger area overhead for no speed gain

**For Area-Constrained Designs:**
- Use Dadda tree instead (see `math_multiplier_dadda_tree.md`)
- Consider Booth encoding for signed multiplication
- Use sequential multipliers if latency acceptable

### Signed Multiplication

Wallace trees output **unsigned products only**. For signed multiplication:

**Option 1: Sign-Magnitude Conversion**
```systemverilog
// Convert to unsigned, multiply, then fix sign
logic sign_result;
logic [N-1:0] a_abs, b_abs;
logic [2*N-1:0] product_unsigned;

assign sign_result = a[N-1] ^ b[N-1];
assign a_abs = a[N-1] ? -a : a;
assign b_abs = b[N-1] ? -b : b;

math_multiplier_wallace_tree_008 u_mult (
    .i_multiplier(a_abs),
    .i_multiplicand(b_abs),
    .ow_product(product_unsigned)
);

assign product_signed = sign_result ? -product_unsigned : product_unsigned;
```

**Option 2: Booth Encoding** (More efficient for signed)
```systemverilog
// Use Booth radix-4 multiplier instead
// (Not covered by Wallace tree modules)
```

### Pipelining Strategy

**Single-Stage Pipeline:**
```systemverilog
// Register output (adds 1 cycle latency)
always_ff @(posedge clk) begin
    product_reg <= ow_product;
end
```

**Multi-Stage Pipeline:**
Split Wallace tree into stages:
1. **Stage 1:** Partial product generation → register
2. **Stage 2:** First half of reduction tree → register
3. **Stage 3:** Second half of reduction tree → register
4. **Stage 4:** Final addition → output

**Benefit:** Achieves 2-3× higher frequency at cost of 3-4 cycle latency

### Synthesis Considerations

**Optimization Directives:**
```tcl
# Let synthesis optimize structure
set_dont_touch false

# For timing-critical designs
set_flatten true
set_boundary_optimization true

# If targeting ASIC
set_implementation rtl  # vs gate-level

# If targeting FPGA
# Let tool map to DSP blocks if available
```

**FPGA Notes:**
- Modern FPGAs have dedicated DSP blocks (DSP48 on Xilinx, DSP on Intel)
- Synthesis tools may map Wallace tree to DSP block
- **Check resource utilization** - may use LUTs instead of DSP if tree doesn't fit

### Common Pitfalls

**Anti-Pattern 1: Expecting parameterized width**

```systemverilog
// WRONG: Trying to override N parameter
math_multiplier_wallace_tree_008 #(.N(12)) u_mult (...);  // Won't work!

// RIGHT: Use fixed variant or create custom width
math_multiplier_wallace_tree_016 u_mult (...);  // Use 16-bit variant
```

**Anti-Pattern 2: Using for signed multiplication directly**

```systemverilog
// WRONG: Signed operands won't work correctly
logic signed [7:0] a, b;
logic signed [15:0] product;
math_multiplier_wallace_tree_008 u_mult (
    .i_multiplier(a),        // Interpreted as unsigned!
    .i_multiplicand(b),
    .ow_product(product)
);

// RIGHT: Convert to unsigned, then fix sign
// (See "Signed Multiplication" section above)
```

**Anti-Pattern 3: Adding a redundant external adder**

```systemverilog
// WRONG: ow_product is already the final summed product.
// Bolting on another adder both wastes area and computes garbage.
math_multiplier_wallace_tree_008 u_mult (..., .ow_product(p));
assign product = p + {carry[14:0], 1'b0};  // No!

// RIGHT: use ow_product directly.
math_multiplier_wallace_tree_008 u_mult (..., .ow_product(product));
```

These modules contain their own final carry-propagate adder. They don't expose
separate sum and carry vectors. There's no ambiguity here—every generated
variant definitively has a final CPA inside.

**Anti-Pattern 4: Not pipelining for high frequency**

```systemverilog
// WRONG: Using 32×32 multiplier at 500 MHz (won't meet timing)
math_multiplier_wallace_tree_032 u_mult (...);  // Critical path too long!

// RIGHT: Add pipeline stages
always_ff @(posedge clk) begin
    stage1 <= inputs;
    stage2 <= wallace_tree_partial(stage1);
    stage3 <= wallace_tree_final(stage2);
    product <= stage3;
end
```

## Related Modules

- **math_multiplier_dadda_tree_*.sv** - same reduction depth, 17-31% fewer adder cells, identical final CPA
- **math_adder_brent_kung_016/032/064.sv** - logarithmic-depth parallel-prefix adder used as the final CPA here (8/16/32-bit multipliers use the 016/032/064 widths respectively)
- **math_adder_carry_save.sv** - 3:2 compressor, used in the `_csa_` variant's reduction tree
- **math_adder_full.sv** - Full adder primitive, used in the plain variant's reduction tree
- **math_adder_half.sv** - Half adder primitive, used in the reduction tree of both variants

## Testing

Covered by 2 test suites:

- `val/math/test_math_multiplier_wallace.py`
- `val/math/test_math_multiplier_wallace_csa.py`

Run levels come from the standard grid: `REG_LEVEL=GATE|FUNC|FULL` selects the
parameter set, `TEST_LEVEL` the per-test depth. Run the whole area with
`make -C val/math run-all-func-parallel`, never bare pytest for suites.

## References

- Wallace, C.S. "A Suggestion for a Fast Multiplier." IEEE Transactions on Electronic Computers, 1964.
- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza, 1965.
- Oklobdzija, V.G. "High-Speed VLSI Arithmetic Units: Adders and Multipliers." Springer, 2002.

## Navigation

- **[← Back to Math Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
