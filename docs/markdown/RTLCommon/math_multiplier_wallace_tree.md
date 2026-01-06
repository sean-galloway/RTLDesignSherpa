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

Fast parallel multipliers using tree-based partial product reduction with carry-save adders. These modules provide highly optimized unsigned integer multiplication for 8×8, 16×16, and 32×32 operations with O(log N) logic depth.

## Overview

The Wallace tree multiplier family implements high-speed multiplication using a tree of 3:2 compressors (carry-save adders) to reduce partial products in parallel. The reduction tree is built using maximal parallelism - reducing partial products at every opportunity rather than following a scheduled approach.

**Key Features:**
- **O(log N) depth** reduction tree (faster than array multipliers)
- **Maximal parallelism** - reduces whenever 3+ partial products available
- **Structural implementation** - explicit full adder and half adder instantiation
- **Fixed-width variants** - Optimized for 8, 16, and 32-bit operands
- **Purely combinational** - single-cycle multiplication (plus final adder delay)

**Architecture:**
1. **Partial Product Generation** - AND gates create N×N matrix
2. **Wallace Reduction Tree** - Iterative CSA stages reduce to 2 rows
3. **Final Addition** - Output assignment (typically drives external adder)

## Module Declarations

### 8-bit Wallace Tree Multiplier

```systemverilog
module math_multiplier_wallace_tree_008 #(
    parameter int N = 8
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

### 16-bit Wallace Tree Multiplier

```systemverilog
module math_multiplier_wallace_tree_016 #(
    parameter int N = 16
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

### 32-bit Wallace Tree Multiplier

```systemverilog
module math_multiplier_wallace_tree_032 #(
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

### Wallace Tree Algorithm

The Wallace tree multiplier uses an aggressive reduction strategy:

**Stage 1: Partial Product Generation**
```
For N×N multiplication:
- Generate N² partial products: PP[i][j] = multiplier[i] & multiplicand[j]
- Arrange in diagonal columns (like manual multiplication)
```

**Stage 2: Wallace Reduction Tree**
```
While more than 2 rows remain:
    For each column with 3+ partial products:
        - Use Full Adder (3→2 reduction)
    For each column with exactly 2 partial products:
        - Use Half Adder (2→2 compression)
    For each column with 1 partial product:
        - Pass through unchanged
```

**Stage 3: Final Addition**
```
Assign reduced sum and carry vectors to output
(External adder typically needed for final product)
```

**Key Characteristic:** Wallace trees reduce **immediately** whenever 3 or more values are available in a column, creating irregular but highly parallel structure.

### 8-bit Example Structure

```systemverilog
// Partial Products (64 AND gates for 8×8)
wire w_pp_0_0 = i_multiplier[0] & i_multiplicand[0];
wire w_pp_0_1 = i_multiplier[0] & i_multiplicand[1];
// ... 64 total partial products
wire w_pp_7_7 = i_multiplier[7] & i_multiplicand[7];

// Wallace Reduction Stages
// Stage 1: Reduce columns with 3+ partial products
math_adder_full FA_02_4 (
    .i_a(w_pp_0_2),      // Column 2: 3 partial products
    .i_b(w_pp_1_1),
    .i_c(w_pp_2_0),
    .ow_sum(w_sum_02_4),
    .ow_carry(w_carry_02_4)  // Carry goes to next column
);

// Columns with 2 partial products use half adders
math_adder_half HA_01_2 (
    .i_a(w_pp_0_1),
    .i_b(w_pp_1_0),
    .ow_sum(w_sum_01_2),
    .ow_carry(w_carry_01_2)
);

// Stage 2: Reduce intermediate sums and carries
math_adder_full FA_03_6 (
    .i_a(w_pp_0_3),
    .i_b(w_pp_1_2),
    .i_c(w_pp_2_1),
    .ow_sum(w_sum_03_6),
    .ow_carry(w_carry_03_6)
);

// ... many more stages until reduced to 2 rows

// Final assignment (sum and carry vectors)
assign ow_product[0] = w_sum_00;
assign ow_product[1] = w_sum_01;
// ... through ow_product[15]
```

### Reduction Pattern

**For 8×8 multiplication:**
- **Initial:** 64 partial products in 15 columns
- **After Stage 1:** ~43 values in 15 columns
- **After Stage 2:** ~29 values in 15 columns
- **After Stage 3:** ~19 values in 15 columns
- **After Stage 4:** ~13 values in 15 columns
- **After Stage 5:** ~9 values in 15 columns
- **Final:** 2 vectors (sum and carry), requires final 16-bit adder

**Number of stages = ⌈log₁.₅(N)⌉ ≈ 6-7 stages for 8-bit**

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
            product    <= '0;
            valid_pipe <= 1'b0;
            valid_out  <= 1'b0;
        end else begin
            product    <= product_comb;
            valid_pipe <= valid_in;
            valid_out  <= valid_pipe;
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

## Timing Characteristics

| Metric | 8-bit | 16-bit | 32-bit |
|--------|-------|--------|--------|
| **Logic Depth** | ~14-16 levels | ~18-22 levels | ~24-30 levels |
| **Typical Delay (ns)** | ~7-8 | ~9-11 | ~12-15 |
| **Max Frequency** | ~125 MHz | ~90-110 MHz | ~65-80 MHz |

**Logic Depth Breakdown:**
- Partial product generation: 1 level (AND gates)
- Wallace reduction tree: O(log₁.₅ N) levels
- Final addition: Typically uses external fast adder

**Critical Path:**
```
i_multiplier[N-1] → PP generation → Tree stage 1 → Tree stage 2 → ...
→ Tree stage K → Final sum/carry → ow_product[2N-1]
```

**Note:** Actual timing depends heavily on synthesis optimization and target technology.

## Performance Characteristics

### Resource Utilization

| Width | Full Adders | Half Adders | AND Gates | Estimated LUTs |
|-------|-------------|-------------|-----------|----------------|
| 8-bit | ~40 | ~15 | 64 | ~120 |
| 16-bit | ~180 | ~60 | 256 | ~520 |
| 32-bit | ~750 | ~250 | 1024 | ~2100 |

**Comparison to Other Multiplier Architectures:**

| Architecture | Area (relative) | Speed (relative) | Best Use Case |
|--------------|-----------------|------------------|---------------|
| **Wallace Tree** | **1.1×** | **1.0×** | **High-speed, one-time cost** |
| Dadda Tree | 1.0× | 1.05× | Area-optimized, similar speed |
| Array Multiplier | 0.8× | 2.5× | Low-speed, minimal area |
| Booth (radix-4) | 0.9× | 1.5× | Signed, reduced partial products |

**Wallace vs Dadda:**
- Wallace: Reduces immediately (maximal parallelism)
- Dadda: Scheduled reduction (fewer logic stages for same depth)
- **Result:** Dadda typically saves ~10% area with similar or better speed

### Area-Speed Tradeoffs

**For High-Speed Requirements:**
- ✅ Use Wallace tree (fastest critical path)
- ✅ Consider pipelining for even higher frequency
- ✅ Accept larger area overhead

**For Area-Constrained Designs:**
- Use Dadda tree instead (see `math_multiplier_dadda_tree.md`)
- Consider Booth encoding for signed multiplication
- Use sequential multipliers if latency acceptable

## Design Considerations

### Advantages

✅ **Fastest combinational multiplier** - O(log N) depth vs O(N) for array
✅ **Highly parallel** - Exploits 3:2 compression at all levels
✅ **No sequential logic** - Pure combinational (easy to pipeline)
✅ **Unsigned friendly** - Natural fit for unsigned operands
✅ **Scalable** - Algorithm extends to any bit width

### Limitations

⚠️ **Large area** - More gates than Dadda tree (~10% overhead)
⚠️ **Irregular structure** - Complex synthesis, harder to hand-layout
⚠️ **Unsigned only** - Requires additional logic for signed multiplication
⚠️ **Fixed width** - Not parameterizable (must instantiate specific variant)
⚠️ **Long critical path** - May require pipelining for high-frequency designs

### When to Use Wallace Tree

**Appropriate Use Cases:**
- High-speed DSP applications (FIR filters, FFT butterfly)
- Single-cycle multiplication requirements
- FPGA designs with abundant LUT resources
- Unsigned integer multiplication

**Consider Alternatives When:**
- Area is critical → Use Dadda tree (10% smaller)
- Operands are signed → Use Booth multiplier
- Low frequency → Use array multiplier (much smaller)
- Variable width needed → Use parameterized array/Booth

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

## Common Pitfalls

❌ **Anti-Pattern 1: Expecting parameterized width**

```systemverilog
// WRONG: Trying to override N parameter
math_multiplier_wallace_tree_008 #(.N(12)) u_mult (...);  // Won't work!

// RIGHT: Use fixed variant or create custom width
math_multiplier_wallace_tree_016 u_mult (...);  // Use 16-bit variant
```

❌ **Anti-Pattern 2: Using for signed multiplication directly**

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

❌ **Anti-Pattern 3: Forgetting final adder**

```systemverilog
// NOTE: Wallace tree typically outputs sum and carry vectors
// that need final addition. Check specific implementation!

// If module outputs separate sum/carry (some variants):
logic [15:0] sum, carry;
assign product = sum + {carry[14:0], 1'b0};  // Final addition
```

❌ **Anti-Pattern 4: Not pipelining for high frequency**

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

## Internal Building Blocks

The Wallace tree multipliers use these sub-components:

**math_multiplier_wallace_tree_csa_008/016/032.sv:**
- Carry-save adder variants optimized for Wallace tree stages
- Not intended for direct instantiation
- Internal use only within Wallace tree modules

## Related Modules

- **math_multiplier_dadda_tree_*.sv** - Area-optimized alternative (10% smaller)
- **math_adder_carry_save.sv** - 3:2 compressor building block
- **math_adder_full.sv** - Full adder primitive
- **math_adder_half.sv** - Half adder primitive

## Wallace Tree vs Dadda Tree

Both use CSA trees but differ in reduction strategy:

| Aspect | Wallace Tree | Dadda Tree |
|--------|--------------|------------|
| **Strategy** | Reduce immediately | Scheduled reduction |
| **Stages** | More reduction stages | Fewer, larger stages |
| **Area** | ~10% larger | Smaller (optimized) |
| **Speed** | Fastest | Similar or faster |
| **Design** | Simpler (greedy) | More complex (scheduled) |

**Recommendation:** Use Dadda tree for production designs (better area-speed balance).

## References

- Wallace, C.S. "A Suggestion for a Fast Multiplier." IEEE Transactions on Electronic Computers, 1964.
- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza, 1965.
- Oklobdzija, V.G. "High-Speed VLSI Arithmetic Units: Adders and Multipliers." Springer, 2002.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
