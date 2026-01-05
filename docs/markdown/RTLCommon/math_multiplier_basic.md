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

# Basic Multiplier Building Blocks

Fundamental multiplication primitives including basic multiplier cells and array-based carry-save multipliers. These modules provide simple multiplication implementations suitable for educational purposes and as building blocks for more complex multiplier architectures.

## Overview

This document covers the basic multiplier components:
- **math_multiplier_basic_cell** - Single-bit multiplier cell with partial product accumulation
- **math_multiplier_carry_save** - Array-based N×N multiplier using carry-save addition

These modules demonstrate fundamental multiplication concepts and serve as reference implementations. For production designs, consider using optimized Wallace or Dadda tree multipliers.

**Key Characteristics:**
- **Structural implementation** - Explicit cell-by-cell construction
- **Educational value** - Clear demonstration of multiplication algorithm
- **Array-based** - Regular structure, easy to understand
- **Scalable** - Generic width support via parameter
- **Combinational** - Pure logic, no sequential elements

## Module Declarations

### Basic Multiplier Cell

```systemverilog
module math_multiplier_basic_cell (
    input  logic i_i,       // Multiplier bit
    input  logic i_j,       // Multiplicand bit
    input  logic i_c,       // Carry input
    input  logic i_p,       // Partial sum input
    output logic ow_c,      // Carry output
    output logic ow_p       // Partial sum output
);
```

### Carry-Save Array Multiplier

```systemverilog
module math_multiplier_carry_save #(
    parameter int N = 4     // Bit width (default: 4)
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
```

## Parameters

### Basic Multiplier Cell

No parameters (single-bit cell).

### Carry-Save Array Multiplier

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Bit width (range: 2-32, typical: 4-16) |

## Ports

### Basic Multiplier Cell Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_i | Input | 1 | Multiplier bit (row index) |
| i_j | Input | 1 | Multiplicand bit (column index) |
| i_c | Input | 1 | Carry input (from cell below) |
| i_p | Input | 1 | Partial sum input (from cell to the left) |
| ow_c | Output | 1 | Carry output (to cell above) |
| ow_p | Output | 1 | Partial sum output (to cell on the right) |

### Carry-Save Array Multiplier Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_multiplier | Input | N | Multiplier operand (unsigned) |
| i_multiplicand | Input | N | Multiplicand operand (unsigned) |
| ow_product | Output | 2N | Product result (unsigned) |

## Functionality

### Basic Multiplier Cell

The basic cell implements a single position in the multiplication array:

**Logic Operations:**
```systemverilog
w_p = i_i & i_j;                                  // Partial product bit
w_sum = i_c ^ i_p ^ w_p;                          // 3-input XOR
w_carry = (i_c & i_p) | (i_c & w_p) | (i_p & w_p); // Majority function

ow_p = w_sum;      // Partial sum output
ow_c = w_carry;    // Carry output
```

**Function:**
- Computes partial product bit: `i_i & i_j`
- Adds to carry input and partial sum input using full adder
- Outputs new partial sum and carry to adjacent cells

**Cell Position in Array:**
```
        i_c (carry from below)
         ↓
    i_p → [CELL] → ow_p (to right)
         ↓
        ow_c (carry to above)

Cell computes: (i_i & i_j) + i_c + i_p
```

### Carry-Save Array Multiplier

The array multiplier creates an N×N grid of basic cells:

**Structure:**
```
Multiplicand:  j₃ j₂ j₁ j₀
Multiplier:
  i₀:         [C][C][C][C]
  i₁:         [C][C][C][C]
  i₂:         [C][C][C][C]
  i₃:         [C][C][C][C]

Where each [C] is a math_multiplier_basic_cell

Connections:
- Horizontal: ow_p[i][j] → i_p[i][j+1]
- Vertical:   ow_c[i][j] → i_c[i+1][j]
- Diagonals collect product bits
```

**Algorithm:**
1. **Generate partial products** - Each cell computes `i_i & i_j`
2. **Accumulate with carry-save** - Each row adds partial products
3. **Collect LSBs** - Left column provides lower product bits
4. **Final addition** - Top row sum and carries added for upper product bits

**Implementation:**
```systemverilog
// Create N×N array of cells
genvar i, j;
generate
    for (i = 0; i < N; i++) begin : gen_row
        for (j = 0; j < N; j++) begin : gen_col
            math_multiplier_basic_cell cell (
                .i_i(i_multiplier[i]),
                .i_j(i_multiplicand[j]),
                .i_c(w_cin[i][j]),
                .i_p(w_pin[i][j]),
                .ow_c(w_cout[i][j]),
                .ow_p(w_pout[i][j])
            );
        end
    end
endgenerate

// Initialize first row
for (j = 0; j < N; j++) begin
    assign w_cin[0][j] = 1'b0;
    assign w_pin[0][j] = 1'b0;
end

// Connect rows (vertical carry propagation)
for (i = 1; i < N; i++) begin
    for (j = 0; j < N; j++) begin
        assign w_cin[i][j] = w_cout[i-1][j];
        assign w_pin[i][j] = (j == N-1) ? 1'b0 : w_pout[i-1][j+1];
    end
end

// Collect LSB of each row (lower product bits)
for (i = 0; i < N; i++) begin
    assign w_product[i] = w_pout[i][0];
end

// Final addition for upper bits
assign final_carries = w_cout[N-1][N-1:0];
assign final_partials = {1'b0, w_pout[N-1][N-1:1]};
assign final_sum = final_carries + final_partials;

assign ow_product = {final_sum, w_product};
```

### Multiplication Example: 5 × 6 (4-bit)

```
Multiplicand (6):  0110
Multiplier (5):    0101

Partial Products:
  i₃ (0): 0000   (0 × 0110)
  i₂ (1): 0110   (1 × 0110)
  i₁ (0): 0000   (0 × 0110)
  i₀ (1): 0110   (1 × 0110)

Array accumulation:
       0110
     0000
   0110
 0000
-----------
 0001 1110   = 30 (decimal)

Product: 5 × 6 = 30 ✓
```

## Usage Examples

### Basic 4×4 Multiplication

```systemverilog
logic [3:0] a, b;
logic [7:0] product;

math_multiplier_carry_save #(.N(4)) u_mult (
    .i_multiplier(a),
    .i_multiplicand(b),
    .ow_product(product)
);

// Example: 7 × 9 = 63
initial begin
    a = 4'd7;
    b = 4'd9;
    #1;
    assert(product == 8'd63);
end
```

### Generic Width Multiplier

```systemverilog
module flexible_multiplier #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0]   a, b,
    output logic [2*WIDTH-1:0] product
);

    math_multiplier_carry_save #(.N(WIDTH)) u_mult (
        .i_multiplier(a),
        .i_multiplicand(b),
        .ow_product(product)
    );

endmodule

// Instantiate with different widths
flexible_multiplier #(.WIDTH(8))  u_mult8  (...);
flexible_multiplier #(.WIDTH(16)) u_mult16 (...);
```

### Building Custom Array from Cells

```systemverilog
// Manual 2×2 multiplier using basic cells
module mult_2x2 (
    input  logic [1:0] i_multiplier,
    input  logic [1:0] i_multiplicand,
    output logic [3:0] ow_product
);

    logic c[1:0][1:0];  // Carry signals
    logic p[1:0][1:0];  // Partial sums

    // Row 0, Column 0
    math_multiplier_basic_cell cell_00 (
        .i_i(i_multiplier[0]),
        .i_j(i_multiplicand[0]),
        .i_c(1'b0),
        .i_p(1'b0),
        .ow_c(c[0][0]),
        .ow_p(p[0][0])
    );
    assign ow_product[0] = p[0][0];

    // Row 0, Column 1
    math_multiplier_basic_cell cell_01 (
        .i_i(i_multiplier[0]),
        .i_j(i_multiplicand[1]),
        .i_c(1'b0),
        .i_p(1'b0),
        .ow_c(c[0][1]),
        .ow_p(p[0][1])
    );

    // Row 1, Column 0
    math_multiplier_basic_cell cell_10 (
        .i_i(i_multiplier[1]),
        .i_j(i_multiplicand[0]),
        .i_c(c[0][0]),
        .i_p(p[0][1]),
        .ow_c(c[1][0]),
        .ow_p(p[1][0])
    );
    assign ow_product[1] = p[1][0];

    // Row 1, Column 1
    math_multiplier_basic_cell cell_11 (
        .i_i(i_multiplier[1]),
        .i_j(i_multiplicand[1]),
        .i_c(c[0][1]),
        .i_p(1'b0),
        .ow_c(c[1][1]),
        .ow_p(p[1][1])
    );

    // Final addition
    assign ow_product[3:2] = c[1][0] + p[1][1] + c[1][1];

endmodule
```

### Multiplier with Valid/Ready Handshake

```systemverilog
module handshake_multiplier #(
    parameter int N = 8
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [N-1:0]     i_multiplier,
    input  logic [N-1:0]     i_multiplicand,
    input  logic             i_valid,
    output logic             o_ready,
    output logic [2*N-1:0]   o_product,
    output logic             o_valid
);

    logic [2*N-1:0] product_comb;

    // Combinational multiplier
    math_multiplier_carry_save #(.N(N)) u_mult (
        .i_multiplier(i_multiplier),
        .i_multiplicand(i_multiplicand),
        .ow_product(product_comb)
    );

    // Pipeline register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            o_product <= '0;
            o_valid   <= 1'b0;
        end else begin
            o_product <= product_comb;
            o_valid   <= i_valid;
        end
    end

    assign o_ready = 1'b1;  // Always ready (combinational)

endmodule
```

## Timing Characteristics

| Metric | 4-bit | 8-bit | 16-bit |
|--------|-------|-------|--------|
| **Logic Depth** | ~8 levels | ~16 levels | ~32 levels |
| **Typical Delay (ns)** | ~3.2 | ~6.4 | ~12.8 |
| **Max Frequency** | ~310 MHz | ~155 MHz | ~78 MHz |

**Logic Depth Breakdown:**
- Each cell: 2 levels (AND + full adder)
- Array depth: 2N levels (carry ripples down rows)
- Final addition: Additional adder delay

**Critical Path:**
```
i_multiplier[N-1] → PP[N-1][0] → row N-1 accumulation → final addition → ow_product[2N-1]
```

**Scaling:** O(N) depth - doubles with doubling of bit width

## Performance Characteristics

### Resource Utilization

| Width | Basic Cells | Final Adder | AND Gates | Estimated LUTs |
|-------|-------------|-------------|-----------|----------------|
| 4-bit | 16 | 4-bit | 16 | ~48 |
| 8-bit | 64 | 8-bit | 64 | ~192 |
| 16-bit | 256 | 16-bit | 256 | ~768 |

**Area Formula:** N² basic cells + N-bit final adder ≈ 3N² LUTs

### Comparison to Optimized Multipliers

| Architecture | 8-bit LUTs | 8-bit Delay | Best Use Case |
|--------------|------------|-------------|---------------|
| Array (Basic Cell) | ~192 | ~6.4 ns | Educational, low speed |
| **Carry-Save Array** | **~192** | **~6.4 ns** | **Simple, moderate speed** |
| Wallace Tree | ~120 | ~3.5 ns | High speed, larger area |
| Dadda Tree | ~108 | ~3.2 ns | **Production (best balance)** |
| Booth Radix-4 | ~100 | ~4.5 ns | Signed multiplication |

**Key Observation:** Array multipliers are ~2× slower but simpler than tree multipliers.

### When to Use Array Multipliers

**Appropriate Use Cases:**
- Educational demonstrations
- Low-frequency designs (<100 MHz for 8-bit)
- Simple prototypes
- Designs where area is more critical than speed
- Parameterized width support needed

**Prefer Optimized Multipliers When:**
- High speed required → Wallace or Dadda tree
- Area critical → Dadda tree (optimized CSA)
- Signed operands → Booth multiplier
- Behavioral sufficient → Use `*` operator (synthesis optimizes)

## Design Considerations

### Advantages

✅ **Simple structure** - Regular array, easy to understand
✅ **Parameterizable** - Generic width support via parameter
✅ **Educational value** - Clearly demonstrates multiplication algorithm
✅ **Moderate area** - Reasonable gate count for small widths
✅ **Purely combinational** - No state, easy to integrate

### Limitations

⚠️ **Slow for large widths** - O(N) depth vs O(log N) for trees
⚠️ **Poor scaling** - Area grows as N², delay as N
⚠️ **Not optimal** - Better alternatives exist (Dadda, Wallace)
⚠️ **Unsigned only** - Requires sign handling for signed operands

### Basic Cell Design Notes

**Verilator Lint Suppression:**
```systemverilog
/* verilator lint_off UNOPTFLAT */
output logic ow_c, ow_p
/* verilator lint_on UNOPTFLAT */
```

**Reason:** Array structure creates combinational feedback paths that are intentional. The explicit output buffering (`always_comb` block) breaks the path for simulation.

### Synthesis Considerations

**For FPGA Designs:**
```tcl
# Let synthesis tool optimize array structure
set_dont_touch false

# Enable register retiming if pipelining
set_optimize_registers true
```

**For ASIC Designs:**
```tcl
# Flatten for better optimization
set_flatten true

# May benefit from custom standard cell multipliers
```

**Note:** Modern synthesis tools often recognize multiplication patterns and replace with optimized implementations.

### Pipelining Strategy

**For higher frequency, add pipeline stages:**

**2-Stage Pipeline:**
```systemverilog
// Stage 1: Register inputs
always_ff @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

// Stage 2: Multiply and register output
math_multiplier_carry_save #(.N(8)) u_mult (
    .i_multiplier(a_reg),
    .i_multiplicand(b_reg),
    .ow_product(product_comb)
);

always_ff @(posedge clk) begin
    product_reg <= product_comb;
end
```

**Multi-Stage Pipeline** (split array into stages):
```systemverilog
// Register after every K rows
// Example: 16-row array split into 4 stages (4 rows each)
```

## Common Pitfalls

❌ **Anti-Pattern 1: Using for high-speed designs**

```systemverilog
// WRONG: Array multiplier too slow for 200 MHz with 16-bit
math_multiplier_carry_save #(.N(16)) u_mult (...);
// Critical path ~13ns, can't meet 5ns period!

// RIGHT: Use Dadda tree for high-speed
math_multiplier_dadda_tree_016 u_mult (...);
```

❌ **Anti-Pattern 2: Not considering behavioral alternative**

```systemverilog
// MANUAL: Explicit array instantiation
math_multiplier_carry_save #(.N(8)) u_mult (
    .i_multiplier(a), .i_multiplicand(b), .ow_product(p)
);

// SIMPLER: Let synthesis optimize
assign p = a * b;  // Synthesis may produce better result!
```

**When to use explicit vs behavioral:**
- Explicit: Educational, specific structure needed, debugging
- Behavioral: Production code, synthesis tool optimization

❌ **Anti-Pattern 3: Expecting signed multiplication**

```systemverilog
// WRONG: Signed operands misinterpreted
logic signed [7:0] a = -5, b = 3;
math_multiplier_carry_save #(.N(8)) u_mult (...);
// Result: 753 (unsigned 251 × 3), not -15!

// RIGHT: Convert to unsigned, fix sign
// (See signed multiplication techniques)
```

❌ **Anti-Pattern 4: Ignoring width limits**

```systemverilog
// CAREFUL: 32×32 array multiplier is very large and slow
math_multiplier_carry_save #(.N(32)) u_mult (...);
// 1024 cells, ~32 levels deep, ~15ns delay

// CONSIDER: Dadda tree or behavioral for large widths
```

## Educational Value

### Understanding Multiplication

The array multiplier clearly demonstrates:

**1. Partial Product Generation:**
```
Each row computes: multiplicand × multiplier_bit[i]
Just like manual multiplication on paper!
```

**2. Shifted Addition:**
```
Each row is shifted left by one position
Carry propagation adds partial products
```

**3. Carry-Save Concept:**
```
Carries propagate downward (next row)
Sums propagate rightward (same row)
Defers final carry-propagate until end
```

### Progression to Optimized Multipliers

**Learning Path:**
1. **Array Multiplier** (this document) - Understand basic concept
2. **Wallace Tree** - Learn parallel reduction
3. **Dadda Tree** - Learn optimization techniques
4. **Booth Encoding** - Learn signed multiplication

**Concept:** Array → parallelize → optimize → specialize

## Related Modules

- **math_multiplier_wallace_tree_*.sv** - Fast tree-based multiplication
- **math_multiplier_dadda_tree_*.sv** - Optimized tree-based multiplication
- **math_adder_carry_save.sv** - 3:2 compressor used in trees
- **math_adder_full.sv** - Full adder primitive
- **math_adder_half.sv** - Half adder primitive

## References

- Parhami, B. "Computer Arithmetic: Algorithms and Hardware Designs." Oxford University Press, 2010.
- Ercegovac, M.D., Lang, T. "Digital Arithmetic." Morgan Kaufmann, 2003.
- Weste, N.H.E., Harris, D. "CMOS VLSI Design: A Circuits and Systems Perspective." Addison-Wesley, 2011.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
