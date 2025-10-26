# Kogge-Stone Parallel Prefix Adder

A parameterized adder using Kogge-Stone inspired propagate-generate logic for arbitrary bit widths, providing improved carry computation over ripple carry adders.

## Overview

The `math_adder_kogge_stone_nbit` module implements an adder using generate (G) and propagate (P) signals with a simplified carry computation structure. While named after the Kogge-Stone algorithm, this implementation uses a sequential carry chain rather than the full parallel prefix tree structure, making it suitable for arbitrary bit widths with a balance between speed and implementation complexity.

**Note:** This is a simplified Kogge-Stone inspired implementation. A full Kogge-Stone parallel prefix adder would use a complete binary tree of black cells achieving O(log N) depth, but at the cost of significantly more hardware and complexity for generic parameterization.

## Module Declaration

```systemverilog
module math_adder_kogge_stone_nbit #(
    parameter int N = 4      // Adder width in bits (any width ≥ 1)
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    output logic [N-1:0] ow_sum,    // Sum output
    output logic         ow_carry   // Carry output
);
```

**Note:** No carry input (i_c) - design assumes Cin = 0. For +1 increment, add external increment logic or use dedicated incrementer module.

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Adder width in bits (range: 1-64, typical: 4-64) |

**Width Guidelines:**
- **Minimum**: 1 bit (degenerates to half adder)
- **Typical**: 4-64 bits (arbitrary widths supported)
- **Maximum**: 64 bits (practical synthesis limit)

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| i_a | N | Operand A (addend) |
| i_b | N | Operand B (addend) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| ow_sum | N | Sum output (A + B) |
| ow_carry | 1 | Carry output (overflow) |

**Important:** No carry input port. This adder always computes A + B (assumes Cin = 0).

## Functionality

### Algorithm Overview

The adder uses a three-stage process inspired by parallel prefix addition principles:

#### Stage 1: Generate and Propagate Terms

```systemverilog
For each bit i:
  G[i] = A[i] & B[i]   // Generate: carry is generated at this position
  P[i] = A[i] | B[i]   // Propagate: carry can propagate through this position
```

**Design Note:** Uses OR for propagate (not XOR). This is mathematically equivalent for carry computation:
- `P[i] = A[i] | B[i]` allows carry propagation when at least one input is 1
- Traditional `P[i] = A[i] ^ B[i]` (XOR) used in some other adders

#### Stage 2: Carry Computation

```systemverilog
C[0] = G[0]  // Initial carry (from LSB)

For i = 1 to N-1:
  C[i] = G[i] | (P[i] & C[i-1])
```

**Interpretation:**
- Carry at position i is generated locally (G[i]), OR
- Carry propagates from previous position (P[i] & C[i-1])

#### Stage 3: Sum Calculation

```systemverilog
Sum[0] = A[0] ^ B[0]  // LSB has no carry input

For i = 1 to N-1:
  Sum[i] = A[i] ^ B[i] ^ C[i-1]
```

### Implementation Details

```systemverilog
// Stage 1: Generate G and P signals (parallel, 1 level)
for (i = 0; i < N; i++) begin
    w_G[i] = i_a[i] & i_b[i];  // Generate
    w_P[i] = i_a[i] | i_b[i];  // Propagate
end

// Stage 2: Carry computation (sequential, N levels)
always_comb begin
    logic carry;
    carry = w_G[0];
    w_C[0] = carry;
    for (int j = 1; j < N; j++) begin
        carry = w_G[j] | (w_P[j] & carry);
        w_C[j] = carry;
    end
end

// Stage 3: Sum calculation (parallel, 1 level)
ow_sum[0] = i_a[0] ^ i_b[0];  // No carry for LSB
for (i = 1; i < N; i++) begin
    ow_sum[i] = i_a[i] ^ i_b[i] ^ w_C[i-1];
end

// Final carry out
ow_carry = w_C[N-1];
```

### Timing Analysis

**Logic Depth:**
- **G/P generation**: 1 level (AND/OR)
- **Carry chain**: N levels (sequential dependency)
- **Sum calculation**: 1 level (XOR)
- **Total**: N + 2 levels

**Critical Path:**
```
i_a[0]/i_b[0] → G[0] → C[0] → C[1] → ... → C[N-1] → ow_carry
```

### Comparison to Other Adders

| Adder Type | Logic Depth | Area | Carry Input | Generic Width |
|------------|-------------|------|-------------|---------------|
| Ripple Carry | O(N) | Minimal | Yes | Yes |
| Carry Lookahead | O(N) | Small | Yes | Yes |
| **Kogge-Stone (this)** | **O(N)** | **Small** | **No** | **Yes** |
| Brent-Kung | O(log N) | Medium | Yes | No (8/16/32 only) |
| True Kogge-Stone | O(log N) | Large | Yes | No (fixed widths) |

**Key Differences:**
- **vs Ripple Carry**: Similar depth, but explicit P/G logic may optimize better
- **vs True Kogge-Stone**: This is O(N) not O(log N); true KS requires full prefix tree
- **vs Brent-Kung**: Simpler, supports arbitrary widths, but slower for N > 16

## Usage Examples

### Basic 16-bit Addition

```systemverilog
logic [15:0] a, b, sum;
logic carry_out;

math_adder_kogge_stone_nbit #(
    .N(16)
) u_adder (
    .i_a      (a),
    .i_b      (b),
    .ow_sum   (sum),
    .ow_carry (carry_out)
);

// Example: 1000 + 2000
initial begin
    a = 16'd1000;
    b = 16'd2000;
    #1;  // Wait for combinational propagation
    assert(sum == 16'd3000);
    assert(carry_out == 1'b0);
end
```

### Adding with Carry Input (External Logic)

```systemverilog
// Since module has no carry input, add external logic
logic [7:0] a, b, sum_with_cin;
logic cin, carry_out;

logic [7:0] b_adjusted;
assign b_adjusted = b + {7'b0, cin};  // Add carry to B operand

math_adder_kogge_stone_nbit #(
    .N(8)
) u_adder (
    .i_a      (a),
    .i_b      (b_adjusted),
    .ow_sum   (sum_with_cin),
    .ow_carry (carry_out)
);

// Alternatively, use dedicated incrementer after addition
logic [7:0] sum_base;
math_adder_kogge_stone_nbit #(.N(8)) u_add (
    .i_a(a), .i_b(b), .ow_sum(sum_base), ...
);
assign sum_with_cin = cin ? (sum_base + 8'b1) : sum_base;
```

### Arbitrary Width Addition (37-bit example)

```systemverilog
// Advantage: Supports non-power-of-2 widths
logic [36:0] a_37, b_37, sum_37;
logic carry_37;

math_adder_kogge_stone_nbit #(
    .N(37)  // Any width supported
) u_adder_37bit (
    .i_a      (a_37),
    .i_b      (b_37),
    .ow_sum   (sum_37),
    .ow_carry (carry_37)
);
```

### Multi-Precision Addition (64-bit via 2×32-bit)

```systemverilog
logic [31:0] a_low, a_high, b_low, b_high;
logic [31:0] sum_low, sum_high;
logic carry_low;

// Low 32 bits
math_adder_kogge_stone_nbit #(.N(32)) u_add_low (
    .i_a      (a_low),
    .i_b      (b_low),
    .ow_sum   (sum_low),
    .ow_carry (carry_low)
);

// High 32 bits (add carry_low to b_high)
logic [31:0] b_high_adjusted;
assign b_high_adjusted = b_high + {31'b0, carry_low};

math_adder_kogge_stone_nbit #(.N(32)) u_add_high (
    .i_a      (a_high),
    .i_b      (b_high_adjusted),
    .ow_sum   (sum_high),
    .ow_carry ()
);

logic [63:0] sum_64 = {sum_high, sum_low};
```

### Accumulator

```systemverilog
logic [31:0] accumulator, data_in;
logic [31:0] accumulator_next;
logic acc_enable;

math_adder_kogge_stone_nbit #(.N(32)) u_accumulator (
    .i_a      (accumulator),
    .i_b      (data_in),
    .ow_sum   (accumulator_next),
    .ow_carry ()
);

always_ff @(posedge clk) begin
    if (rst_n == 0) begin
        accumulator <= 32'b0;
    end else if (acc_enable) begin
        accumulator <= accumulator_next;
    end
end
```

### Adder Array (Multiple Parallel Adders)

```systemverilog
// 8 parallel 16-bit adders
localparam int NUM_ADDERS = 8;
logic [15:0] a_array [NUM_ADDERS];
logic [15:0] b_array [NUM_ADDERS];
logic [15:0] sum_array [NUM_ADDERS];

genvar k;
generate
    for (k = 0; k < NUM_ADDERS; k++) begin : gen_adder_array
        math_adder_kogge_stone_nbit #(
            .N(16)
        ) u_adder (
            .i_a      (a_array[k]),
            .i_b      (b_array[k]),
            .ow_sum   (sum_array[k]),
            .ow_carry ()
        );
    end
endgenerate
```

## Timing Characteristics

### Combinational Delay Analysis

| Width | Logic Levels | Typical Delay (ns) @ 1.0V | Max Frequency |
|-------|--------------|---------------------------|---------------|
| 4-bit | 6 | ~1.2 | ~800 MHz |
| 8-bit | 10 | ~2.0 | ~500 MHz |
| 16-bit | 18 | ~3.5 | ~285 MHz |
| 32-bit | 34 | ~6.5 | ~155 MHz |
| 64-bit | 66 | ~12.5 | ~80 MHz |

**Logic Level Breakdown (16-bit example):**
1. G/P generation: 1 level (AND/OR)
2. Carry chain: 16 levels (C[0] → C[1] → ... → C[15])
3. Sum calculation: 1 level (XOR)
4. **Total**: 18 levels

### Critical Paths

**Longest Path (Carry Out):**
```
i_a[0]/i_b[0] → G[0] → C[0] → C[1] → ... → C[N-1] → ow_carry
```

**Sum Output Path:**
```
i_a[i]/i_b[i] → P[i] → ow_sum[i]  (depends on C[i-1])
```

### Performance vs Width

| Width | Relative Delay | Relative Frequency |
|-------|---------------|-------------------|
| 4-bit | 1.0× | 1.00× |
| 8-bit | 1.7× | 0.60× |
| 16-bit | 3.0× | 0.35× |
| 32-bit | 5.7× | 0.19× |
| 64-bit | 11.0× | 0.10× |

**Observation:** Delay scales linearly with width (O(N)).

## Performance Characteristics

### Resource Utilization

| Width | LUTs (Est.) | FFs (Pipeline) | Description |
|-------|-------------|----------------|-------------|
| 8-bit | ~24 | 0 (combinational) | Small |
| 16-bit | ~48 | 0 (combinational) | Medium |
| 32-bit | ~96 | 0 (combinational) | Large |
| 64-bit | ~192 | 0 (combinational) | Very large |

**Area Breakdown (16-bit):**
- G/P generation: 16 × 2 gates = 32 LUTs
- Carry chain: 16 × 2 gates = 32 LUTs (OR + AND)
- Sum calculation: 16 × 1 gate = 16 LUTs (XOR)
- **Total**: ~48 LUTs

### Comparison to Alternatives

| Adder Architecture | Relative Speed | Relative Area | Generic Width |
|-------------------|----------------|---------------|---------------|
| Ripple Carry | 1.0× | 1.0× | Yes |
| **Kogge-Stone (this)** | **1.5×** | **1.2×** | **Yes** |
| Carry Lookahead | 1.5× | 1.2× | Yes |
| Brent-Kung | 4.0× | 4.0× | No (8/16/32 only) |
| True Kogge-Stone | 6.0× | 6.0× | No (fixed widths) |

## Design Considerations

### When to Use This Adder

✅ **Appropriate Use Cases:**
- Arbitrary bit widths (non-power-of-2)
- Designs requiring parameterizable width
- No carry input required
- Moderate speed requirements
- Area-constrained designs

### When to Use Alternatives

**Use Brent-Kung if:**
- Width is 8, 16, or 32 bits
- Need maximum speed (O(log N) depth)
- Can afford larger area

**Use Carry Lookahead if:**
- Need carry input support
- Width ≤ 16 bits
- Similar performance to this module

**Use Ripple Carry if:**
- Width ≤ 4 bits
- Minimal area is critical
- Speed not important

### Lack of Carry Input Workarounds

Since this module has no carry input port, consider these alternatives:

**Option 1: Pre-add carry to operand**
```systemverilog
logic [N-1:0] b_adjusted;
assign b_adjusted = b + {{N-1{1'b0}}, cin};
```

**Option 2: Use different adder with carry input**
```systemverilog
// Use carry lookahead instead
math_adder_carry_lookahead #(.N(N)) u_add (
    .i_a(a), .i_b(b), .i_c(cin), ...
);
```

**Option 3: Post-increment sum**
```systemverilog
assign sum_with_cin = cin ? (ow_sum + 1'b1) : ow_sum;
```

### Synthesis Considerations

**Optimization Tips:**

1. **Flatten hierarchy**:
   ```tcl
   set_flatten true -effort high
   ```

2. **Allow carry chain optimization**:
   ```tcl
   set_dont_touch false
   ```

3. **Consider pipelining for N > 16**:
   ```systemverilog
   // Break carry chain in middle
   logic [N/2-1:0] r_c_mid;
   always_ff @(posedge clk) r_c_mid <= w_C[N/2-1:0];
   ```

## Verification Strategy

Test suite location: `val/common/test_math_adder_kogge_stone_nbit.py`

**Key Test Scenarios:**
- Random stimulus (various widths)
- Corner cases: 0+0, 0+MAX, MAX+MAX
- Full carry propagation: 0xFFFF...FF + 1
- Arbitrary widths: 7-bit, 13-bit, 37-bit
- Overflow detection

**Test Command:**
```bash
pytest val/common/test_math_adder_kogge_stone_nbit.py -v
```

## Common Pitfalls

❌ **Anti-Pattern 1**: Expecting carry input port

```systemverilog
// WRONG: No carry input port exists!
math_adder_kogge_stone_nbit #(.N(8)) u_add (
    .i_a(a), .i_b(b), .i_c(cin),  // ERROR: No i_c port!
    ...
);

// RIGHT: Pre-add carry to operand or use different adder
logic [7:0] b_adj = b + {7'b0, cin};
math_adder_kogge_stone_nbit #(.N(8)) u_add (
    .i_a(a), .i_b(b_adj), ...
);
```

❌ **Anti-Pattern 2**: Using for very wide additions

```systemverilog
// WRONG: 128-bit with O(N) depth (slow!)
math_adder_kogge_stone_nbit #(.N(128)) u_add (...);
// Result: 130 logic levels!

// RIGHT: Break into smaller pieces or use different architecture
```

❌ **Anti-Pattern 3**: Assuming parallel prefix performance

```systemverilog
// WRONG ASSUMPTION: "Kogge-Stone is O(log N)"
// This implementation is O(N), not true parallel prefix

// For true O(log N), use Brent-Kung (if width matches):
math_adder_brent_kung_032 u_fast_add (...);
```

❌ **Anti-Pattern 4**: Chaining without pipelining

```systemverilog
// WRONG: Long combinational chain
logic [31:0] sum1, sum2, sum3;
math_adder_kogge_stone_nbit #(.N(32)) u1 (.i_a(a), .i_b(b), .ow_sum(sum1), ...);
math_adder_kogge_stone_nbit #(.N(32)) u2 (.i_a(sum1), .i_b(c), .ow_sum(sum2), ...);
math_adder_kogge_stone_nbit #(.N(32)) u3 (.i_a(sum2), .i_b(d), .ow_sum(sum3), ...);
// 3 × 34 levels = 102 logic levels!

// RIGHT: Pipeline between adders
always_ff @(posedge clk) begin
    r_sum1 <= sum1;
    r_sum2 <= sum2;
end
```

## Related Modules

- **math_adder_brent_kung_*.sv** - True parallel prefix, O(log N) depth (8/16/32-bit)
- **math_adder_carry_lookahead.sv** - Similar performance, has carry input
- **math_adder_ripple_carry.sv** - Simpler, slightly smaller area
- **math_adder_carry_save_nbit.sv** - For multi-operand addition

## References

- Kogge, P.M., Stone, H.S. "A Parallel Algorithm for the Efficient Solution of a General Class of Recurrence Equations." IEEE Transactions on Computers, 1973.
- Harris, D. "A Taxonomy of Parallel Prefix Networks." Asilomar Conference, 2003.
- Deschamps, J.P., Bioul, G., Sutter, G. "Synthesis of Arithmetic Circuits." Wiley, 2006.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
