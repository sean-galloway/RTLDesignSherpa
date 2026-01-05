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

# Carry Lookahead Adder

A parameterized carry lookahead adder supporting arbitrary bit widths with O(N) depth using generate and propagate logic to reduce carry propagation delay compared to ripple carry adders.

## Overview

The `math_adder_carry_lookahead` module implements a carry lookahead adder (CLA) with parameterizable width. While not a true parallel-prefix lookahead (which would have O(log N) depth), this implementation uses propagate (P) and generate (G) signals to compute carries more efficiently than a simple ripple-carry adder. It provides a good balance between speed and area for small to medium width additions (4-16 bits).

## Module Declaration

```systemverilog
module math_adder_carry_lookahead #(
    parameter int N = 4      // Adder width in bits (any width ≥ 1)
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic         i_c,       // Carry input
    output logic [N-1:0] ow_sum,    // Sum output
    output logic         ow_carry   // Carry output
);
```

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Adder width in bits (range: 1-64, typical: 4-16) |

**Width Guidelines:**
- **Typical**: 4, 8, 16 bits (good speed/area balance)
- **Minimum**: 1 bit (degenerates to half adder)
- **Maximum**: 64 bits (practical synthesis limit, but consider parallel prefix for >16 bits)

**Design Note:** For N > 16, consider using `math_adder_brent_kung` or `math_adder_kogge_stone` for better performance.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| i_a | N | Operand A (addend) |
| i_b | N | Operand B (addend) |
| i_c | 1 | Carry input (0 for addition, 1 for +1 increment) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| ow_sum | N | Sum output (A + B + Cin) |
| ow_carry | 1 | Carry output (overflow) |

## Functionality

### Algorithm Overview

The carry lookahead adder uses **propagate (P)** and **generate (G)** signals to compute carries more efficiently than ripple carry:

#### Bit-Level Definitions

**For each bit position i:**
```
Generate:  G[i] = A[i] & B[i]   (carry is generated at this position)
Propagate: P[i] = A[i] ^ B[i]   (carry is propagated through this position)
```

#### Carry Calculation

**Initial carry:**
```
C[0] = Cin  (input carry)
```

**Carry recurrence (for i = 1 to N):**
```
C[i] = G[i-1] | (P[i-1] & C[i-1])
```

**Interpretation:**
- Carry is generated (G[i-1] = 1) at position i-1, OR
- Carry is propagated (P[i-1] = 1) from position i-1 if there was an incoming carry (C[i-1] = 1)

#### Sum Calculation

```
Sum[i] = P[i] ^ C[i]
```

Sum is XOR of propagate signal and incoming carry.

### Implementation

```systemverilog
// Stage 1: Generate P and G signals (parallel, 1 level of logic)
for (i = 0; i < N; i++) begin
    w_g[i] = i_a[i] & i_b[i];  // Generate
    w_p[i] = i_a[i] ^ i_b[i];  // Propagate
end

// Stage 2: Calculate carries (sequential dependency, N levels)
w_c[0] = i_c;
for (i = 1; i <= N; i++) begin
    w_c[i] = w_g[i-1] | (w_p[i-1] & w_c[i-1]);
end

// Stage 3: Calculate sum (parallel, 1 level of logic)
for (i = 0; i < N; i++) begin
    ow_sum[i] = w_p[i] ^ w_c[i];
end

// Final carry out
ow_carry = w_c[N];
```

### Timing Analysis

**Logic Depth:**
- **P/G generation**: 1 level (AND/XOR)
- **Carry chain**: N levels (each carry depends on previous)
- **Sum calculation**: 1 level (XOR)
- **Total**: N + 2 levels

**Critical Path:**
```
i_a/i_b → P[0]/G[0] → C[1] → C[2] → ... → C[N-1] → C[N] → Sum[N-1]
```

### Comparison to Other Adders

| Adder Type | Logic Depth | Area | Best Use Case |
|------------|-------------|------|---------------|
| Ripple Carry | O(N) | Minimal | N ≤ 4, area-critical |
| **CLA (this)** | **O(N)** | **Small** | **4 ≤ N ≤ 16, balanced** |
| Brent-Kung | O(log N) | Medium | N ≥ 16, speed-critical |
| Kogge-Stone | O(log N) | Large | N ≥ 32, max speed |

**Note:** True carry lookahead adders (with group generate/propagate) can achieve O(log N) depth but require more complex logic. This implementation is a hybrid approach optimized for simplicity and area.

## Usage Examples

### Basic 8-bit Addition

```systemverilog
logic [7:0] a, b, sum;
logic carry_out;

math_adder_carry_lookahead #(
    .N(8)
) u_adder (
    .i_a      (a),
    .i_b      (b),
    .i_c      (1'b0),        // No carry input
    .ow_sum   (sum),
    .ow_carry (carry_out)
);

// Example: 200 + 100
initial begin
    a = 8'd200;
    b = 8'd100;
    #1;  // Wait for combinational propagation
    assert(sum == 8'd44);       // 300 % 256 = 44
    assert(carry_out == 1'b1);  // Overflow
end
```

### 4-bit Incrementer

```systemverilog
logic [3:0] count, count_plus_1;

math_adder_carry_lookahead #(
    .N(4)
) u_incrementer (
    .i_a      (count),
    .i_b      (4'b0),        // B = 0
    .i_c      (1'b1),        // Carry in = 1 → +1
    .ow_sum   (count_plus_1),
    .ow_carry ()             // Unused
);
```

### 16-bit ALU Component

```systemverilog
typedef enum logic [2:0] {
    ALU_ADD  = 3'b000,
    ALU_SUB  = 3'b001,
    ALU_INC  = 3'b010,
    ALU_DEC  = 3'b011
} alu_op_t;

module simple_alu (
    input  logic [15:0]  a,
    input  logic [15:0]  b,
    input  alu_op_t      op,
    output logic [15:0]  result,
    output logic         carry,
    output logic         zero
);

    logic [15:0] b_mux;
    logic        cin_mux;

    // Operation selection
    always_comb begin
        case (op)
            ALU_ADD: begin
                b_mux = b;
                cin_mux = 1'b0;
            end
            ALU_SUB: begin
                b_mux = ~b;          // Two's complement: A + (~B) + 1
                cin_mux = 1'b1;
            end
            ALU_INC: begin
                b_mux = 16'b0;
                cin_mux = 1'b1;      // A + 0 + 1 = A + 1
            end
            ALU_DEC: begin
                b_mux = 16'hFFFF;    // -1 in two's complement
                cin_mux = 1'b0;      // A + (-1) + 0 = A - 1
            end
            default: begin
                b_mux = 16'b0;
                cin_mux = 1'b0;
            end
        endcase
    end

    // Adder
    math_adder_carry_lookahead #(
        .N(16)
    ) u_adder (
        .i_a      (a),
        .i_b      (b_mux),
        .i_c      (cin_mux),
        .ow_sum   (result),
        .ow_carry (carry)
    );

    // Zero flag
    assign zero = ~|result;

endmodule
```

### Multi-Precision Addition (32-bit via 2×16-bit)

```systemverilog
logic [15:0] a_low, a_high, b_low, b_high;
logic [15:0] sum_low, sum_high;
logic carry_low, carry_high;

// Low 16 bits
math_adder_carry_lookahead #(.N(16)) u_add_low (
    .i_a      (a_low),
    .i_b      (b_low),
    .i_c      (1'b0),
    .ow_sum   (sum_low),
    .ow_carry (carry_low)
);

// High 16 bits (chain carry from low)
math_adder_carry_lookahead #(.N(16)) u_add_high (
    .i_a      (a_high),
    .i_b      (b_high),
    .i_c      (carry_low),     // Carry from low adder
    .ow_sum   (sum_high),
    .ow_carry (carry_high)
);

// Concatenate results
logic [31:0] sum_32 = {sum_high, sum_low};
```

### Conditional Increment (For Loop Counters)

```systemverilog
logic [7:0] loop_counter;
logic loop_active, loop_done;

math_adder_carry_lookahead #(.N(8)) u_loop_inc (
    .i_a      (loop_counter),
    .i_b      (8'b0),
    .i_c      (loop_active),   // Increment only when active
    .ow_sum   (loop_counter_next),
    .ow_carry ()
);

always_ff @(posedge clk) begin
    if (rst_n == 0) begin
        loop_counter <= 8'b0;
    end else if (loop_active) begin
        loop_counter <= loop_counter_next;
    end
end

assign loop_done = (loop_counter == 8'd99);
```

## Timing Characteristics

### Combinational Delay Analysis

| Width | Logic Levels | Typical Delay (ns) @ 1.0V | Max Frequency |
|-------|--------------|---------------------------|---------------|
| 4-bit | 6 | ~1.2 | ~800 MHz |
| 8-bit | 10 | ~2.0 | ~500 MHz |
| 16-bit | 18 | ~3.5 | ~285 MHz |
| 32-bit | 34 | ~6.5 | ~155 MHz |

**Logic Level Breakdown (8-bit example):**
1. P/G generation: 1 level (AND/XOR)
2. Carry chain: 8 levels (C[1] → C[2] → ... → C[8])
3. Sum calculation: 1 level (XOR)
4. **Total**: 10 levels

### Critical Paths

**Main Critical Path (Longest):**
```
i_a[0]/i_b[0] → P[0]/G[0] → C[1] → C[2] → ... → C[N] → ow_carry
```

**Sum Output Path:**
```
i_a[i]/i_b[i] → P[i] → ow_sum[i]  (depends on C[i] from carry chain)
```

### Performance vs Width

| Width | Delay (relative) | Frequency (relative) |
|-------|-----------------|---------------------|
| 4-bit | 1.0× (baseline) | 1.00× (baseline) |
| 8-bit | 1.7× | 0.60× |
| 16-bit | 3.0× | 0.35× |
| 32-bit | 5.7× | 0.19× |

**Observation:** Delay scales linearly with width → Consider parallel prefix adders (Brent-Kung, Kogge-Stone) for N > 16.

## Performance Characteristics

### Resource Utilization

| Width | LUTs (Est.) | FFs (Pipeline) | Description |
|-------|-------------|----------------|-------------|
| 4-bit | ~12 | 0 (combinational) | Minimal |
| 8-bit | ~24 | 0 (combinational) | Small |
| 16-bit | ~48 | 0 (combinational) | Medium |
| 32-bit | ~96 | 0 (combinational) | Large (consider alternatives) |

**Area Breakdown (8-bit):**
- P/G generation: 8 × 2 gates = 16 LUTs
- Carry chain: 8 × 2 gates = 16 LUTs (OR + AND)
- Sum calculation: 8 × 1 gate = 8 LUTs (XOR)
- **Total**: ~24 LUTs (may optimize to fewer)

### Speed vs Area Trade-offs

| Adder Architecture | Relative Speed | Relative Area | Best Width Range |
|-------------------|----------------|---------------|------------------|
| Ripple Carry | 1.0× (slowest) | 1.0× (smallest) | N ≤ 4 |
| **CLA (this)** | **1.5×** | **1.2×** | **4 ≤ N ≤ 16** |
| Brent-Kung | 4.0× | 4.0× | 16 ≤ N ≤ 32 |
| Kogge-Stone | 6.0× (fastest) | 6.0× (largest) | N ≥ 32 |

## Design Considerations

### When to Use This Adder

✅ **Appropriate Use Cases:**
- Small to medium width additions (4-16 bits)
- Area-constrained designs with moderate speed requirements
- ALU components in simple processors
- Address arithmetic (incrementers, offsets)
- Simple calculators or counters
- FPGA designs with limited LUT budget

❌ **Consider Alternatives When:**
- **N > 16**: Use Brent-Kung or Kogge-Stone for better speed
- **N ≤ 4**: Use ripple carry for minimal area
- **Critical datapath**: Use parallel prefix adders (Brent-Kung/Kogge-Stone)
- **Very high frequency**: Pipeline or use faster adder architecture

### Width Selection Guidelines

**Recommended Widths:**
- **4-bit**: Good for nibble operations, BCD arithmetic
- **8-bit**: Standard byte operations, small ALU
- **16-bit**: Address arithmetic, medium-width ALU
- **32-bit**: Only if area is critical (prefer Brent-Kung)

### Synthesis Considerations

**Optimization Tips:**

1. **Flatten hierarchy** for better carry chain optimization:
   ```tcl
   set_flatten true -effort high
   ```

2. **Mark as combinational** to prevent retiming issues:
   ```tcl
   set_dont_touch u_adder/w_c* false
   ```

3. **Critical path optimization**:
   ```tcl
   set_max_delay -from [get_ports i_a] -to [get_ports ow_carry] 2.0
   ```

4. **Consider pipelining** for N > 16:
   ```systemverilog
   // Pipeline example: Break carry chain in middle
   logic [N/2:0] r_c_mid;
   logic [N-1:0] r_sum_high;

   always_ff @(posedge clk) begin
       r_c_mid <= w_c[N/2];  // Register mid-point carry
   end
   ```

### Verilator Lint Note

The module includes a Verilator pragma:
```systemverilog
/* verilator lint_off UNOPTFLAT */
// ... carry chain logic ...
/* verilator lint_on UNOPTFLAT */
```

**Reason:** Carry chain creates combinational loops that Verilator warns about but are intentional for CLA operation.

## Verification Strategy

Test suite location: `val/common/test_math_adder_carry_lookahead.py`

**Key Test Scenarios:**
- Random stimulus (all widths)
- Corner cases: 0+0, 0+MAX, MAX+MAX, MAX+1
- Carry propagation: All 1's + 1 (tests full carry chain)
- Incrementer mode: A + 0 + 1
- Subtraction mode: A + (~B) + 1
- Multi-precision chaining

**Test Command:**
```bash
pytest val/common/test_math_adder_carry_lookahead.py -v
```

## Common Pitfalls

❌ **Anti-Pattern 1**: Using for very wide additions without pipelining

```systemverilog
// WRONG: 64-bit addition with CLA (poor performance)
math_adder_carry_lookahead #(.N(64)) u_add (...);
// Result: 66 logic levels, very slow!

// RIGHT: Use parallel prefix adder
math_adder_brent_kung_032 u_add_low (...)  // Lower 32 bits
math_adder_brent_kung_032 u_add_high (...)  // Upper 32 bits
```

❌ **Anti-Pattern 2**: Expecting registered outputs

```systemverilog
// WRONG: Assuming outputs are registered
always_ff @(posedge clk) begin
    data <= ow_sum;  // ow_sum is combinational!
end

// RIGHT: Add explicit output register
logic [N-1:0] r_sum;
always_ff @(posedge clk) begin
    r_sum <= ow_sum;
end
```

❌ **Anti-Pattern 3**: Chaining adders without pipelining

```systemverilog
// WRONG: Long chain without pipeline
logic [15:0] a, b, c, d, result;
logic [15:0] ab_sum, abc_sum;

math_adder_carry_lookahead #(.N(16)) u1 (.i_a(a), .i_b(b), .ow_sum(ab_sum), ...);
math_adder_carry_lookahead #(.N(16)) u2 (.i_a(ab_sum), .i_b(c), .ow_sum(abc_sum), ...);
math_adder_carry_lookahead #(.N(16)) u3 (.i_a(abc_sum), .i_b(d), .ow_sum(result), ...);

// 3 × 18 levels = 54 logic levels!

// RIGHT: Pipeline the chain
always_ff @(posedge clk) begin
    r_ab_sum <= ab_sum;
    r_abc_sum <= abc_sum;
end
```

❌ **Anti-Pattern 4**: Ignoring synthesis warnings

```verilog
// Synthesis warning: "Combinational loop detected"
// This is expected for CLA carry chain, but verify:
// - Loop is intentional
// - No actual circular dependency
// - All signals eventually resolve
```

## Related Modules

- **math_adder_brent_kung_*.sv** - Faster parallel prefix adder (O(log N) depth)
- **math_adder_kogge_stone_nbit.sv** - Fastest parallel prefix adder
- **math_adder_ripple_carry.sv** - Minimal area adder (slower)
- **math_adder_carry_save_nbit.sv** - For multi-operand addition (multipliers)
- **math_subtractor_carry_lookahead.sv** - CLA-based subtractor variant

## References

- Weinberger, A., Smith, J.L. "A Logic for High-Speed Addition." National Bureau of Standards, 1958.
- Sklanski, J. "Conditional-Sum Addition Logic." IRE Transactions on Electronic Computers, 1960.
- Deschamps, J.P., Bioul, G., Sutter, G. "Synthesis of Arithmetic Circuits: FPGA, ASIC and Embedded Systems." Wiley, 2006.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
