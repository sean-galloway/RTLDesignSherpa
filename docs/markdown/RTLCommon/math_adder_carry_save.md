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

# Carry-Save Adder

Single-bit and N-bit carry-save adder modules for high-speed multi-operand addition, implementing 3:2 compression with constant-depth parallel operation. These modules are fundamental building blocks for fast multipliers and multi-operand addition trees.

## Overview

Carry-save adders (CSAs) perform parallel addition of three operands in a single level of logic by keeping the sum and carry outputs separate (not chaining carries between bits). This enables:
- **Constant depth**: O(1) logic depth regardless of bit width
- **3:2 compression**: Reduce 3 numbers to 2 in one stage
- **Multiplier trees**: Essential for Wallace and Dadda tree multipliers
- **Multi-operand addition**: Add many numbers efficiently

**Modules Covered:**
- **math_adder_carry_save** - Single-bit CSA (3:2 compressor)
- **math_adder_carry_save_nbit** - N-bit parallel CSA array

## Module Declarations

### Single-bit Carry-Save Adder

```systemverilog
module math_adder_carry_save (
    input  logic i_a,        // Input A
    input  logic i_b,        // Input B
    input  logic i_c,        // Input C
    output logic ow_sum,     // Sum output
    output logic ow_carry    // Carry output
);
```

### N-bit Carry-Save Adder

```systemverilog
module math_adder_carry_save_nbit #(
    parameter int N = 4      // Bit width
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic [N-1:0] i_c,       // Operand C (or carry from previous CSA)
    output logic [N-1:0] ow_sum,    // Sum outputs (parallel)
    output logic [N-1:0] ow_carry   // Carry outputs (parallel, NOT chained!)
);
```

## Parameters

### Single-bit CSA

No parameters (fixed single-bit operation).

### N-bit CSA

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Bit width (range: 1-64, typical: 8-64) |

**Width Guidelines:**
- **Typical**: 8-64 bits (matches datapath width)
- **Multipliers**: Match partial product width
- **No practical limit**: CSA depth is independent of N

## Ports

### Single-bit CSA Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | 1 | Input A |
| i_b | Input | 1 | Input B |
| i_c | Input | 1 | Input C |
| ow_sum | Output | 1 | Sum output bit |
| ow_carry | Output | 1 | Carry output bit |

### N-bit CSA Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | N | Operand A |
| i_b | Input | N | Operand B |
| i_c | Input | N | Operand C |
| ow_sum | Output | N | Sum vector (parallel) |
| ow_carry | Output | N | Carry vector (parallel, NOT shifted!) |

**Important:** The N-bit CSA outputs TWO N-bit vectors. To get the final result, you must add them using a conventional adder (ripple carry, CLA, or parallel prefix).

## Functionality

### Single-bit Carry-Save Adder (3:2 Compressor)

The CSA compresses 3 bits into 2 bits (sum and carry):

**Logic Equations:**
```
Sum = A ⊕ B ⊕ C                                    // 3-input XOR
Carry = (A • B) | (A • C) | (B • C)                // Majority function
      = Majority(A, B, C)
```

**Truth Table:**
| A | B | C | Sum | Carry | A+B+C (decimal) |
|---|---|---|-----|-------|-----------------|
| 0 | 0 | 0 | 0   | 0     | 0               |
| 0 | 0 | 1 | 1   | 0     | 1               |
| 0 | 1 | 0 | 1   | 0     | 1               |
| 0 | 1 | 1 | 0   | 1     | 2               |
| 1 | 0 | 0 | 1   | 0     | 1               |
| 1 | 0 | 1 | 0   | 1     | 2               |
| 1 | 1 | 0 | 0   | 1     | 2               |
| 1 | 1 | 1 | 1   | 1     | 3               |

**Key Property:** Sum + 2×Carry = A + B + C (mathematically exact)

**Implementation:**
```systemverilog
assign ow_sum   = i_a ^ i_b ^ i_c;                          // XOR
assign ow_carry = (i_a & i_b) | (i_a & i_c) | (i_b & i_c); // Majority
```

**Note:** This is identical to a full adder, but used differently:
- **Full adder**: Carry chains to next bit
- **CSA**: Carry kept separate, processed in next stage

### N-bit Carry-Save Adder

The N-bit CSA applies 3:2 compression to each bit position in parallel:

```
Bit 0:  CSA(A[0], B[0], C[0]) → Sum[0], Carry[0]
Bit 1:  CSA(A[1], B[1], C[1]) → Sum[1], Carry[1]
...
Bit N-1: CSA(A[N-1], B[N-1], C[N-1]) → Sum[N-1], Carry[N-1]
```

**Implementation:**
```systemverilog
genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_carry_save
        assign ow_sum[i]   = i_a[i] ^ i_b[i] ^ i_c[i];
        assign ow_carry[i] = (i_a[i] & i_b[i]) | (i_a[i] & i_c[i]) | (i_b[i] & i_c[i]);
    end
endgenerate
```

**Critical Difference from Ripple Carry:**
- **Carry NOT chained**: Each bit's carry goes to separate output, not to next bit
- **Constant depth**: All bits computed in parallel (1 level of logic)
- **Requires final addition**: Must add sum and carry vectors to get actual result

### Final Addition Step

To get the actual sum, add the two output vectors (carry is in same weight position):

```systemverilog
// CSA produces two vectors
math_adder_carry_save_nbit #(.N(N)) u_csa (
    .i_a(a), .i_b(b), .i_c(c),
    .ow_sum(sum_vec),
    .ow_carry(carry_vec)
);

// Add the two vectors to get final result
// IMPORTANT: Carry vector is NOT shifted!
logic [N:0] final_result;
assign final_result = {1'b0, sum_vec} + {1'b0, carry_vec};
```

**Common Misconception:** The carry vector does NOT need left-shifting. The CSA already accounts for weight alignment internally.

## Timing Characteristics

### Propagation Delays

| Module | Logic Levels | Typical Delay (ns) |
|--------|--------------|-------------------|
| Single-bit CSA | 2 | ~0.4 |
| N-bit CSA | 2 | ~0.4 (independent of N!) |

**Key Advantage:** Delay is constant regardless of bit width!

**Critical Path:**
```
i_a/i_b/i_c → ow_sum    (2 XOR gates)
i_a/i_b/i_c → ow_carry  (2 gates: AND + OR)
```

**Comparison:**
| Adder Type | N-bit Delay |
|------------|-------------|
| **CSA** | **O(1)** - constant |
| Ripple Carry | O(N) - linear |
| Carry Lookahead | O(N) - linear (simplified) |
| Parallel Prefix | O(log N) |

## Usage Examples

### Adding 3 Numbers (Single CSA Stage)

```systemverilog
logic [7:0] a, b, c;
logic [7:0] sum_vec, carry_vec;
logic [8:0] final_result;

// Stage 1: CSA reduces 3 numbers to 2
math_adder_carry_save_nbit #(.N(8)) u_csa (
    .i_a(a),
    .i_b(b),
    .i_c(c),
    .ow_sum(sum_vec),
    .ow_carry(carry_vec)
);

// Stage 2: Conventional adder produces final result
assign final_result = {1'b0, sum_vec} + {1'b0, carry_vec};

// Example: 10 + 20 + 30 = 60
initial begin
    a = 8'd10;
    b = 8'd20;
    c = 8'd30;
    #1;
    assert(final_result == 9'd60);
end
```

### Adding 4 Numbers (2-Level CSA Tree)

```systemverilog
logic [7:0] a, b, c, d;
logic [7:0] sum1, carry1;
logic [7:0] sum2, carry2;
logic [9:0] final_result;

// Level 1: CSA reduces 4 numbers to 2 (actually 3)
// CSA1: A + B + C → Sum1, Carry1
math_adder_carry_save_nbit #(.N(8)) u_csa1 (
    .i_a(a), .i_b(b), .i_c(c),
    .ow_sum(sum1),
    .ow_carry(carry1)
);

// Level 2: CSA reduces 3 numbers to 2
// CSA2: Sum1 + Carry1 + D → Sum2, Carry2
math_adder_carry_save_nbit #(.N(8)) u_csa2 (
    .i_a(sum1),
    .i_b(carry1),
    .i_c(d),
    .ow_sum(sum2),
    .ow_carry(carry2)
);

// Final: Conventional adder
assign final_result = {2'b0, sum2} + {2'b0, carry2};
```

### Adding 7 Numbers (Wallace Tree Structure)

```systemverilog
// Reduce 7 numbers to 2 using CSA tree
logic [7:0] n1, n2, n3, n4, n5, n6, n7;

// Level 1: 7 → 5 (two CSAs)
logic [7:0] l1_s1, l1_c1, l1_s2, l1_c2;
math_adder_carry_save_nbit #(.N(8)) u_csa_l1_1 (
    .i_a(n1), .i_b(n2), .i_c(n3),
    .ow_sum(l1_s1), .ow_carry(l1_c1)
);
math_adder_carry_save_nbit #(.N(8)) u_csa_l1_2 (
    .i_a(n4), .i_b(n5), .i_c(n6),
    .ow_sum(l1_s2), .ow_carry(l1_c2)
);
// n7 passes through

// Level 2: 5 → 4 (one CSA)
logic [7:0] l2_s1, l2_c1;
math_adder_carry_save_nbit #(.N(8)) u_csa_l2_1 (
    .i_a(l1_s1), .i_b(l1_c1), .i_c(l1_s2),
    .ow_sum(l2_s1), .ow_carry(l2_c1)
);
// l1_c2, n7 pass through

// Level 3: 4 → 3 (one CSA)
logic [7:0] l3_s1, l3_c1;
math_adder_carry_save_nbit #(.N(8)) u_csa_l3_1 (
    .i_a(l2_s1), .i_b(l2_c1), .i_c(l1_c2),
    .ow_sum(l3_s1), .ow_carry(l3_c1)
);
// n7 passes through

// Level 4: 3 → 2 (one CSA)
logic [7:0] l4_s1, l4_c1;
math_adder_carry_save_nbit #(.N(8)) u_csa_l4_1 (
    .i_a(l3_s1), .i_b(l3_c1), .i_c(n7),
    .ow_sum(l4_s1), .ow_carry(l4_c1)
);

// Final addition
logic [9:0] final_result;
assign final_result = {2'b0, l4_s1} + {2'b0, l4_c1};
```

### 8-bit×8-bit Multiplier Partial Product Reduction

```systemverilog
// Generate partial products (8×8 = 8 partial products)
logic [7:0] pp [0:7];  // Partial products

// CSA tree to reduce 8 partial products to 2
// (Simplified - real implementation more complex)

// Level 1: 8 → 6 (two CSAs)
logic [15:0] l1_s1, l1_c1, l1_s2, l1_c2;
math_adder_carry_save_nbit #(.N(16)) u_csa_pp_l1_1 (
    .i_a({8'b0, pp[0]}),
    .i_b({7'b0, pp[1], 1'b0}),
    .i_c({6'b0, pp[2], 2'b0}),
    .ow_sum(l1_s1), .ow_carry(l1_c1)
);
// ... continue tree reduction
// Final: Fast adder for last two vectors
```

## Performance Characteristics

### Resource Utilization

| Module | LUTs | Description |
|--------|------|-------------|
| Single-bit CSA | 2 | 1 XOR + 1 Majority |
| N-bit CSA | ~2N | N single-bit CSAs |

**Comparison to Full Adder:**
- **Logic**: Identical (both use XOR + Majority)
- **Usage**: Different (parallel vs chained)
- **Area**: Same (~2 LUTs per bit)

### Speed Advantages

**CSA vs Ripple Carry Adder (8-bit example):**

| Operation | Depth | Delay (ns) |
|-----------|-------|-----------|
| CSA (parallel) | 2 levels | ~0.4 |
| Ripple (sequential) | 16 levels | ~3.0 |
| **Speedup** | **8×** | **7.5×** |

**Why CSA is Faster:**
- No carry propagation between bits
- All bits computed in parallel
- Constant depth regardless of width

## Design Considerations

### When to Use Carry-Save Adders

✅ **Ideal Use Cases:**
- **Multipliers**: Wallace tree, Dadda tree
- **Multi-operand addition**: Add 3+ numbers
- **DSP applications**: MAC units, filters
- **Dot products**: Sum of products
- **Compression trees**: Reduce many numbers to few

### When NOT to Use CSA

❌ **Inappropriate Use Cases:**
- **Two-operand addition**: Use conventional adder (simpler)
- **Final result needed immediately**: CSA requires additional adder stage
- **Single addition**: No benefit over regular adder

### CSA Tree Design Guidelines

**Number of Stages:**
```
N operands → ceil(log_1.5(N)) CSA stages + 1 final adder
```

**Example:**
- 3 operands: 1 CSA + 1 adder
- 7 operands: 4 CSA + 1 adder
- 15 operands: 6 CSA + 1 adder

**Optimization:** Minimize final adder width by aligning partial products carefully.

### Final Adder Selection

After CSA tree reduction, choose final adder wisely:

| Width | Best Final Adder |
|-------|-----------------|
| ≤ 8 bits | Ripple carry (small, adequate) |
| 8-16 bits | Carry lookahead |
| 16-32 bits | Brent-Kung |
| ≥ 32 bits | Kogge-Stone or pipelined |

## Common Pitfalls

❌ **Anti-Pattern 1**: Shifting carry output

```systemverilog
// WRONG: Don't shift carry vector!
assign final_result = sum_vec + {carry_vec, 1'b0};  // INCORRECT!

// RIGHT: Add without shift (CSA handles alignment)
assign final_result = sum_vec + carry_vec;
```

❌ **Anti-Pattern 2**: Using CSA for two-operand addition

```systemverilog
// WRONG: Overkill for simple addition
math_adder_carry_save_nbit u_csa (
    .i_a(a), .i_b(b), .i_c(8'b0),  // Third input wasted!
    ...
);
assign result = sum_vec + carry_vec;  // Extra adder stage!

// RIGHT: Use conventional adder
assign result = a + b;  // Simpler, same result
```

❌ **Anti-Pattern 3**: Ignoring final addition

```systemverilog
// WRONG: CSA outputs are NOT the final result!
math_adder_carry_save_nbit u_csa (
    .i_a(a), .i_b(b), .i_c(c),
    .ow_sum(result),        // INCOMPLETE!
    .ow_carry(ignored)      // Missing carry!
);

// RIGHT: Add sum and carry vectors
assign final_result = ow_sum + ow_carry;
```

❌ **Anti-Pattern 4**: Incorrect width for final addition

```systemverilog
// WRONG: Overflow possible
logic [7:0] a, b, c;
logic [7:0] sum_vec, carry_vec;
logic [7:0] result;  // TOO NARROW!
assign result = sum_vec + carry_vec;  // May overflow!

// RIGHT: Add extra bit for overflow
logic [8:0] result;  // Width N+1
assign result = {1'b0, sum_vec} + {1'b0, carry_vec};
```

## Related Modules

- **math_adder_full.sv** - Identical logic, used in ripple chains
- **math_multiplier_wallace_tree_*.sv** - Uses CSA for partial product reduction
- **math_multiplier_dadda_tree_*.sv** - Uses CSA with optimized schedule
- **math_multiplier_carry_save.sv** - Multiplier variant using CSA stages

## References

- Wallace, C.S. "A Suggestion for a Fast Multiplier." IEEE Transactions on Electronic Computers, 1964.
- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza, 1965.
- Deschamps, J.P., Bioul, G., Sutter, G. "Synthesis of Arithmetic Circuits." Wiley, 2006.
- Hennessy, J.L., Patterson, D.A. "Computer Architecture: A Quantitative Approach." Morgan Kaufmann, 2011.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
