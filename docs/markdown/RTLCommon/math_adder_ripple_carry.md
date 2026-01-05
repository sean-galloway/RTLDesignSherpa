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

# Ripple Carry Adder

A parameterized N-bit ripple carry adder built from a chain of full adders, providing minimal area at the cost of O(N) propagation delay. This is the simplest and most area-efficient multi-bit adder architecture.

## Overview

The `math_adder_ripple_carry` module implements the classic ripple carry adder where carry propagates sequentially from LSB to MSB through a chain of full adders. While this results in O(N) delay (slowest among adder architectures), it offers the smallest area and simplest implementation, making it ideal for low-speed, area-critical applications.

## Module Declaration

```systemverilog
module math_adder_ripple_carry #(
    parameter int N = 4      // Adder width in bits (any width ≥ 1)
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic         i_c,       // Carry input
    output logic [N-1:0] ow_sum,    // Sum output
    output logic         ow_carry   // Carry output
);
```

**Related Module:** `math_adder_full_nbit` provides functionally identical behavior with slightly different internal structure (uniform generate loop vs explicit first full adder).

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Adder width in bits (range: 1-64, typical: 2-8) |

**Width Guidelines:**
- **Optimal**: 2-8 bits (best area/speed trade-off for this architecture)
- **Minimum**: 1 bit (degenerates to single full adder)
- **Maximum**: 64 bits (practical limit, but very slow)
- **Above 16 bits**: Consider carry lookahead or parallel prefix adders

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
| ow_carry | 1 | Carry output (final carry from MSB) |

## Functionality

### Algorithm: Sequential Carry Propagation

The ripple carry adder computes addition bit-by-bit from LSB to MSB, with each bit's carry output feeding the next bit's carry input:

```
Bit 0 (LSB):  Sum[0], C[0] = FullAdder(A[0], B[0], Cin)
Bit 1:        Sum[1], C[1] = FullAdder(A[1], B[1], C[0])
Bit 2:        Sum[2], C[2] = FullAdder(A[2], B[2], C[1])
...
Bit N-1 (MSB): Sum[N-1], Cout = FullAdder(A[N-1], B[N-1], C[N-2])
```

### Full Adder Building Block

Each bit position uses a full adder with three inputs:

```systemverilog
// Full adder logic (implemented in math_adder_full.sv)
assign sum   = a ^ b ^ c_in;                    // XOR for sum
assign c_out = (a & b) | (c_in & (a ^ b));     // Majority function for carry
```

**Truth Table:**
| A | B | Cin | Sum | Cout |
|---|---|-----|-----|------|
| 0 | 0 | 0   | 0   | 0    |
| 0 | 0 | 1   | 1   | 0    |
| 0 | 1 | 0   | 1   | 0    |
| 0 | 1 | 1   | 0   | 1    |
| 1 | 0 | 0   | 1   | 0    |
| 1 | 0 | 1   | 0   | 1    |
| 1 | 1 | 0   | 0   | 1    |
| 1 | 1 | 1   | 1   | 1    |

### Implementation

```systemverilog
// Intermediate carries between full adders
logic [N-1:0] w_c;

// First full adder (LSB) - uses input carry i_c
math_adder_full fa0 (
    .i_a(i_a[0]),
    .i_b(i_b[0]),
    .i_c(i_c),
    .ow_sum(ow_sum[0]),
    .ow_carry(w_c[0])
);

// Remaining full adders - chain carry from previous stage
genvar i;
generate
    for (i = 1; i < N; i++) begin : gen_full_adders
        math_adder_full fa (
            .i_a(i_a[i]),
            .i_b(i_b[i]),
            .i_c(w_c[i-1]),        // Carry from previous bit
            .ow_sum(ow_sum[i]),
            .ow_carry(w_c[i])
        );
    end
endgenerate

// Final carry out
assign ow_carry = w_c[N-1];
```

### Timing Analysis

**Logic Depth:**
- **Per bit**: 2 levels (XOR for sum + Carry logic)
- **Carry chain**: N × 2 levels (sequential dependency)
- **Total**: 2N levels

**Critical Path (Carry Propagation):**
```
i_c → FA[0].Cout → FA[1].Cout → ... → FA[N-1].Cout → ow_carry
```

**Why It's Slow:** The critical path traverses all N full adders sequentially. Each full adder adds 2 gate delays, resulting in total delay proportional to N.

### Comparison to Other Adders

| Adder Type | Logic Depth | Area (relative) | Speed (relative) | Best Use Case |
|------------|-------------|-----------------|------------------|---------------|
| **Ripple Carry** | **O(N)** | **1.0× (min)** | **1.0× (slowest)** | **N ≤ 8, area-critical** |
| Carry Lookahead | O(N) | 1.2× | 1.5× | 4 ≤ N ≤ 16 |
| Brent-Kung | O(log N) | 4.0× | 4.0× | 16 ≤ N ≤ 32 |
| Kogge-Stone | O(log N) | 6.0× | 6.0× | N ≥ 32, critical path |

**Key Advantage:** Smallest possible adder area - only N full adders, no additional logic.

## Usage Examples

### Basic 8-bit Addition

```systemverilog
logic [7:0] a, b, sum;
logic carry_out;

math_adder_ripple_carry #(
    .N(8)
) u_adder (
    .i_a      (a),
    .i_b      (b),
    .i_c      (1'b0),        // No carry input
    .ow_sum   (sum),
    .ow_carry (carry_out)
);

// Example: 100 + 50
initial begin
    a = 8'd100;
    b = 8'd50;
    #1;  // Wait for combinational propagation
    assert(sum == 8'd150);
end
```

### 4-bit Incrementer

```systemverilog
logic [3:0] count, count_plus_1;

math_adder_ripple_carry #(
    .N(4)
) u_incrementer (
    .i_a      (count),
    .i_b      (4'b0),        // B = 0
    .i_c      (1'b1),        // Carry in = 1 → +1
    .ow_sum   (count_plus_1),
    .ow_carry ()             // Unused
);
```

### BCD Digit Adder (4-bit)

```systemverilog
// Add two BCD digits (0-9)
logic [3:0] bcd_a, bcd_b, bcd_sum_raw;
logic [3:0] bcd_sum_corrected;
logic carry_raw, carry_corrected;

// Raw binary addition
math_adder_ripple_carry #(.N(4)) u_bcd_add (
    .i_a      (bcd_a),
    .i_b      (bcd_b),
    .i_c      (1'b0),
    .ow_sum   (bcd_sum_raw),
    .ow_carry (carry_raw)
);

// BCD correction: if sum > 9, add 6
logic bcd_overflow;
assign bcd_overflow = carry_raw | (bcd_sum_raw > 4'd9);

math_adder_ripple_carry #(.N(4)) u_bcd_correct (
    .i_a      (bcd_sum_raw),
    .i_b      (bcd_overflow ? 4'd6 : 4'd0),
    .i_c      (1'b0),
    .ow_sum   (bcd_sum_corrected),
    .ow_carry ()
);

assign bcd_carry_out = bcd_overflow;
```

### Multi-Precision Addition (16-bit via 2×8-bit)

```systemverilog
logic [7:0] a_low, a_high, b_low, b_high;
logic [7:0] sum_low, sum_high;
logic carry_low, carry_high;

// Low byte
math_adder_ripple_carry #(.N(8)) u_add_low (
    .i_a      (a_low),
    .i_b      (b_low),
    .i_c      (1'b0),
    .ow_sum   (sum_low),
    .ow_carry (carry_low)
);

// High byte (chain carry from low)
math_adder_ripple_carry #(.N(8)) u_add_high (
    .i_a      (a_high),
    .i_b      (b_high),
    .i_c      (carry_low),
    .ow_sum   (sum_high),
    .ow_carry (carry_high)
);

logic [15:0] sum_16 = {sum_high, sum_low};
```

### Simple ALU (Add/Subtract)

```systemverilog
logic [7:0] a, b, result;
logic sub;  // 1 = subtract, 0 = add
logic [7:0] b_mux;
logic carry_out;

// Two's complement subtraction: A - B = A + (~B) + 1
assign b_mux = sub ? ~b : b;

math_adder_ripple_carry #(.N(8)) u_alu (
    .i_a      (a),
    .i_b      (b_mux),
    .i_c      (sub),         // Carry in = 1 for subtraction
    .ow_sum   (result),
    .ow_carry (carry_out)
);
```

## Timing Characteristics

### Combinational Delay Analysis

| Width | Logic Levels | Typical Delay (ns) @ 1.0V | Max Frequency |
|-------|--------------|---------------------------|---------------|
| 2-bit | 4 | ~0.8 | ~1250 MHz |
| 4-bit | 8 | ~1.5 | ~650 MHz |
| 8-bit | 16 | ~3.0 | ~330 MHz |
| 16-bit | 32 | ~6.0 | ~165 MHz |
| 32-bit | 64 | ~12.0 | ~83 MHz |

**Logic Level Breakdown (8-bit example):**
- Carry chain: 8 full adders × 2 levels each = 16 levels
- Sum outputs: Available after carry arrives at each position

**Observation:** Delay doubles when width doubles (linear scaling).

### Critical Paths

**Longest Path (Carry Out):**
```
i_c → FA[0] → FA[1] → FA[2] → ... → FA[N-1] → ow_carry
2N gate delays
```

**Sum Output Paths (variable length):**
```
LSB (Sum[0]): i_a[0]/i_b[0] → 2 levels (fastest)
Mid (Sum[4]): Depends on C[3] → 10 levels (8-bit example)
MSB (Sum[7]): Depends on C[6] → 16 levels (slowest)
```

### Performance vs Width

| Width | Relative Delay | Relative Frequency |
|-------|---------------|-------------------|
| 4-bit | 1.0× | 1.00× |
| 8-bit | 2.0× | 0.50× |
| 16-bit | 4.0× | 0.25× |
| 32-bit | 8.0× | 0.125× |

**Why Linear Scaling is Bad:** For wide adders, delay becomes prohibitive. Consider faster architectures for N > 8.

## Performance Characteristics

### Resource Utilization

| Width | LUTs (Est.) | FFs (Pipeline) | Description |
|-------|-------------|----------------|-------------|
| 4-bit | ~8 | 0 (combinational) | Minimal |
| 8-bit | ~16 | 0 (combinational) | Small |
| 16-bit | ~32 | 0 (combinational) | Medium (consider alternatives) |
| 32-bit | ~64 | 0 (combinational) | Large (use faster adder) |

**Area Breakdown (8-bit):**
- 8 full adders: 8 × 2 gates = 16 LUTs (XOR + Carry logic)
- **Total**: ~16 LUTs (absolute minimum for 8-bit adder)

**Why It's Smallest:** No additional logic beyond full adders - just direct carry chain.

### Comparison: Area vs Speed

| Width | Ripple | CLA | Brent-Kung |
|-------|--------|-----|------------|
| **8-bit Area** | 16 | 24 | 60 |
| **8-bit Speed** | 1× | 1.7× | 4× |
| **Area Advantage** | Baseline | +50% | +275% |

## Design Considerations

### When to Use Ripple Carry Adder

✅ **Ideal Use Cases:**
- Width ≤ 8 bits
- Area is critical constraint
- Speed is not critical (< 100 MHz)
- Simple control logic
- Low-power designs (minimal gates = minimal switching)
- BCD arithmetic (4-bit digits)
- Small incrementers/decrementers

### When to Use Alternatives

**Use Carry Lookahead if:**
- 4 ≤ N ≤ 16
- Need moderate speed improvement
- Can afford 20-50% more area

**Use Brent-Kung if:**
- N = 8, 16, or 32
- Speed is critical
- Can afford 4× area

**Use Kogge-Stone if:**
- N ≥ 32
- Maximum speed required
- Area budget allows 6× increase

### Width Selection Trade-offs

| Application | Recommended Width | Rationale |
|-------------|------------------|-----------|
| Counter increment | 4-8 bits | Minimal area, adequate speed |
| BCD digit | 4 bits | Natural fit for BCD |
| Byte operations | 8 bits | Good balance |
| Word operations | 16 bits | Marginal - consider CLA |
| Double word | 32 bits | Too slow - use faster adder |

### Synthesis Considerations

**Optimization Tips:**

1. **Allow inference of fast carry chains**:
   ```tcl
   # Let tool map to dedicated carry logic
   set_dont_touch false
   ```

2. **Consider FPGA carry chains**:
   - Modern FPGAs have dedicated fast carry chains
   - Ripple carry maps well to these primitives
   - May achieve better performance than expected

3. **For ASIC, use standard cell library**:
   ```tcl
   # Use full adder cells from library
   set_dont_use [get_lib_cells */ADDF*] false
   ```

4. **Break long chains for high frequency**:
   ```systemverilog
   // Pipeline every 8 bits
   logic [7:0] r_sum_low, r_carry_mid;
   always_ff @(posedge clk) begin
       r_sum_low <= ow_sum[7:0];
       r_carry_mid <= w_c[7];
   end
   ```

## Verification Strategy

Test suite location: `val/common/test_math_adder_ripple_carry.py`

**Key Test Scenarios:**
- Random stimulus (all widths)
- Corner cases: 0+0, 0+MAX, MAX+MAX
- Full carry propagation: 0x00 + 0xFF (all carries ripple)
- Incrementer mode: A + 0 + 1
- Subtraction mode: A + (~B) + 1
- BCD operations (4-bit)

**Test Command:**
```bash
pytest val/common/test_math_adder_ripple_carry.py -v
```

## Common Pitfalls

❌ **Anti-Pattern 1**: Using for wide additions

```systemverilog
// WRONG: 64-bit ripple carry (extremely slow!)
math_adder_ripple_carry #(.N(64)) u_add (...);
// Result: 128 logic levels, ~25ns delay @ 1.0V!

// RIGHT: Use faster adder for wide operations
math_adder_brent_kung_032 u_add_low (...);   // Lower 32 bits
math_adder_brent_kung_032 u_add_high (...);  // Upper 32 bits
```

❌ **Anti-Pattern 2**: In critical timing paths

```systemverilog
// WRONG: Ripple adder in critical datapath
always_ff @(posedge clk) begin
    data_reg <= ripple_adder_output;  // May not meet timing!
end

// RIGHT: Use faster adder or pipeline
```

❌ **Anti-Pattern 3**: Ignoring FPGA carry chains

```systemverilog
// WRONG: Custom carry logic that doesn't infer carry chain
// (Defeats FPGA optimization)

// RIGHT: Use standard ripple carry structure
// Synthesis tools will map to fast carry primitives
```

❌ **Anti-Pattern 4**: Chaining multiple adders

```systemverilog
// WRONG: Cascading multiple ripple adders in one cycle
logic [7:0] sum1, sum2, sum3;
math_adder_ripple_carry #(.N(8)) u1 (.i_a(a), .i_b(b), .ow_sum(sum1), ...);
math_adder_ripple_carry #(.N(8)) u2 (.i_a(sum1), .i_b(c), .ow_sum(sum2), ...);
math_adder_ripple_carry #(.N(8)) u3 (.i_a(sum2), .i_b(d), .ow_sum(sum3), ...);
// 3 × 16 levels = 48 gate delays!

// RIGHT: Pipeline or use carry-save adder tree
```

## Related Modules

- **math_adder_full.sv** - Single-bit full adder building block
- **math_adder_half.sv** - Single-bit half adder (no carry input)
- **math_adder_full_nbit.sv** - Functionally equivalent to this module
- **math_adder_carry_lookahead.sv** - Faster alternative (1.5× speed, +20% area)
- **math_adder_brent_kung_*.sv** - Much faster (4× speed for 32-bit)

## References

- Mano, M.M. "Digital Design." Prentice Hall, 2002. (Chapter 4: Combinational Logic)
- Weste, N., Harris, D. "CMOS VLSI Design." Addison Wesley, 2010.
- Deschamps, J.P., Bioul, G., Sutter, G. "Synthesis of Arithmetic Circuits." Wiley, 2006.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
