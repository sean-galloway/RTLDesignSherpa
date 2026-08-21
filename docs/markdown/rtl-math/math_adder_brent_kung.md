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

# Brent-Kung Parallel Prefix Adder

A family of parallel prefix adders built on the Brent-Kung algorithm — O(log N) depth without the Kogge-Stone area bill, thanks to an asymmetric tree and area-efficient gray cells.

## Overview

The `math_adder_brent_kung` module family implements the Brent-Kung parallel prefix addition algorithm, which achieves O(log N) critical path depth while minimizing hardware area compared to other parallel prefix adders like Kogge-Stone. The trick is the asymmetric tree: a forward tree computes intermediate results, then a reverse tree fills in the carries using area-efficient "gray" cells that only propagate generate signals.

Available widths: **8-bit**, **16-bit**, **32-bit**, **64-bit**

### Module Hierarchy

**Top-Level Modules (User-Facing):**
- `math_adder_brent_kung_008.sv` - 8-bit adder
- `math_adder_brent_kung_016.sv` - 16-bit adder
- `math_adder_brent_kung_032.sv` - 32-bit adder
- `math_adder_brent_kung_064.sv` - 64-bit adder (used as the final CPA of the 32-bit Dadda and Wallace multipliers)

**Internal Building Blocks:**
- `math_adder_brent_kung_pg.sv` - Single-bit P/G generator
- `math_adder_brent_kung_black.sv` - Black cell (outputs P and G)
- `math_adder_brent_kung_gray.sv` - Gray cell (outputs only G, area-efficient)
- `math_adder_brent_kung_bitwisepg.sv` - Bitwise P/G logic stage
- `math_adder_brent_kung_grouppg_008/016/032/064.sv` - Width-specific prefix networks
- `math_adder_brent_kung_sum.sv` - Final sum calculation

### Module Declaration

```systemverilog
module math_adder_brent_kung_032 #(
    parameter int N = 32     // Adder width in bits
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic         i_c,       // Carry input
    output logic [N-1:0] ow_sum,    // Sum output
    output logic         ow_carry   // Carry output
);
```

**Note:** Replace `_032` with `_008`, `_016` or `_064` for the 8-, 16- or 64-bit version. All four share this port list; only `N` and the internal prefix network change.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 32 | Adder width in bits (8, 16, 32 or 64) |

**Width Options:**
- **8-bit**: Set N=8 in `math_adder_brent_kung_008`
- **16-bit**: Set N=16 in `math_adder_brent_kung_016`
- **32-bit**: Set N=32 in `math_adder_brent_kung_032`
- **64-bit**: Set N=64 in `math_adder_brent_kung_064`

**Why Fixed Widths?** The parallel prefix network structure is width-specific and optimized for each size during design. Generic parameterization would require runtime generation of the tree structure — not something a parameter can express.

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | N | Operand A (addend) |
| i_b | Input | N | Operand B (addend) |
| i_c | Input | 1 | Carry input (0 for addition, 1 for +1 increment) |
| ow_sum | Output | N | Sum output (A + B + Cin) |
| ow_carry | Output | 1 | Carry output (overflow) |

## Functional Description

### Parallel Prefix Addition Theory

Parallel prefix adders compute all carries in parallel using **propagate (P)** and **generate (G)** signals:

**Bit-Level Definitions:**
- **Generate**: G_i = A_i & B_i (carry generated at position i)
- **Propagate**: P_i = A_i ^ B_i (carry propagated through position i)
- **Sum**: S_i = P_i ^ C_i (sum bit given incoming carry)

**Group-Level Recurrence:**
- **G[i:j]** = G[i:k] | (P[i:k] & G[k-1:j]) (group generate)
- **P[i:j]** = P[i:k] & P[k-1:j] (group propagate)

### Brent-Kung Algorithm Stages

The Brent-Kung adder executes in three stages:

#### Stage 1: Bitwise P/G Generation
```
For each bit i:
  P[i] = A[i] ^ B[i]
  G[i] = A[i] & B[i]
```

**Hardware**: Array of AND/XOR gates (1 level of logic)

#### Stage 2: Parallel Prefix Network (Forward + Reverse Trees)
```
Forward Tree (log2(N) - 1 levels, black cells):
  Build binary tree upward using black cells
  Compute group P/G for increasing spans: [1:0], [3:2], [7:4], etc.

Reverse Tree (log2(N)-1 levels):
  Propagate group G downward using gray cells
  Fill in missing intermediate positions
```

**Hardware**: Network of black cells (forward) and gray cells (reverse)

**Key Optimization**: Gray cells only compute G (not P), saving ~30% area vs Kogge-Stone

#### Stage 3: Final Sum Calculation
```
For each bit i:
  Sum[i] = P[i] ^ G[i-1]  (XOR with incoming carry)

Carry_out = G[N-1]  (final group generate)
```

**Hardware**: Array of XOR gates (1 level of logic)

### Three-Stage Pipeline

The top-level module instantiates three sub-modules:

```systemverilog
// Stage 1: Generate bitwise P and G signals
math_adder_brent_kung_bitwisepg #(.N(N)) BitwisePGLogic_inst (
    .i_a (i_a),
    .i_b (i_b),
    .i_c (i_c),
    .ow_g(ow_g),  // Generate signals [N:0]
    .ow_p(ow_p)   // Propagate signals [N:0]
);

// Stage 2: Parallel prefix network (forward + reverse trees)
math_adder_brent_kung_grouppg_032 #(.N(N)) GroupPGLogic_inst (
    .i_g  (ow_g),
    .i_p  (ow_p),
    .ow_gg(ow_gg),  // Group generate [N:0]
    .ow_pp()        // Unused (gray cells only compute G)
);

// Stage 3: Compute final sum
math_adder_brent_kung_sum #(.N(N)) SumLogic_inst (
    .i_p      (ow_p),
    .i_gg     (ow_gg),
    .ow_sum   (ow_sum),
    .ow_carry (ow_carry)
);
```

### Internal Building Blocks

#### PG Cell (`math_adder_brent_kung_pg`)
```systemverilog
// Single-bit P/G generator
assign ow_g = i_a & i_b;  // Generate
assign ow_p = i_a ^ i_b;  // Propagate
```

**Usage**: Initial stage to create bit-level P/G signals

#### Black Cell (`math_adder_brent_kung_black`)
```systemverilog
// Combines two P/G pairs, outputs both
assign ow_g = i_g | (i_p & i_g_km1);  // Group generate
assign ow_p = i_p & i_p_km1;          // Group propagate
```

**Usage**: Forward tree (needs both P and G for further propagation)

**Logic Depth**: 2 gates (1 AND + 1 OR/AND)

#### Gray Cell (`math_adder_brent_kung_gray`)
```systemverilog
// Combines two P/G pairs, outputs only G (area-efficient)
assign ow_g = i_g | (i_p & i_g_km1);  // Group generate
// No P output (saves one AND gate per cell)
```

**Usage**: Reverse tree (only needs G, not P)

**Area Savings**: ~33% fewer gates vs black cell

**Logic Depth**: 2 gates (1 AND + 1 OR)

### Prefix Network Structure (32-bit Example)

```
Depth 0 (Bitwise):  P0 G0  P1 G1  P2 G2  P3 G3  ...  P31 G31

Depth 1 (Forward):  [1:0]g  [3:2]  [5:4]  [7:6] ... [31:30]      (15 black + 1 gray;
                                                                  [1:0] is GRAY -- bit 1's
                                                                  final prefix needs no P)

Depth 2 (Forward):  [3:0]g  [7:4]  [11:8]  [15:12] ... [31:28]   (7 black + 1 gray)

Depth 3 (Forward):  [7:0]g  [15:8]  [23:16]  [31:24]             (3 black + 1 gray)

Depth 4 (Forward):  [15:0]g  [31:16]                             (1 black + 1 gray)

Depth 5 (Root):     [31:0]g                                      (gray -- the root
                                                                  needs no P output)

Depth 6+ (Reverse fill): gray cells complete the remaining
prefixes ([2:0], [4:0], [5:0], [6:0], ...) by combining each
bit's own (g,p) with the nearest completed prefix below it

Depth 8 (Reverse):  deepest gap-fill (e.g. [30:29])            (Gray cells)

Depth 9 (Sum):      S0    S1    S2    S3    ...    S31         (XOR gates)
```

**Key Features:**
- **Forward tree**: log2(N) - 1 levels; these are the levels that contain black cells
- **Reverse tree**: log2(N) - 1 further levels, gray cells only
- **Prefix-network depth**: 2 x log2(N) - 2 cell levels
- **Total depth**: 2 x log2(N) cell levels, adding the bitwise PG stage and the sum XOR stage
- **Black cells**: Used in the forward tree (outputs both P and G)
- **Gray cells**: Used where only G is needed further (outputs only G, saves area); the reverse tree — including the [31:0] root — is gray-only. The RTL confirms: the root instantiates `math_adder_brent_kung_gray`, not a black cell

Measured from the generated prefix networks (`math_adder_brent_kung_grouppg_*.sv`):

| Width | Prefix levels | Total levels | Black cells | Gray cells |
|-------|---------------|--------------|-------------|------------|
| 8-bit | 4 | 6 | 4 | 8 |
| 16-bit | 6 | 8 | 11 | 16 |
| 32-bit | 8 | 10 | 26 | 32 |
| 64-bit | 10 | 12 | 57 | 64 |

: Brent-Kung prefix network depth and cell counts, counted from the RTL

Black cells follow `N - log2(N) - 1` and gray cells `N`. Don't take my word for
it — count them yourself with
`grep -c math_adder_brent_kung_black rtl/math/math_adder_brent_kung_grouppg_032.sv`.

## Timing

### Combinational Delay Analysis

Logic levels below are cell levels counted from the RTL. The delay and frequency
columns are rough estimates only — no synthesis run backs them, and they will
move substantially with technology, constraints and effort level.

| Width | Logic Levels | Est. Delay (ns) | Est. Max Frequency |
|-------|--------------|-----------------|--------------------|
| 8-bit | 6 | ~2.0 | ~500 MHz |
| 16-bit | 8 | ~2.5 | ~400 MHz |
| 32-bit | 10 | ~3.0 | ~333 MHz |
| 64-bit | 12 | ~3.5 | ~285 MHz |

: Brent-Kung timing, logic levels measured and delays estimated

**Logic Level Breakdown (32-bit):**
1. Bitwise PG: 1 level (AND/XOR)
2. Forward tree: 4 levels (levels containing black cells)
3. Reverse tree: 4 levels (gray cells only)
4. Sum calculation: 1 level (XOR)
5. **Total**: 10 levels

**Comparison to Other Adders:**

| Adder Type | Logic Depth | Area | Best Use Case |
|------------|-------------|------|---------------|
| Ripple Carry | O(N) | Minimal | Low-speed, area-critical |
| Carry Lookahead | O(log N) | Medium | Moderate speed |
| **Brent-Kung** | **O(log N)** | **Medium** | **Balanced speed/area** |
| Kogge-Stone | O(log N) | Maximum | Maximum speed (datapath) |

### Critical Paths

1. **Forward Tree Path**: i_a/i_b -> PG -> black cells (prefix levels 1-4) -> Group G
2. **Reverse Tree Path**: Group G -> gray cells (prefix levels 5-8) -> Final G
3. **Sum Path**: Final G → XOR with P → ow_sum

**Optimization Tip**: Pipeline between stages for >1 GHz operation:
```systemverilog
// Pipeline registers (example for 2-stage pipeline)
logic [N-1:0] r_p_stage1, r_g_stage1;
logic [N-1:0] r_sum;

always_ff @(posedge clk) begin
    // Stage 1: PG generation + first half of prefix tree
    r_p_stage1 <= ow_p;
    r_g_stage1 <= partial_gg;  // Intermediate prefix result

    // Stage 2: Second half of prefix tree + sum
    r_sum <= ow_sum;
end
```

## Usage Example

### Basic 32-bit Addition

```systemverilog
logic [31:0] a, b, sum;
logic carry_out;

math_adder_brent_kung_032 #(
    .N(32)
) u_adder (
    .i_a      (a),
    .i_b      (b),
    .i_c      (1'b0),        // No carry input
    .ow_sum   (sum),
    .ow_carry (carry_out)
);

// Example: 123 + 456
initial begin
    a = 32'd123;
    b = 32'd456;
    #1;  // Wait for combinational propagation
    assert(sum == 32'd579);
end
```

### 8-bit Incrementer

```systemverilog
logic [7:0] count, count_plus_1;

math_adder_brent_kung_008 #(
    .N(8)
) u_incrementer (
    .i_a      (count),
    .i_b      (8'b0),        // B = 0
    .i_c      (1'b1),        // Carry in = 1 → +1 increment
    .ow_sum   (count_plus_1),
    .ow_carry ()             // Unused
);
```

### 16-bit Subtraction (A - B)

```systemverilog
logic [15:0] a, b, difference;
logic borrow;

// Subtraction: A - B = A + (~B) + 1 (two's complement)
math_adder_brent_kung_016 #(
    .N(16)
) u_subtractor (
    .i_a      (a),
    .i_b      (~b),          // Invert B
    .i_c      (1'b1),        // Carry in = 1 (for two's complement)
    .ow_sum   (difference),
    .ow_carry (borrow)       // Borrow = ~carry_out
);

// Example: 1000 - 300
initial begin
    a = 16'd1000;
    b = 16'd300;
    #1;
    assert(difference == 16'd700);
end
```

### Multi-Precision Addition (64-bit via 2×32-bit)

```systemverilog
logic [31:0] a_low, a_high, b_low, b_high;
logic [31:0] sum_low, sum_high;
logic carry_low, carry_high;

// Low 32 bits
math_adder_brent_kung_032 u_add_low (
    .i_a      (a_low),
    .i_b      (b_low),
    .i_c      (1'b0),
    .ow_sum   (sum_low),
    .ow_carry (carry_low)
);

// High 32 bits (chain carry from low)
math_adder_brent_kung_032 u_add_high (
    .i_a      (a_high),
    .i_b      (b_high),
    .i_c      (carry_low),     // Carry from low adder
    .ow_sum   (sum_high),
    .ow_carry (carry_high)
);

// Concatenate results
logic [63:0] sum_64 = {sum_high, sum_low};
```

### Overflow Detection (Signed Addition)

```systemverilog
logic [31:0] a_signed, b_signed, sum_signed;
logic overflow;

math_adder_brent_kung_032 u_signed_add (
    .i_a      (a_signed),
    .i_b      (b_signed),
    .i_c      (1'b0),
    .ow_sum   (sum_signed),
    .ow_carry ()
);

// Overflow detection for signed addition
// Overflow = (A[31] == B[31]) && (Sum[31] != A[31])
assign overflow = (a_signed[31] == b_signed[31]) &&
                  (sum_signed[31] != a_signed[31]);

// Example: Detect overflow
initial begin
    // Max positive + positive = overflow
    a_signed = 32'h7FFFFFFF;  // +2,147,483,647
    b_signed = 32'h00000001;  // +1
    #1;
    assert(overflow == 1'b1);  // Result wraps to negative
end
```

## Design Notes

### Width Selection

**Available Widths:**
- **8-bit**: Suitable for byte operations, small arithmetic units
- **16-bit**: Common for ALU slices, address arithmetic
- **32-bit**: Standard integer width, general-purpose ALU
- **64-bit**: Wide datapaths and product-width CPAs; this is the final adder inside the 32-bit Dadda and Wallace multipliers

**For Non-Standard Widths:**
- Extend inputs with zeros: `{24'b0, a[7:0]}` for 8-bit in 32-bit adder
- Truncate outputs: `sum_32[15:0]` for 16-bit result
- Or use ripple carry / carry lookahead for custom widths

### Synthesis Considerations

**Optimization Tips:**
1. **Flatten hierarchy** for best optimization:
   ```tcl
   set_flatten true -effort high
   ```

2. **Pipeline for high frequency**:
   - Break at forward/reverse tree boundary
   - Break at prefix network / sum calculation boundary

3. **Critical path optimization**:
   ```tcl
   set_max_delay -from [get_ports i_a] -to [get_ports ow_sum] 3.0
   ```

4. **Area optimization** (if needed):
   - Consider carry lookahead instead (smaller but still fast)
   - Share adders using time-division multiplexing

### Performance

Cell counts below are exact (counted from the RTL); the LUT figures are estimates
derived from them, not synthesis results.

| Width | Black cells | Gray cells | LUTs (Est.) | FFs (Pipeline) |
|-------|-------------|------------|-------------|----------------|
| 8-bit | 4 | 8 | ~45 | 0 (combinational) |
| 16-bit | 11 | 16 | ~100 | 0 (combinational) |
| 32-bit | 26 | 32 | ~240 | 0 (combinational) |
| 64-bit | 57 | 64 | ~510 | 0 (combinational) |

: Brent-Kung area, cell counts measured and LUTs estimated

**Area Breakdown (32-bit):**
- Bitwise PG: 32 x 2 gates = 64 LUTs
- Black cells: 26 cells x 3 gates = 78 LUTs
- Gray cells: 32 cells x 2 gates = 64 LUTs
- Sum logic: 32 x 1 gate = 32 LUTs
- **Total**: ~238 LUTs

**Comparison (32-bit, estimated):**
- **Ripple Carry**: ~32 LUTs (32 full adders)
- **Brent-Kung**: ~240 LUTs (balanced)
- **Kogge-Stone**: ~450 LUTs (maximum speed, maximum area)

**Speed vs Area Trade-offs:**

| Adder Architecture | Relative Speed | Relative Area | Logic Depth |
|-------------------|----------------|---------------|-------------|
| Ripple Carry | 1.0× (slowest) | 1.0× (smallest) | O(N) |
| Carry Lookahead | 4.0× | 3.0× | O(log N) |
| **Brent-Kung** | **6.0×** | **4.5×** | **O(log N)** |
| Kogge-Stone | 8.0× (fastest) | 7.0× (largest) | O(log N) |

**When to Use Brent-Kung:**
- **Balanced designs**: Need good speed without excessive area
- **Mid-range frequency**: 200-500 MHz targets
- **FPGA implementations**: LUT utilization matters
- **Multiple adders**: Area budget shared across many units

**When to Use Alternatives:**
- Use **Ripple Carry** for: Low-speed, area-critical (e.g., control logic)
- Use **Kogge-Stone** for: Critical datapath, maximum performance (e.g., FPU)

### Common Pitfalls

**Anti-Pattern 1**: Using wrong width variant

```systemverilog
// WRONG: Trying to parameterize to 24-bit
math_adder_brent_kung_032 #(.N(24)) u_add (...);
// Result: Mismatch with grouppg_032 network (designed for 32-bit)

// RIGHT: Use 32-bit, ignore upper bits
math_adder_brent_kung_032 #(.N(32)) u_add (
    .i_a({8'b0, a[23:0]}),  // Zero-extend
    .i_b({8'b0, b[23:0]}),
    .ow_sum(sum_32),
    ...
);
logic [23:0] sum = sum_32[23:0];  // Truncate
```

**Anti-Pattern 2**: Ignoring carry output for signed arithmetic

```systemverilog
// WRONG: Using carry for signed overflow
logic [31:0] a_signed, b_signed, sum;
logic overflow;

math_adder_brent_kung_032 u_add (...);
assign overflow = ow_carry;  // INCORRECT for signed!

// RIGHT: Check sign bits
assign overflow = (a_signed[31] == b_signed[31]) &&
                  (sum[31] != a_signed[31]);
```

**Anti-Pattern 3**: Expecting registered outputs

```systemverilog
// WRONG: Assuming outputs are registered
always_ff @(posedge clk) begin
    result <= ow_sum;  // ow_sum is combinational!
end

// RIGHT: Add explicit output register
logic [31:0] r_sum;
always_ff @(posedge clk) begin
    r_sum <= ow_sum;
end
```

**Anti-Pattern 4**: Chaining without considering timing

```systemverilog
// WRONG: Long chain of adders in one cycle
logic [31:0] a, b, c, d, result;
logic [31:0] ab_sum, abc_sum;

math_adder_brent_kung_032 u_add1 (.i_a(a), .i_b(b), .ow_sum(ab_sum), ...);
math_adder_brent_kung_032 u_add2 (.i_a(ab_sum), .i_b(c), .ow_sum(abc_sum), ...);
math_adder_brent_kung_032 u_add3 (.i_a(abc_sum), .i_b(d), .ow_sum(result), ...);

// 3 × 3ns = 9ns path!  May not close timing at high frequency

// RIGHT: Pipeline the chain
logic [31:0] r_ab_sum, r_abc_sum;
always_ff @(posedge clk) begin
    r_ab_sum <= ab_sum;
    r_abc_sum <= abc_sum;
end
```

## Related Modules

- **math_adder_pg_chain.sv** - Medium-speed adder (less area)
- **math_adder_ripple_carry.sv** - Minimal area adder (slow)
- **math_adder_carry_save_nbit.sv** - For multi-operand addition (multipliers)
- **math_subtractor_*.sv** - Subtraction variants (uses two's complement)

## Testing

From the test suite (`val/math/test_math_adder_brent_kung.py`) — one parameterized
test covering every width, not one file per width.

**Key Test Scenarios:**
- Exhaustive testing (8-bit only)
- Random stimulus (16/32-bit)
- Corner cases: 0+0, 0+MAX, MAX+MAX
- Carry propagation: All 1's + 1
- Signed overflow detection
- Multi-precision chaining

**Test Command:**
```bash
# Test all widths the test sweeps (REG_LEVEL selects the width list)
pytest val/math/test_math_adder_brent_kung.py -v

# A single width
pytest "val/math/test_math_adder_brent_kung.py::test_math_adder_brent_kung[32]" -v
```

The width sweep is driven by `REG_LEVEL`: `FUNC` (the default) covers 8 and 16
bits, `FULL` covers 8, 16 and 32. The 64-bit variant is exercised indirectly,
as the final CPA of the 32-bit Dadda and Wallace multiplier tests, rather than
by a direct adder test.

Run levels come from the standard grid: `REG_LEVEL=GATE|FUNC|FULL` selects the
parameter set, `TEST_LEVEL` the per-test depth. Run the whole area with
`make -C val/math run-all-func-parallel`, never bare pytest for suites.

## References

- Brent, R.P., Kung, H.T. "A Regular Layout for Parallel Adders." IEEE Transactions on Computers, 1982.
- Harris, D. "A Taxonomy of Parallel Prefix Networks." Asilomar Conference, 2003.
- Deschamps, J.P., Bioul, G., Sutter, G. "Synthesis of Arithmetic Circuits: FPGA, ASIC and Embedded Systems." Wiley, 2006.

## Navigation

- [Back to Math Index](index.md)
- [Back to Main Documentation Index](../index.md)
