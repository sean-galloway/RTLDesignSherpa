# 4:2 Compressor

A 4:2 compressor (also called a 5:3 counter) that reduces 5 input bits to 3 output bits, providing faster column height reduction than traditional 3:2 compressors in multiplier trees.

## Overview

The `math_compressor_4to2` module implements a 4:2 compressor using two cascaded full adders. It accepts 4 primary inputs plus a carry-in, producing a sum, carry, and carry-out. The key advantage is that the carry-out (`ow_cout`) is independent of the carry-in (`i_cin`), enabling efficient chaining within multiplier reduction trees.

**Key Features:**
- **5 inputs to 3 outputs** - More efficient column reduction than 3:2 compressors
- **Cout independent of Cin** - Enables parallel carry chains
- **2 full adder depth** - Predictable timing
- **Building block** for Dadda/Wallace trees with 4:2 compressors

## Module Declaration

```systemverilog
module math_compressor_4to2 (
    input  logic i_x1, i_x2, i_x3, i_x4,
    input  logic i_cin,
    output logic ow_sum,
    output logic ow_carry,
    output logic ow_cout
);
```

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_x1 | Input | 1 | First input bit |
| i_x2 | Input | 1 | Second input bit |
| i_x3 | Input | 1 | Third input bit |
| i_x4 | Input | 1 | Fourth input bit |
| i_cin | Input | 1 | Carry input (from previous compressor) |
| ow_sum | Output | 1 | Sum output (same column weight) |
| ow_carry | Output | 1 | Carry output (weight = column + 1) |
| ow_cout | Output | 1 | Carry-out (weight = column + 1, independent of Cin) |

## Functionality

### Architecture

The 4:2 compressor is implemented as two cascaded full adders:

```
         i_x1 ─┐
               ├─ FA1 ─┬─ int_sum ─┐
         i_x2 ─┤       │           ├─ FA2 ─┬─ ow_sum
               │       │           │       │
         i_x3 ─┘       │     i_x4 ─┤       └─ ow_carry
                       │           │
                       └─ ow_cout  └─ i_cin
```

**Stage 1 (FA1):** Compresses X1, X2, X3
- Sum goes to Stage 2
- Carry becomes `ow_cout` (independent of i_cin!)

**Stage 2 (FA2):** Compresses int_sum, X4, Cin
- Sum becomes `ow_sum`
- Carry becomes `ow_carry`

### Truth Table (simplified)

The compressor performs: `i_x1 + i_x2 + i_x3 + i_x4 + i_cin = ow_sum + 2*(ow_carry + ow_cout)`

| Sum of inputs (0-5) | ow_cout | ow_carry | ow_sum |
|---------------------|---------|----------|--------|
| 0 | 0 | 0 | 0 |
| 1 | 0 | 0 | 1 |
| 2 | 0/1 | 0/1 | 0 |
| 3 | 0/1 | 0/1 | 1 |
| 4 | 1 | 1 | 0 |
| 5 | 1 | 1 | 1 |

**Note:** Multiple input combinations can produce the same sum, with different cout/carry distributions.

### Key Property: Cout Independence

The critical property of this implementation is that `ow_cout` depends only on X1, X2, X3 - not on i_cin:

```systemverilog
// First stage: cout is independent of cin
ow_cout = (i_x1 & i_x2) | (i_x2 & i_x3) | (i_x1 & i_x3);
```

This allows multiple 4:2 compressors to be chained with their cout signals forming independent carry chains, reducing the critical path compared to implementations where all carries depend on cin.

## Timing Characteristics

| Metric | Value | Description |
|--------|-------|-------------|
| Logic Depth | 4 gates | 2 full adders in series |
| Cin to Sum | 2 XOR gates | Through FA2 only |
| Cin to Carry | 1 XOR + 1 AND-OR | Through FA2 only |
| X1-X3 to Cout | 1 AND-OR | Through FA1 only |

**Critical Path:** X1/X2/X3 -> FA1 sum -> FA2 sum = 4 XOR gate delays

## Usage Examples

### Single Compressor

```systemverilog
logic x1, x2, x3, x4, cin;
logic sum, carry, cout;

math_compressor_4to2 u_comp (
    .i_x1(x1), .i_x2(x2), .i_x3(x3), .i_x4(x4),
    .i_cin(cin),
    .ow_sum(sum),
    .ow_carry(carry),
    .ow_cout(cout)
);
```

### Chained Compressors (Multiplier Column)

```systemverilog
// Reduce 8 bits in a column to 4 using two chained 4:2 compressors
logic [7:0] col_bits;
logic sum1, carry1, cout1;
logic sum2, carry2, cout2;

// First compressor: bits [3:0] + carry from previous column
math_compressor_4to2 u_comp1 (
    .i_x1(col_bits[0]), .i_x2(col_bits[1]),
    .i_x3(col_bits[2]), .i_x4(col_bits[3]),
    .i_cin(cin_from_prev),
    .ow_sum(sum1),
    .ow_carry(carry1),
    .ow_cout(cout1)
);

// Second compressor: bits [7:4] + cout from first compressor
math_compressor_4to2 u_comp2 (
    .i_x1(col_bits[4]), .i_x2(col_bits[5]),
    .i_x3(col_bits[6]), .i_x4(col_bits[7]),
    .i_cin(cout1),  // Chain cout to cin
    .ow_sum(sum2),
    .ow_carry(carry2),
    .ow_cout(cout2)
);

// Results: sum1, sum2 stay in this column
// carry1, carry2, cout2 go to next column
```

### In Dadda Tree Multiplier

```systemverilog
// Part of Dadda reduction stage
// Column has partial products: pp0, pp1, pp2, pp3, pp4
// Plus carry-in from previous column

math_compressor_4to2 u_dadda_comp (
    .i_x1(pp0), .i_x2(pp1), .i_x3(pp2), .i_x4(pp3),
    .i_cin(cin_prev),
    .ow_sum(reduced_sum),      // Stays in column
    .ow_carry(carry_to_next),  // Goes to column+1
    .ow_cout(cout_to_next)     // Goes to column+1
);

// pp4 passes through to next stage if column height allows
```

## Performance Characteristics

### Resource Utilization

| Metric | Value |
|--------|-------|
| Full Adders | 2 |
| Total Gates | ~10-12 (technology dependent) |
| LUTs (FPGA) | ~3-4 |

### Comparison with 3:2 Compressor (Full Adder)

| Metric | 3:2 Compressor | 4:2 Compressor |
|--------|----------------|----------------|
| Inputs | 3 | 5 |
| Outputs | 2 | 3 |
| Reduction ratio | 3:2 | 5:3 |
| Gate count | ~5 | ~10-12 |
| Logic depth | 2 | 4 |
| Column reduction | -1 per stage | -2 per stage |

**Advantage:** 4:2 compressors reduce column height faster, resulting in fewer reduction stages for multipliers.

### Design Optimization Priorities

This module is optimized with the following priorities:
1. **Area** - Minimal gate count using two full adders
2. **Wire complexity** - Simple cascaded structure with minimal routing
3. **Logic depth** - Fixed 2 full adder delays

## Design Considerations

### Advantages

- **Faster reduction** - Each compressor removes 2 bits from column height (vs 1 for 3:2)
- **Cin independence** - Cout doesn't depend on Cin, enabling parallel carry computation
- **Predictable timing** - Fixed 2 FA delay
- **Standard building block** - Well-understood for multiplier design

### Applications

- **Multiplier trees** - Dadda and Wallace trees with 4:2 compressors
- **Multi-operand adders** - Reducing many operands to 2
- **DSP blocks** - Custom multiply-accumulate units
- **BF16/FP16 arithmetic** - Mantissa multiplication

## Related Modules

- **math_adder_full** - Full adder building block (3:2 compressor)
- **math_adder_half** - Half adder building block
- **math_multiplier_dadda_4to2_008** - 8x8 multiplier using this compressor
- **math_adder_carry_save** - Alternative 3:2 compressor naming

## References

- Dadda, L. "Some Schemes for Parallel Multipliers." Alta Frequenza 34, 1965.
- Weinberger, A. "4:2 Carry-Save Adder Module." IBM Technical Disclosure Bulletin, 1981.
- Oklobdzija, V.G. et al. "A Method for Speed Optimized Partial Product Reduction and Generation of Fast Parallel Multipliers Using an Algorithmic Approach." IEEE Trans. Computers, 1996.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
