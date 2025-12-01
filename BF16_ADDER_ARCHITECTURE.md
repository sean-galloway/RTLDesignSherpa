# BF16 Adder Architecture Specification

High-performance BF16 (Brain Float 16) floating-point adder with configurable pipeline stages, optimized for AI/ML inference and training workloads. This implementation targets 1.6GHz operation on TSMC 5nm with 34% timing margin in single-cycle mode, with optional pipeline stages for higher frequency operation.

## Overview

The BF16 adder implements IEEE-754-like floating-point addition/subtraction optimized for neural network operations. Unlike multiplication (which uses partial product reduction trees), floating-point addition requires operand alignment and normalization—making the architecture fundamentally different.

**Key Features:**
- **1.6GHz target frequency** on TSMC 5nm (conservative, 34% margin single-cycle)
- **4 independent pipeline stages** for frequency/latency tradeoff
- **Reuses existing modules**: `shifter_barrel`, `count_leading_zeros`
- **Behavioral arithmetic** for exponent/mantissa (no compressor trees needed)
- **Flush-to-Zero (FTZ)** for subnormal handling
- **Round-to-Nearest-Even (RNE)** rounding

**Why FP Addition is Different from Multiplication:**

| Aspect | FP Multiply | FP Add |
|--------|-------------|--------|
| Exponent operation | ADD (simple) | SUBTRACT + COMPARE |
| Mantissa operation | N×N multiply (partial products) | Align + Add/Sub (2 operands) |
| Normalization | 0-1 bit shift | 0 to N bit shift |
| Compressor trees | ✅ Required (Dadda) | ❌ Not needed |
| Generator scripts | High value | Low value |
| Critical components | Reduction tree | Barrel shifters + LZD |

**Architecture Components:**

| Module | Purpose | Critical Path |
|--------|---------|---------------|
| `math_bf16_adder` | Complete BF16 adder | ~410ps (single-cycle) |
| `shifter_barrel` | Mantissa alignment & normalization | ~80ps per instance |
| `count_leading_zeros` | Leading zero detection for normalization | ~40ps |

## BF16 Format Specification

BF16 (Brain Float 16) is a 16-bit floating-point format that truncates FP32:

```
BF16 Format (16 bits):
[15]     - Sign bit (1 bit)
[14:7]   - Exponent (8 bits, bias = 127)
[6:0]    - Mantissa (7 bits explicit, 1 bit implied)

Normalized value:    (-1)^sign × 2^(exp-127) × 1.mantissa
Represented range:   ~1.18e-38 to ~3.39e+38 (same as FP32)
Precision:           ~3 significant decimal digits
```

**Special Values:**

| Value | Sign | Exponent | Mantissa | Description |
|-------|------|----------|----------|-------------|
| +0 | 0 | 0x00 | 0x00 | Positive zero |
| -0 | 1 | 0x00 | 0x00 | Negative zero |
| +Inf | 0 | 0xFF | 0x00 | Positive infinity |
| -Inf | 1 | 0xFF | 0x00 | Negative infinity |
| NaN | X | 0xFF | != 0 | Not a Number |
| Subnormal | X | 0x00 | != 0 | Flushed to zero (FTZ) |

**Design Decisions (Industry Standard):**
- Subnormals flushed to zero (simplifies alignment logic)
- No signaling NaN propagation
- No IEEE exception flags
- Round-to-Nearest-Even (RNE) by default
- Sign of zero: x - x = +0 per IEEE 754 RNE rules

## Module Declaration

```systemverilog
module math_bf16_adder #(
    parameter int PIPE_STAGE_1 = 0,  // After exponent diff + swap
    parameter int PIPE_STAGE_2 = 0,  // After alignment shifter
    parameter int PIPE_STAGE_3 = 0,  // After mantissa add/sub
    parameter int PIPE_STAGE_4 = 0   // After normalize
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [15:0] i_a,            // BF16 operand A
    input  logic [15:0] i_b,            // BF16 operand B
    input  logic        i_valid,        // Input valid
    output logic [15:0] ow_result,      // BF16 sum/difference
    output logic        ow_overflow,    // Overflow to infinity
    output logic        ow_underflow,   // Underflow to zero
    output logic        ow_invalid,     // Invalid operation (NaN)
    output logic        ow_valid        // Output valid
);
```

**Pipeline Parameter Options:**

| Configuration | Latency | Target Frequency | Use Case |
|--------------|---------|------------------|----------|
| All 0 | 1 cycle | 1.6 GHz | Single-cycle, area-optimized |
| `PIPE_STAGE_2=1` | 2 cycles | 2.0+ GHz | Break after expensive shifter |
| `PIPE_STAGE_2=1, PIPE_STAGE_4=1` | 3 cycles | 2.5+ GHz | Balanced pipeline |
| All 1 | 5 cycles | 3.0+ GHz | Maximum frequency |

## Architecture Details

### Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           math_bf16_adder                                   │
│                                                                             │
│  ┌──────────────┐    ┌──────────────┐                                      │
│  │   BF16 A     │    │   BF16 B     │                                      │
│  │  [15:0]      │    │  [15:0]      │                                      │
│  └──────┬───────┘    └──────┬───────┘                                      │
│         │                   │                                               │
│  ═══════╪═══════════════════╪═══════════════════════════════════════════   │
│  STAGE A: Unpack + Compare + Swap                                           │
│  ═══════╪═══════════════════╪═══════════════════════════════════════════   │
│         │                   │                                               │
│         ▼                   ▼                                               │
│  ┌─────────────────────────────────────┐                                   │
│  │         Field Extraction            │                                   │
│  │   sign_a, exp_a[7:0], mant_a[6:0]  │                                   │
│  │   sign_b, exp_b[7:0], mant_b[6:0]  │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │      Special Case Detection         │                                   │
│  │   zero, subnormal, inf, NaN        │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │     Exponent Compare + Subtract     │                                   │
│  │   exp_diff = |exp_a - exp_b|        │                                   │
│  │   a_larger = (exp_a >= exp_b) &&    │                                   │
│  │              (mant_a >= mant_b)     │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │         Operand Swap                │                                   │
│  │   L = larger magnitude operand      │                                   │
│  │   S = smaller magnitude operand     │                                   │
│  │   eff_sub = sign_L XOR sign_S       │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│  ═══════════════╪═══════════════════════  PIPE_STAGE_1 (optional)          │
│                 │                                                           │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│  STAGE B: Mantissa Alignment                                                │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │      Mantissa Extension             │                                   │
│  │   mant_L_ext = {1, mant_L, 000}    │  (11 bits: 1.mmmmmmm GRS)         │
│  │   mant_S_ext = {1, mant_S, 000}    │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │      shifter_barrel (RIGHT)         │◄── exp_diff (shift amount)       │
│  │   mant_S_aligned = mant_S >> diff   │                                   │
│  │   + sticky bit capture              │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│  ═══════════════╪═══════════════════════  PIPE_STAGE_2 (optional)          │
│                 │                                                           │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│  STAGE C: Mantissa Add/Subtract                                             │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   Effective Operation Select        │                                   │
│  │   if (eff_sub)                      │                                   │
│  │       result = mant_L - mant_S      │                                   │
│  │   else                              │                                   │
│  │       result = mant_L + mant_S      │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   Overflow/Zero Detection           │                                   │
│  │   add_overflow = result[11]         │  (sum >= 2.0)                     │
│  │   sum_is_zero = (result == 0)       │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│  ═══════════════╪═══════════════════════  PIPE_STAGE_3 (optional)          │
│                 │                                                           │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│  STAGE D: Normalization                                                     │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   count_leading_zeros               │                                   │
│  │   (with bit reversal)               │                                   │
│  │   lzc = leading zeros in result     │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   Normalization Logic               │                                   │
│  │   if (add_overflow)                 │                                   │
│  │       shift RIGHT 1, exp++          │                                   │
│  │   else if (lzc > 1)                 │                                   │
│  │       shift LEFT (lzc-1), exp--     │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   shifter_barrel (LEFT or RIGHT)    │                                   │
│  │   mant_norm = shift(mant, amt)      │                                   │
│  │   exp_adj = exp_L ± shift_amt       │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│  ═══════════════╪═══════════════════════  PIPE_STAGE_4 (optional)          │
│                 │                                                           │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│  STAGE E: Round + Pack                                                      │
│  ═══════════════╪═══════════════════════════════════════════════════════   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   Round-to-Nearest-Even (RNE)       │                                   │
│  │   G = guard, R = round, S = sticky  │                                   │
│  │   round_up = G & (R | S | LSB)      │                                   │
│  │   mant_rounded = mant + round_up    │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   Special Case Mux                  │                                   │
│  │   Priority: NaN > Inf > Zero >      │                                   │
│  │             Overflow > Underflow    │                                   │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│  ┌─────────────────────────────────────┐                                   │
│  │   Result Assembly                   │                                   │
│  │   result = {sign, exp[7:0], mant[6:0]}                                  │
│  └──────────────┬──────────────────────┘                                   │
│                 │                                                           │
│                 ▼                                                           │
│            BF16 Result [15:0]                                               │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Floating-Point Addition Algorithm

The floating-point addition algorithm has fundamentally different structure from multiplication:

**Step 1: Unpack and Detect Special Cases**

```systemverilog
// Extract fields
wire       sign_a = i_a[15];
wire [7:0] exp_a  = i_a[14:7];
wire [6:0] mant_a = i_a[6:0];

// Special case detection
wire a_is_zero     = (exp_a == 8'h00) && (mant_a == 7'h00);
wire a_is_subnorm  = (exp_a == 8'h00) && (mant_a != 7'h00);  // → FTZ
wire a_is_inf      = (exp_a == 8'hFF) && (mant_a == 7'h00);
wire a_is_nan      = (exp_a == 8'hFF) && (mant_a != 7'h00);
wire a_is_normal   = ~a_is_zero && ~a_is_subnorm && ~a_is_inf && ~a_is_nan;
```

**Step 2: Compare Exponents and Swap Operands**

```
Why swap? We always want: |A| >= |B|

This ensures:
- Alignment shift is always RIGHT (simpler)
- Subtraction result is always positive (no sign correction)
- Result sign = sign of larger operand

Compare algorithm:
1. If exp_a > exp_b → A is larger
2. If exp_a < exp_b → B is larger  
3. If exp_a == exp_b → compare mantissas
```

```systemverilog
// Exponent difference
wire [8:0] exp_diff_raw = {1'b0, exp_a} - {1'b0, exp_b};
wire       a_larger = ~exp_diff_raw[8] && (~exp_equal || mant_a >= mant_b);

// Absolute difference for shift amount
wire [7:0] exp_diff = a_larger ? (exp_a - exp_b) : (exp_b - exp_a);

// Swap: L = larger, S = smaller
wire [7:0] exp_L  = a_larger ? exp_a  : exp_b;
wire [6:0] mant_L = a_larger ? mant_a : mant_b;
wire [6:0] mant_S = a_larger ? mant_b : mant_a;
```

**Step 3: Effective Operation**

```
The effective operation depends on the signs, not the opcode:

same signs     → effective ADD  (magnitudes add)
different signs → effective SUB  (magnitudes subtract)

Examples:
  (+5) + (+3) = +8   [same signs → ADD]
  (+5) + (-3) = +2   [diff signs → SUB]
  (-5) + (+3) = -2   [diff signs → SUB]
  (-5) + (-3) = -8   [same signs → ADD]
```

```systemverilog
wire eff_sub = sign_L ^ sign_S;  // 1 = subtract, 0 = add
```

**Step 4: Mantissa Alignment**

```
Before adding mantissas, they must represent the same power of 2.

Example: 1.5 × 2^5 + 1.25 × 2^3
        = 1.5 × 2^5 + 0.3125 × 2^5   (shift smaller right by exp_diff=2)
        = 1.8125 × 2^5

The alignment shift is: mant_S >> exp_diff

CRITICAL: Capture sticky bit (OR of all shifted-out bits) for rounding!
```

```systemverilog
// Extend mantissa with implied 1 and guard bits
// Format: {1, mant[6:0], G, R, S} = 11 bits
wire [10:0] mant_L_ext = {l_is_normal, mant_L, 3'b000};
wire [10:0] mant_S_ext = {s_is_normal, mant_S, 3'b000};

// Alignment using shifter_barrel
shifter_barrel #(.WIDTH(11)) u_align (
    .data(mant_S_ext),
    .ctrl(3'b001),        // Logical right shift
    .shift_amount(exp_diff),
    .data_out(mant_S_aligned)
);

// Sticky bit: OR of all bits shifted out
wire sticky = |(mant_S_ext & ((1 << exp_diff) - 1));
```

**Step 5: Mantissa Add/Subtract**

```systemverilog
// 12-bit result (extra bit for overflow)
logic [11:0] mant_sum;

if (eff_sub)
    mant_sum = {1'b0, mant_L_ext} - {1'b0, mant_S_aligned};
else
    mant_sum = {1'b0, mant_L_ext} + {1'b0, mant_S_aligned};

// Detect overflow (sum >= 2.0) or zero
wire add_overflow = mant_sum[11];
wire sum_is_zero  = (mant_sum == 0) && ~sticky;
```

**Step 6: Normalization**

```
After add/sub, the result may need normalization:

Addition overflow (bit[11] = 1):
  Result >= 2.0, need to shift RIGHT by 1, increment exponent
  Example: 1.5 + 1.5 = 11.0 (binary) → 1.1 × 2^1

Subtraction with cancellation (leading zeros):
  Result < 1.0, need to shift LEFT, decrement exponent
  Example: 1.5 - 1.25 = 0.25 = 0.01 (binary) → 1.0 × 2^-2
  
The leading zero count determines the left shift amount.
```

```systemverilog
// Leading zero count (note: CLZ module scans from bit[0], need reversal)
count_leading_zeros #(.WIDTH(12)) u_clz (
    .data(mant_reversed),  // Bit-reversed input
    .clz(lzc)
);

// Normalization decision
if (add_overflow) begin
    // Shift right 1, exp++
    mant_norm = mant_sum[11:1];
    exp_adj = exp_L + 1;
end else if (lzc > 1) begin
    // Shift left by (lzc-1), exp -= (lzc-1)
    mant_norm = mant_sum << (lzc - 1);
    exp_adj = exp_L - (lzc - 1);
end else begin
    // Already normalized
    mant_norm = mant_sum[10:0];
    exp_adj = exp_L;
end
```

**Step 7: Rounding (RNE)**

```
Round-to-Nearest-Even uses Guard, Round, and Sticky bits:

Mantissa format after normalization:
  [10]    = implied 1
  [9:3]   = 7-bit result mantissa
  [2]     = Guard bit (G)
  [1]     = Round bit (R)
  [0]     = part of Sticky (S includes shifted-out bits)

RNE rule: Round up if G && (R || S || LSB)
This rounds ties to even, preventing cumulative bias.
```

```systemverilog
wire guard  = mant_norm[2];
wire round  = mant_norm[1];
wire sticky = mant_norm[0] | sticky_from_shift;
wire lsb    = mant_norm[3];  // LSB of result mantissa

wire round_up = guard && (round || sticky || lsb);
wire [7:0] mant_rounded = {1'b0, mant_norm[9:3]} + {7'b0, round_up};

// Handle rounding overflow (0x7F + 1 = 0x80)
wire round_overflow = mant_rounded[7];
wire [6:0] mant_final = round_overflow ? 7'h00 : mant_rounded[6:0];
wire [7:0] exp_final = exp_adj + round_overflow;
```

### Special Case Handling

**Priority Order (highest to lowest):**

| Priority | Condition | Result |
|----------|-----------|--------|
| 1 | Either input is NaN | Quiet NaN (0x7FC0) |
| 2 | Inf - Inf (invalid) | Quiet NaN + invalid flag |
| 3 | Either input is Inf | Inf (with appropriate sign) |
| 4 | Both inputs zero | Zero (sign per IEEE rules) |
| 5 | One input zero | Other operand (pass-through) |
| 6 | Exact zero result | +0 (RNE mode) |
| 7 | Exponent overflow | Infinity + overflow flag |
| 8 | Exponent underflow | Zero + underflow flag (FTZ) |
| 9 | Normal result | Computed value |

**IEEE 754 Sign of Zero Rules:**

```
Addition:
  (+0) + (+0) = +0
  (-0) + (-0) = -0
  (+0) + (-0) = +0  (RNE mode)
  
Subtraction producing zero:
  x - x = +0  (RNE mode, regardless of x's sign)
```

### Timing Analysis (TSMC 5nm, 1.6GHz)

**Clock Period:** 625ps

**Single-Cycle Critical Path:**

| Stage | Component | Estimated Delay | Cumulative |
|-------|-----------|-----------------|------------|
| A1 | Unpack + special case | ~20ps | 20ps |
| A2 | Exponent subtract (8-bit) | ~40ps | 60ps |
| A3 | Compare + swap muxes | ~20ps | 80ps |
| B | **Barrel shifter (alignment)** | ~80ps | 160ps |
| C | Mantissa add/sub (12-bit) | ~50ps | 210ps |
| D1 | **CLZ (12-bit)** | ~40ps | 250ps |
| D2 | **Barrel shifter (normalize)** | ~80ps | 330ps |
| D3 | Exponent adjust | ~30ps | 360ps |
| E1 | Rounding logic | ~25ps | 385ps |
| E2 | Special case mux + pack | ~25ps | **410ps** |

**Margin:** 625ps - 410ps = 215ps (34%) ✓

**Critical Path:** Alignment Shifter → Add → CLZ → Normalize Shifter

**Pipelined Timing (with PIPE_STAGE_2 and PIPE_STAGE_4):**

| Stage | Delay | Clock Needed |
|-------|-------|--------------|
| Unpack + Compare + Align | ~160ps | 200ps (5GHz capable) |
| Add/Sub | ~50ps | 100ps |
| CLZ + Normalize | ~150ps | 200ps |
| Round + Pack | ~50ps | 100ps |

With 2 pipeline registers (PIPE_STAGE_2=1, PIPE_STAGE_4=1), the design can target **2.5GHz+**.

### Area Estimates

| Component | Gates (approx) | Area (5nm) |
|-----------|---------------|------------|
| Unpack + special case | ~80 | ~0.3 µm² |
| Exponent compare/subtract | ~60 | ~0.2 µm² |
| Operand swap muxes | ~120 | ~0.4 µm² |
| Barrel shifter (×2) | ~200 | ~0.8 µm² |
| Mantissa add/sub | ~80 | ~0.3 µm² |
| CLZ (12-bit) | ~60 | ~0.2 µm² |
| Rounding logic | ~40 | ~0.15 µm² |
| Special case mux | ~60 | ~0.2 µm² |
| Pipeline registers (all 4) | ~400 | ~1.5 µm² |
| **Total (no pipeline)** | **~700** | **~2.5 µm²** |
| **Total (full pipeline)** | **~1100** | **~4.0 µm²** |

**Comparison:**

| Module | Gates | Area | Notes |
|--------|-------|------|-------|
| BF16 Adder | ~700 | ~2.5 µm² | Comparable to multiplier |
| BF16 Multiplier | ~700 | ~2.5 µm² | Dadda tree dominant |
| BF16 FMA | ~2000 | ~7.0 µm² | Wide adder + CLZ |

## Usage Examples

### Basic BF16 Addition

```systemverilog
logic [15:0] a, b, result;
logic overflow, underflow, invalid, valid;

math_bf16_adder #(
    .PIPE_STAGE_1(0),
    .PIPE_STAGE_2(0),
    .PIPE_STAGE_3(0),
    .PIPE_STAGE_4(0)
) u_adder (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_a(a),
    .i_b(b),
    .i_valid(1'b1),
    .ow_result(result),
    .ow_overflow(overflow),
    .ow_underflow(underflow),
    .ow_invalid(invalid),
    .ow_valid(valid)
);

// Example: 1.5 + 2.5 = 4.0
// BF16(1.5) = 0x3FC0, BF16(2.5) = 0x4020, BF16(4.0) = 0x4080
initial begin
    a = 16'h3FC0;  // 1.5
    b = 16'h4020;  // 2.5
    #10;
    assert(result == 16'h4080);  // 4.0
end
```

### Pipelined High-Frequency Design

```systemverilog
// 2-stage pipeline for 2.5GHz operation
math_bf16_adder #(
    .PIPE_STAGE_1(0),
    .PIPE_STAGE_2(1),  // After alignment
    .PIPE_STAGE_3(0),
    .PIPE_STAGE_4(1)   // After normalization
) u_adder_fast (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_a(operand_a),
    .i_b(operand_b),
    .i_valid(input_valid),
    .ow_result(sum),
    .ow_overflow(ovf),
    .ow_underflow(udf),
    .ow_invalid(inv),
    .ow_valid(output_valid)  // 3 cycles after input_valid
);
```

### Subtraction (A - B)

```systemverilog
// BF16 subtraction: negate B's sign bit, then add
wire [15:0] b_negated = {~i_b[15], i_b[14:0]};

math_bf16_adder u_sub (
    .i_clk(clk),
    .i_rst_n(rst_n),
    .i_a(i_a),
    .i_b(b_negated),  // Flip sign for subtraction
    .i_valid(valid_in),
    .ow_result(difference),
    .ow_overflow(ovf),
    .ow_underflow(udf),
    .ow_invalid(inv),
    .ow_valid(valid_out)
);
```

### Neural Network Residual Connection

```systemverilog
module residual_add (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] activation,    // BF16 from layer
    input  logic [15:0] skip_input,    // BF16 skip connection
    input  logic        valid_in,
    output logic [15:0] residual_out,  // BF16 sum
    output logic        valid_out
);

    math_bf16_adder #(
        .PIPE_STAGE_1(0),
        .PIPE_STAGE_2(1),  // Pipeline for throughput
        .PIPE_STAGE_3(0),
        .PIPE_STAGE_4(0)
    ) u_residual (
        .i_clk(clk),
        .i_rst_n(rst_n),
        .i_a(activation),
        .i_b(skip_input),
        .i_valid(valid_in),
        .ow_result(residual_out),
        .ow_overflow(),      // Could log for debugging
        .ow_underflow(),
        .ow_invalid(),
        .ow_valid(valid_out)
    );

endmodule
```

### Vector Add Unit

```systemverilog
module bf16_vector_add #(
    parameter int VECTOR_WIDTH = 8
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] vec_a [VECTOR_WIDTH],
    input  logic [15:0] vec_b [VECTOR_WIDTH],
    input  logic        valid_in,
    output logic [15:0] vec_sum [VECTOR_WIDTH],
    output logic        valid_out
);

    logic [VECTOR_WIDTH-1:0] element_valid;

    genvar i;
    generate
        for (i = 0; i < VECTOR_WIDTH; i++) begin : gen_adders
            math_bf16_adder #(
                .PIPE_STAGE_1(0),
                .PIPE_STAGE_2(0),
                .PIPE_STAGE_3(0),
                .PIPE_STAGE_4(0)
            ) u_add (
                .i_clk(clk),
                .i_rst_n(rst_n),
                .i_a(vec_a[i]),
                .i_b(vec_b[i]),
                .i_valid(valid_in),
                .ow_result(vec_sum[i]),
                .ow_overflow(),
                .ow_underflow(),
                .ow_invalid(),
                .ow_valid(element_valid[i])
            );
        end
    endgenerate

    // All elements complete together (same pipeline depth)
    assign valid_out = element_valid[0];

endmodule
```

## Design Considerations

### Advantages

- **Flexible pipelining**: 4 independent stage controls for frequency/latency tuning
- **Reuses existing primitives**: `shifter_barrel`, `count_leading_zeros`
- **No generators needed**: Simple hand-written RTL (vs complex multiplier generators)
- **Industry-standard behavior**: FTZ, RNE, IEEE special case handling
- **Comparable complexity to multiplier**: ~700 gates vs ~700 for BF16 multiply

### Limitations

- **Inherent latency**: FP add has more stages than multiply (align → add → normalize)
- **Two barrel shifters**: Each ~80ps critical path
- **CLZ in critical path**: LZD adds ~40ps after mantissa operation
- **Not suitable for FMA integration**: FMA has its own wider addition path

### When to Use This Module

**Appropriate Use Cases:**
- Neural network residual connections (skip adds)
- Bias addition (though often folded into FMA)
- Element-wise vector addition
- Standalone add/subtract operations
- Any BF16 + BF16 → BF16 computation

**Consider Alternatives When:**
- Multiply-accumulate needed → Use `math_bf16_fma` instead
- Higher precision needed → Use FP32 addition
- Integer sufficient → Use fixed-point

### Comparison: Standalone Add vs FMA

| Aspect | `math_bf16_adder` | `math_bf16_fma` |
|--------|-------------------|-----------------|
| Operation | A + B | A × B + C |
| Mantissa width | 11-bit (8 + GRS) | 48-bit (product + FP32) |
| Adder type | Behavioral | Han-Carlson structural |
| Use case | Residuals, bias | Matrix multiply, dot product |
| Area | ~700 gates | ~2000 gates |

## Dependencies

**Required Existing Modules:**

```
math_bf16_adder
├── shifter_barrel.sv      (2 instances: align + normalize)
└── count_leading_zeros.sv (1 instance: normalization LZD)
```

**Module Interfaces:**

```systemverilog
// shifter_barrel
module shifter_barrel #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0]         data,
    input  logic [2:0]               ctrl,          // 001=right, 100=left
    input  logic [($clog2(WIDTH)):0] shift_amount,
    output logic [WIDTH-1:0]         data_out
);

// count_leading_zeros
module count_leading_zeros #(
    parameter int WIDTH         = 32,
    parameter     INSTANCE_NAME = "CLZ"
) (
    input  logic [WIDTH-1:0]      data,
    output logic [$clog2(WIDTH):0] clz
);
```

**Note on CLZ:** The `count_leading_zeros` module scans from bit[0], so the BF16 adder performs bit-reversal before calling it. This matches the pattern used in `math_bf16_fma`.

## Verification

### Test Categories

| Category | Description | Key Cases |
|----------|-------------|-----------|
| Basic | Simple adds/subs | 1.0 + 1.0, 2.0 - 1.0 |
| Alignment | Different exponents | Large + small, small + large |
| Cancellation | Near-equal subtraction | 1.0 - 0.999, precision loss |
| Overflow | Large + large | Max + max → Inf |
| Underflow | Tiny + tiny | Min + min → 0 (FTZ) |
| Special | NaN, Inf, Zero | NaN + x, Inf + Inf, 0 + 0 |
| Rounding | RNE edge cases | Ties round to even |
| Sign | Mixed signs | +a + -b, -a + +b |

### CocoTB Test Example

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
import struct

def float_to_bf16(f):
    """Convert float to BF16 (truncate FP32)"""
    fp32 = struct.pack('>f', f)
    return struct.unpack('>H', fp32[:2])[0]

def bf16_to_float(bf16):
    """Convert BF16 to float (extend to FP32)"""
    fp32_bytes = struct.pack('>H', bf16) + b'\x00\x00'
    return struct.unpack('>f', fp32_bytes)[0]

@cocotb.test()
async def test_basic_add(dut):
    """Test basic addition: 1.5 + 2.5 = 4.0"""
    dut.i_rst_n.value = 0
    await Timer(10, units='ns')
    dut.i_rst_n.value = 1
    
    dut.i_a.value = float_to_bf16(1.5)
    dut.i_b.value = float_to_bf16(2.5)
    dut.i_valid.value = 1
    
    await RisingEdge(dut.i_clk)
    await RisingEdge(dut.i_clk)
    
    result = bf16_to_float(dut.ow_result.value.integer)
    assert abs(result - 4.0) < 0.01, f"Expected 4.0, got {result}"

@cocotb.test()
async def test_subtraction_to_zero(dut):
    """Test x - x = +0"""
    dut.i_a.value = float_to_bf16(3.14159)
    dut.i_b.value = float_to_bf16(-3.14159)  # Negated for subtraction
    dut.i_valid.value = 1
    
    await RisingEdge(dut.i_clk)
    await RisingEdge(dut.i_clk)
    
    assert dut.ow_result.value == 0x0000, "x - x should be +0"
```

## Synthesis

```bash
# Lint check
verilator --lint-only --top-module math_bf16_adder \
    rtl/common/math_bf16_adder.sv \
    rtl/common/shifter_barrel.sv \
    rtl/common/count_leading_zeros.sv

# Synthesis (example with Yosys)
yosys -p "
    read_verilog -sv rtl/common/math_bf16_adder.sv
    read_verilog -sv rtl/common/shifter_barrel.sv
    read_verilog -sv rtl/common/count_leading_zeros.sv
    hierarchy -top math_bf16_adder
    proc; opt; fsm; opt; memory; opt
    techmap; opt
    stat
"
```

## References

### Floating-Point Addition Algorithm

- Patterson & Hennessy, "Computer Organization and Design" - FP arithmetic chapter
- Oberman & Flynn, "Design Issues in Division and Other Floating-Point Operations"
- IEEE 754-2019 Standard for Floating-Point Arithmetic

### BF16 Format

- Kalamkar, D. et al. "A Study of BFLOAT16 for Deep Learning Training." arXiv, 2019
- Google Brain Float specification
- Intel BFloat16 documentation

### Implementation

- Ercegovac & Lang, "Digital Arithmetic" - Chapters on FP addition
- Weste & Harris, "CMOS VLSI Design" - Arithmetic circuits

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-11-26 | Initial architecture specification |

## Navigation

- **[BF16 Multiplier Architecture](BF16_ARCHITECTURE.md)**
- **[RTL Common Documentation](docs/markdown/RTLCommon/index.md)**
- **[Back to Repository Root](README.md)**
