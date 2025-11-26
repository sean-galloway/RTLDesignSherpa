# BF16 RTL Generators

RTL generators for BF16 (Brain Float 16) arithmetic modules optimized for AI/ML accelerators.

## Overview

This package provides Python-based RTL generators that create synthesizable SystemVerilog modules for BF16 floating-point operations. The generated modules follow industry-standard practices used in TPUs and AI training accelerators.

### BF16 Format

```
BF16: [15]=sign, [14:7]=8-bit exponent (bias=127), [6:0]=7-bit mantissa
FP32: [31]=sign, [30:23]=8-bit exponent (bias=127), [22:0]=23-bit mantissa
```

BF16 is simply the upper 16 bits of FP32 - same exponent range, reduced mantissa precision. This makes BF16<->FP32 conversion trivial while providing sufficient dynamic range for neural network training.

## Generated Modules

| Module | Purpose | Description |
|--------|---------|-------------|
| `math_adder_han_carlson_016.sv` | 16-bit CPA | Han-Carlson prefix adder for multiplier final addition |
| `math_adder_han_carlson_048.sv` | 48-bit CPA | Han-Carlson prefix adder for FMA wide addition |
| `math_multiplier_dadda_4to2_008.sv` | 8x8 Multiplier | Dadda tree with 4:2 compressors for mantissa multiply |
| `math_bf16_mantissa_mult.sv` | Mantissa Multiplier | BF16 mantissa multiply with normalization detection |
| `math_bf16_exponent_adder.sv` | Exponent Adder | Exponent addition with bias handling and overflow detection |
| `math_bf16_multiplier.sv` | BF16 Multiplier | Complete BF16 multiplier with special case handling |
| `math_bf16_fma.sv` | BF16 FMA | Fused Multiply-Add with FP32 accumulator |

## Architecture

### Module Hierarchy

```
math_bf16_fma
├── math_multiplier_dadda_4to2_008 (mantissa multiply)
│   ├── math_compressor_4to2 (existing)
│   ├── math_adder_full (existing)
│   ├── math_adder_half (existing)
│   └── math_adder_han_carlson_016 (final CPA)
│       ├── math_prefix_cell (existing)
│       └── math_prefix_cell_gray (existing)
├── math_adder_han_carlson_048 (wide addition)
│   ├── math_prefix_cell (existing)
│   └── math_prefix_cell_gray (existing)
└── count_leading_zeros (existing, for normalization)

math_bf16_multiplier
├── math_bf16_mantissa_mult
│   └── math_multiplier_dadda_4to2_008
└── math_bf16_exponent_adder
```

### Dependency Order (bottom-up for synthesis)

1. `math_adder_half.sv` (existing)
2. `math_adder_full.sv` (existing)
3. `math_compressor_4to2.sv` (existing)
4. `math_prefix_cell.sv` (existing)
5. `math_prefix_cell_gray.sv` (existing)
6. `count_leading_zeros.sv` (existing)
7. `math_adder_han_carlson_016.sv`
8. `math_adder_han_carlson_048.sv`
9. `math_multiplier_dadda_4to2_008.sv`
10. `math_bf16_mantissa_mult.sv`
11. `math_bf16_exponent_adder.sv`
12. `math_bf16_multiplier.sv`
13. `math_bf16_fma.sv`

## Generator Files

### `han_carlson_adder.py`

Generates Han-Carlson prefix adders - a hybrid design combining properties of Kogge-Stone and Brent-Kung.

**Key Characteristics (16-bit):**
- 5 logic levels (vs 4 for Kogge-Stone)
- ~39 prefix cells (vs 64 for Kogge-Stone)
- Constant fanout of 2 (vs exponential for Sklansky)
- 4 wiring tracks (vs 8 for Kogge-Stone)

**Algorithm:**
1. **Stage 0**: Initial P/G computation (P = A XOR B, G = A AND B)
2. **Stage 1**: Span-2 prefix on even positions (combine adjacent pairs)
3. **Stages 2-N-1**: Kogge-Stone style on even positions (doubling span each stage)
4. **Stage N**: Fill odd positions from even neighbors

**Usage:**
```python
from rtl_generators.bf16.han_carlson_adder import generate_han_carlson_adder
generate_han_carlson_adder(width=16, output_path='rtl/common')
```

### `dadda_4to2_multiplier.py`

Generates Dadda reduction tree multipliers using 4:2 compressors instead of traditional 3:2 CSA cells.

**Key Characteristics (8x8):**
- 3 reduction stages (vs 4 with 3:2 CSA)
- ~18 4:2 compressors
- Critical path: 9 XOR delays (3 per stage)

**Algorithm:**
1. Generate 64 partial products (8x8 AND gate array)
2. Dadda reduction stages targeting heights: 6 -> 4 -> 3 -> 2
3. Final CPA using Han-Carlson adder

**Dadda Height Sequence:** 2, 3, 4, 6, 9, 13, 19, 28, ...

Each stage reduces column height to the next smaller Dadda number. 4:2 compressors reduce 5 inputs to 2 outputs, enabling faster height reduction than 3:2 CSAs.

**Usage:**
```python
from rtl_generators.bf16.dadda_4to2_multiplier import generate_dadda_4to2_multiplier
generate_dadda_4to2_multiplier(width=8, output_path='rtl/common')
```

### `bf16_mantissa_mult.py`

Generates BF16 mantissa multiplier wrapper that extends 7-bit mantissa with implied leading 1 and handles normalization.

**Features:**
- 8x8 unsigned multiply (7-bit explicit + 1 implied bit)
- Normalization detection (product >= 2.0)
- Guard, round, sticky bits for RNE rounding

**Mantissa Extension:**
```
Normalized: {1, mantissa[6:0]} = 8-bit value [1.0, 2.0)
Subnormal/Zero: {0, mantissa[6:0]} = treated as zero (FTZ mode)
```

**Product Format:**
- If MSB=1: `1x.xxxxxx_xxxxxxxx` -> needs normalization (right shift + exp++)
- If MSB=0: `01.xxxxxx_xxxxxxxx` -> already normalized

**Usage:**
```python
from rtl_generators.bf16.bf16_mantissa_mult import generate_bf16_mantissa_mult
generate_bf16_mantissa_mult(output_path='rtl/common')
```

### `bf16_exponent_adder.py`

Generates BF16 exponent adder with bias handling and overflow/underflow detection.

**Features:**
- 10-bit intermediate for overflow/underflow detection
- Bias subtraction: `exp_result = exp_a + exp_b - 127 + norm_adjust`
- Special case detection (zero, infinity, NaN indicators)

**Overflow/Underflow Logic:**
```
Underflow: result <= 0 (signed comparison via MSB check)
Overflow: result > 254 (255 reserved for inf/NaN)
```

**Usage:**
```python
from rtl_generators.bf16.bf16_exponent_adder import generate_bf16_exponent_adder
generate_bf16_exponent_adder(output_path='rtl/common')
```

### `bf16_multiplier.py`

Generates complete BF16 multiplier integrating mantissa and exponent paths.

**Architecture:**
1. Extract sign, exponent, mantissa from BF16 operands
2. Detect special cases (zero, subnormal, infinity, NaN)
3. Compute sign (XOR of input signs)
4. Multiply mantissas using Dadda 4:2 tree
5. Add exponents with bias subtraction
6. Apply Round-to-Nearest-Even (RNE) rounding
7. Handle special cases (propagate NaN, 0*inf=NaN, etc.)

**Special Case Priority:**
1. NaN propagation (any NaN input -> NaN output)
2. Invalid operation (0 * inf = NaN)
3. Infinity result (either input is inf)
4. Zero result (either input is zero/subnormal)
5. Overflow (exponent > 254)
6. Underflow (exponent < 1)
7. Normal result

**Usage:**
```python
from rtl_generators.bf16.bf16_multiplier import generate_bf16_multiplier
generate_bf16_multiplier(output_path='rtl/common')
```

### `bf16_fma.py`

Generates BF16 Fused Multiply-Add with FP32 accumulator - the standard approach for AI training.

**Operation:** `result = (a * b) + c` where a,b are BF16 and c,result are FP32

**Architecture:**
1. BF16 multiplication (8x8 mantissa)
2. Extend product to FP32 precision (24-bit mantissa with implied 1)
3. Align addend with product based on exponent difference
4. 48-bit wide addition using Han-Carlson structural adder
5. Leading zero count for normalization
6. RNE rounding to FP32

**Key Design Decisions:**
- **48-bit internal precision**: Captures all significant bits from both operands
- **Structural adder**: Uses Han-Carlson adder instead of behavioral `+` for timing predictability
- **Two's complement subtraction**: Invert + carry-in for effective subtraction
- **Bit reversal for CLZ**: The `count_leading_zeros` module counts trailing zeros, so input is bit-reversed

**Special Case Priority (fixed in FMA):**
1. NaN/Invalid (highest priority)
2. Infinity cases
3. Zero operand pass-through (BEFORE overflow/underflow!)
4. Exact zero result (returns +0 per IEEE 754 RNE)
5. Overflow
6. Underflow
7. Normal result

**Usage:**
```python
from rtl_generators.bf16.bf16_fma import generate_bf16_fma
generate_bf16_fma(output_path='rtl/common')
```

## Usage

### Generate All Modules

```bash
# From repository root
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common
```

### Generate Individual Modules

```bash
# Han-Carlson adder (16-bit)
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/han_carlson_adder.py 16 rtl/common

# Han-Carlson adder (48-bit)
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/han_carlson_adder.py 48 rtl/common

# Dadda multiplier (8-bit)
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/dadda_4to2_multiplier.py 8 rtl/common

# BF16 mantissa multiplier
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/bf16_mantissa_mult.py rtl/common

# BF16 exponent adder
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/bf16_exponent_adder.py rtl/common

# Complete BF16 multiplier
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/bf16_multiplier.py rtl/common

# BF16 FMA
PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/bf16_fma.py rtl/common
```

### Python API

```python
from rtl_generators.bf16 import (
    HanCarlsonAdder,
    Dadda4to2Multiplier,
    BF16MantissaMult,
    BF16ExponentAdder,
    BF16Multiplier,
    BF16FMA
)

# Using convenience functions
from rtl_generators.bf16.han_carlson_adder import generate_han_carlson_adder
from rtl_generators.bf16.dadda_4to2_multiplier import generate_dadda_4to2_multiplier
from rtl_generators.bf16.bf16_mantissa_mult import generate_bf16_mantissa_mult
from rtl_generators.bf16.bf16_exponent_adder import generate_bf16_exponent_adder
from rtl_generators.bf16.bf16_multiplier import generate_bf16_multiplier
from rtl_generators.bf16.bf16_fma import generate_bf16_fma
```

## Verification

Tests are located in `val/common/`:

```bash
# Run all BF16 tests
cd val/common
make run-bf16

# Run with different test levels
make run-bf16-gate    # Quick smoke tests
make run-bf16-func    # Default functional tests
make run-bf16-full    # Comprehensive tests

# Run individual tests
PYTHONPATH=bin:$PYTHONPATH WAVES=0 SIM=verilator pytest test_math_bf16_multiplier.py -v
PYTHONPATH=bin:$PYTHONPATH WAVES=0 SIM=verilator pytest test_math_bf16_fma.py -v
PYTHONPATH=bin:$PYTHONPATH WAVES=0 SIM=verilator pytest test_math_bf16_fma_systematic.py -v
```

### Test Files

| Test | Description | Test Cases |
|------|-------------|------------|
| `test_math_bf16_exponent_adder.py` | Exponent adder unit test | Special values, overflow/underflow |
| `test_math_bf16_mantissa_mult.py` | Mantissa multiplier unit test | Normalization, rounding bits |
| `test_math_bf16_multiplier.py` | Complete multiplier test | 86+ parameterized cases |
| `test_math_bf16_fma.py` | FMA functional test | Special values, accumulation, random |
| `test_math_bf16_fma_systematic.py` | Systematic edge case test | 25,137 power-of-2 boundary cases |

## IEEE 754 Compliance Notes

### Flush-To-Zero (FTZ) Mode

Subnormal numbers are treated as zero. This is standard practice for BF16 in AI accelerators:
- Simplifies hardware (no denormalized number handling)
- Minimal impact on neural network accuracy
- Matches GPU tensor core behavior

### Round-to-Nearest-Even (RNE)

All rounding uses IEEE 754 round-to-nearest-even:
```
Round up if: guard_bit AND (round_bit OR sticky_bit OR lsb)
```
This ensures ties round to even, preventing cumulative rounding bias.

### Sign of Zero

Per IEEE 754, when the result is exactly zero in RNE mode, the sign is positive:
- `1.0 - 1.0 = +0` (not -0)
- `0 * anything = +0` (unless both operands negative, then -0)

### Product Exponent Underflow

When multiplying two very small numbers, the product exponent can underflow:
```
exp_result = exp_a + exp_b - bias
```
If this goes negative, the product is effectively zero. The FMA handles this by using signed arithmetic for exponent calculations and detecting the underflow condition before overflow checks.

## Design References

- **Han-Carlson Adder**: "A Fast Parallel Adder Based on Parallel Prefix Computation" (Han & Carlson, 1982)
- **Dadda Multiplier**: "Some Schemes for Parallel Multipliers" (Dadda, 1965)
- **4:2 Compressors**: "Fast Multipliers" by Weiner & Weste
- **BF16 Format**: Google Brain Float specification (identical to FP32 truncated to 16 bits)

## File Structure

```
bin/rtl_generators/bf16/
├── __init__.py              # Package exports
├── README.md                # This file
├── rtl_header.py            # Standard RTL header generator
├── generate_all.py          # Master generation script
├── han_carlson_adder.py     # Han-Carlson prefix adder generator
├── dadda_4to2_multiplier.py # Dadda 4:2 multiplier generator
├── bf16_mantissa_mult.py    # BF16 mantissa multiplier generator
├── bf16_exponent_adder.py   # BF16 exponent adder generator
├── bf16_multiplier.py       # Complete BF16 multiplier generator
└── bf16_fma.py              # BF16 FMA generator
```

## Version History

- **2025-11-24**: Initial release with multiplier and FMA
- **2025-11-25**: Fixed FMA bugs (zero product priority, rounding overflow, sign of zero, product underflow)

## Author

Sean Galloway (RTL Design Sherpa project)
