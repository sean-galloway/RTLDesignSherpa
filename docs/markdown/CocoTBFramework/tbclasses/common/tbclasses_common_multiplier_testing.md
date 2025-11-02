# Multiplier Testing Module Documentation

## Overview

The `MultiplierTB` class provides comprehensive testing for digital multiplier implementations. It validates multiplication operations across various architectures including array multipliers, Booth multipliers, and Wallace tree multipliers with specialized test patterns for each architecture type.

## Purpose and Use Cases

### When to Use MultiplierTB
- Testing integer multiplier circuits of various architectures
- Verifying Booth algorithm implementations (radix-2, radix-4)
- Validating Wallace tree and Dadda multiplier designs
- Testing signed and unsigned multiplication
- Ensuring proper partial product generation and accumulation

### Multiplier Fundamentals
Digital multiplication generates a product from two operands:
- **Product Width**: Typically 2×N bits for N-bit operands
- **Partial Products**: Intermediate results in multiplication algorithm
- **Booth Encoding**: Signed multiplication optimization technique
- **Carry Propagation**: Final addition of partial products

## Configuration

### Environment Variables
- `PARAM_N`: Bit width of multiplier operands (default: 8)
- `TEST_LEVEL`: Test intensity - simple/basic/booth/medium/full (default: basic)
- `SEED`: Random number generator seed (default: 12345)
- `DUT`: Device under test identifier

### Expected DUT Interface

```verilog
module multiplier #(
    parameter N = 8
) (
    // Operands
    input  [N-1:0]     i_multiplier,    // First operand
    input  [N-1:0]     i_multiplicand,  // Second operand
    
    // Result
    output [2*N-1:0]   ow_product       // Product output
);
```

## Test Methodologies

### 1. Main Loop Testing (`main_loop`)
**Purpose**: Comprehensive multiplication validation

**Test Strategy**:
- **Exhaustive Testing**: For small bit widths (N ≤ 4)
- **Statistical Sampling**: For larger bit widths with random test vectors
- **Product Verification**: `product = multiplier × multiplicand`

```python
async def main_loop(self, count=256):
    if self.max_val * self.max_val < count:
        # Exhaustive testing for small parameter spaces
        test_all_combinations()
    else:
        # Random sampling for large parameter spaces
        random_sampling(count)
    
    for a, b in test_vectors:
        # Apply inputs
        self.dut.i_multiplier.value = a
        self.dut.i_multiplicand.value = b
        
        # Wait for combinational logic
        await self.wait_time(1, 'ns')
        
        # Verify result
        expected = (a * b) & (2**(2*N) - 1)
        actual = int(self.dut.ow_product.value)
        assert actual == expected
```

### 2. Booth Algorithm Testing (`booth_specific_test`)
**Purpose**: Specialized testing for Booth multiplier implementations

**Booth Radix-4 Encoding**:
```
Booth Group | Operation
000, 111    | +0
001, 010    | +A  
011         | +2A
100         | -2A
101, 110    | -A
```

**Test Patterns**:
```python
# Booth-specific test cases
booth_patterns = [
    (5, 7),              # Simple case with different booth groups
    (4, 15),             # Tests +2A encoding
    (pattern_01, pattern_10),  # Alternating bit patterns
    (max_positive, max_positive),  # Boundary conditions
    (min_negative, min_negative),  # Sign extension tests
]

# Booth group analysis for debugging
for i in range(num_groups):
    booth_group = extract_booth_group(multiplier, i)
    operation = decode_booth_operation(booth_group)
    verify_partial_product(operation, multiplicand, i)
```

### 3. Corner Cases Testing (`corner_cases_test`)
**Purpose**: Test boundary conditions and special values

**Corner Case Patterns**:
```python
corner_cases = [
    0,                  # Zero
    1,                  # One  
    max_val,            # All ones
    max_val // 2,       # 01111...
    max_val // 2 + 1,   # 10000...
    0xA,                # 1010 pattern
    0x5,                # 0101 pattern
]

# Add powers of 2
corner_cases.extend(1 << i for i in range(N))

# Test all combinations
for a in corner_cases:
    for b in corner_cases:
        verify_multiplication(a, b)
```

### 4. Walking Ones Test (`walking_ones_test`)
**Purpose**: Test with systematic bit patterns

**Pattern**: Single bit walking through all positions
```python
for pos_a in range(N):
    for pos_b in range(N):
        a = 1 << pos_a
        b = 1 << pos_b
        expected_product = 1 << (pos_a + pos_b)
        verify_multiplication(a, b, expected_product)
```

### 5. Alternating Pattern Test (`alternating_pattern_test`)
**Purpose**: Test adjacent bit interactions

**Patterns**:
- `pattern1`: 0101_0101... (alternating 01)
- `pattern2`: 1010_1010... (alternating 10)

### 6. Special Patterns Test (`special_patterns_test`)
**Purpose**: Architecture-specific test patterns

**Booth-Specific Patterns**:
```python
booth_special = [
    (0x2, 0x2),     # 2×2, simple multiplication
    (0x3, 0x3),     # 3×3, testing +1 -1 sequence  
    (0x7, 0x7),     # 7×7, testing multiple +1 patterns
    (0x5, 0x5),     # 5×5, testing +1 0 -1 sequence
    (0xA, 0xA),     # 10×10, testing -1 +1 sequence
    (0x55, 0xAA),   # Alternating 01/10 patterns
    (0x33, 0xCC),   # Alternating 00/11 patterns
]
```

## Implementation Examples

### Basic Multiplier Test
```python
import cocotb
from CocoTBFramework.tbclasses.common.multiplier_testing import MultiplierTB

@cocotb.test()
async def test_multiplier_basic(dut):
    """Basic multiplier functionality test"""
    tb = MultiplierTB(dut)
    tb.print_settings()
    await tb.run_comprehensive_tests()

@cocotb.test()
async def test_simple_case(dut):
    """Test the specific case that often fails: 5×7=35"""
    tb = MultiplierTB(dut)
    await tb.simple_test()
```

### Booth Multiplier Specific Test
```python
@cocotb.test()
async def test_booth_multiplier(dut):
    """Specialized testing for Booth multiplier"""
    tb = MultiplierTB(dut)
    
    # Set test level to focus on Booth patterns
    tb.test_level = 'booth'
    
    # Run Booth-specific tests
    await tb.booth_specific_simple_test()
    await tb.booth_specific_test()
    
    tb.log.info(f"Booth multiplier test complete: {tb.pass_count}/{tb.test_count} passed")

@cocotb.test()
async def test_booth_signed_multiplication(dut):
    """Test signed multiplication using Booth algorithm"""
    tb = MultiplierTB(dut)
    
    # Test signed multiplication cases
    signed_test_cases = [
        (5, 7),      # Positive × Positive
        (5, -3),     # Positive × Negative  
        (-5, 7),     # Negative × Positive
        (-5, -3),    # Negative × Negative
        (0, -1),     # Zero × Negative
        (-1, -1),    # (-1) × (-1) = 1
    ]
    
    for a_signed, b_signed in signed_test_cases:
        # Convert to N-bit 2's complement
        a = a_signed & tb.mask
        b = b_signed & tb.mask
        
        tb.dut.i_multiplier.value = a
        tb.dut.i_multiplicand.value = b
        await tb.wait_time(1, 'ns')
        
        actual_product = int(tb.dut.ow_product.value)
        expected_product = (a_signed * b_signed) & (2**(2*tb.N) - 1)
        
        assert actual_product == expected_product, \
            f"Signed multiplication failed: {a_signed}×{b_signed} = {expected_product}, got {actual_product}"
```

### Performance Analysis Test
```python
@cocotb.test()
async def test_multiplier_patterns(dut):
    """Test specific multiplication patterns"""
    tb = MultiplierTB(dut)
    
    # Test power-of-2 multiplications (should be shifts)
    powers_of_2 = [1, 2, 4, 8, 16, 32, 64, 128]
    
    for power in powers_of_2:
        if power < tb.max_val:
            for test_val in [1, 3, 5, 7, 15, 31]:
                if test_val < tb.max_val:
                    tb.dut.i_multiplier.value = test_val
                    tb.dut.i_multiplicand.value = power
                    await tb.wait_time(1, 'ns')
                    
                    expected = (test_val * power) & (2**(2*tb.N) - 1)
                    actual = int(tb.dut.ow_product.value)
                    
                    assert actual == expected, \
                        f"Power-of-2 multiplication failed: {test_val}×{power}"
    
    tb.log.info("Power-of-2 multiplication tests passed")

@cocotb.test()
async def test_multiplier_comprehensive(dut):
    """Comprehensive multiplier testing with all patterns"""
    tb = MultiplierTB(dut)
    
    await tb.clear_interface()
    
    # Run all test patterns
    failures = []
    failures.extend(await tb.simple_test())
    failures.extend(await tb.corner_cases_test())
    failures.extend(await tb.walking_ones_test())
    failures.extend(await tb.alternating_pattern_test())
    failures.extend(await tb.special_patterns_test())
    
    # If Booth multiplier, run Booth-specific tests
    if "booth" in tb.dut_type.lower():
        failures.extend(await tb.booth_specific_test())
    
    # Report results
    if failures:
        tb.log.error(f"Found {len(failures)} failures in comprehensive test")
        for i, failure in enumerate(failures[:5]):  # Show first 5 failures
            tb.log.error(f"Failure {i+1}: {failure}")
    else:
        tb.log.info("All comprehensive tests passed!")
```

## Test Levels

### Simple Level
- **Focus**: Single test case (5×7=35)
- **Purpose**: Quick functionality check
- **Duration**: Seconds

### Basic Level  
- **Test Count**: min(64, 2^N) test vectors
- **Includes**: Simple test + main loop + corner cases
- **Duration**: Fast, suitable for continuous integration

### Booth Level
- **Focus**: Booth algorithm specific patterns only
- **Includes**: Booth-specific simple and comprehensive tests
- **Purpose**: Targeted Booth multiplier validation

### Medium Level
- **Test Count**: min(128, 2^N) test vectors  
- **Includes**: Basic + walking ones + corner cases
- **Duration**: Moderate, good for regular validation

### Full Level
- **Test Count**: min(256, 2^N) test vectors
- **Includes**: All test patterns (main, corner, walking, alternating, special)
- **Duration**: Comprehensive, suitable for final verification

## Algorithm-Specific Considerations

### Array Multipliers
- **Partial Product Matrix**: Systematic generation of all partial products
- **Carry Propagation**: Proper addition tree implementation
- **Critical Path**: Longest combinational delay

### Booth Multipliers
- **Encoding Groups**: Proper 3-bit group formation and decoding
- **Sign Extension**: Correct handling of negative numbers
- **Partial Product Signs**: Proper negation and complement generation

### Wallace Tree Multipliers  
- **Reduction Stages**: Correct 3:2 and 2:1 compressor implementation
- **Tree Balance**: Optimal delay through reduction levels
- **Final Addition**: Carry-propagate adder for final sum

### Dadda Multipliers
- **Height Reduction**: Optimal reduction sequence
- **Compressor Efficiency**: Minimal logic complexity
- **Regular Structure**: Systematic layout for VLSI implementation

## Error Analysis

### Common Failure Patterns

#### 1. Booth Algorithm Errors
```
Booth specific test failed:
  Input: multiplier=5 (0x5), multiplicand=7 (0x7)
  Expected: product=35 (0x23)
  Actual: product=34 (0x22)
  
  Booth groups analysis:
    Group 0: bits=101 (value=5) => operation: -A
    Group 1: bits=010 (value=2) => operation: +A
    Group 2: bits=000 (value=0) => operation: 0
  
  Debug: Check partial product generation for Group 0
```

#### 2. Partial Product Errors
```
Test failed: 5×235=1175, got 1174
  Analyzing partial products:
    Bit position 0: Expected 1, Got 0
    Partial product a[0] & b[0] = 1
  
  Debug: Check least significant bit handling
```

#### 3. Carry Propagation Issues
```
Walking ones test failed:
  Input: multiplier=0b00001000, multiplicand=0b00000100
  Expected: product=0b0000000000100000
  Actual: product=0b0000000000010000
  
  Debug: Check carry chain between bit positions 4 and 5
```

### Debug Strategies

#### 1. Start Simple
```python
# Begin with the simplest case
@cocotb.test()
async def debug_simple(dut):
    tb = MultiplierTB(dut)
    # Test 1×1=1 first
    dut.i_multiplier.value = 1
    dut.i_multiplicand.value = 1
    await tb.wait_time(1, 'ns')
    assert dut.ow_product.value == 1
```

#### 2. Binary Analysis
```python
def analyze_failure(self, a, b, expected, actual):
    """Detailed binary analysis of multiplication failure"""
    self.log.error("Binary analysis:")
    self.log.error(f"  a = {bin(a)[2:].zfill(self.N)}")
    self.log.error(f"  b = {bin(b)[2:].zfill(self.N)}")
    self.log.error(f"  expected = {bin(expected)[2:].zfill(2*self.N)}")
    self.log.error(f"  actual   = {bin(actual)[2:].zfill(2*self.N)}")
    
    # Find first differing bit
    for i in range(2*self.N):
        if ((expected >> i) & 1) != ((actual >> i) & 1):
            self.log.error(f"  First difference at bit {i}")
            break
```

#### 3. Incremental Testing
```python
# Test incrementally increasing complexity
test_sequence = [
    (1, 1),    # Identity
    (1, 2),    # Simple shift
    (2, 2),    # Power of 2
    (3, 3),    # Adjacent bits
    (5, 7),    # Common failure case
]
```

## Performance Optimization

### Test Vector Selection
```python
# Automatic complexity scaling
if self.N <= 4:
    # Exhaustive for very small multipliers
    test_all_combinations()
elif self.N <= 8:
    # Representative sampling
    stratified_sampling()
else:
    # Statistical sampling only
    random_sampling()
```

### Failure Analysis Optimization
```python
# Stop after multiple failures in same pattern
if failure_count > 10 and all_same_pattern(failures):
    self.log.error("Systematic failure detected, stopping test")
    return failures[:10]  # Return sample of failures
```

## Troubleshooting Guide

### 1. Interface Issues
- **Signal Names**: Verify `i_multiplier`, `i_multiplicand`, `ow_product`
- **Bit Widths**: Confirm N-bit inputs, 2N-bit output
- **Timing**: Ensure adequate settling time for combinational logic

### 2. Algorithm Issues  
- **Booth Encoding**: Verify 3-bit group formation and decoding
- **Sign Extension**: Check proper handling of MSB for signed multiplication
- **Partial Products**: Validate individual partial product generation

### 3. Environment Setup
```bash
# Example configuration for 8-bit multiplier
export PARAM_N=8
export TEST_LEVEL=medium
export SEED=42
export DUT=booth_multiplier_8bit
```

This module provides comprehensive validation of multiplier implementations, ensuring correct arithmetic operations across various architectures with specialized testing for algorithm-specific characteristics like Booth encoding and partial product generation.