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

# Subtractor Testing Module Documentation

## Overview

The `SubtractorTB` class provides comprehensive testing for digital subtractor implementations. It validates subtraction operations across various architectures including full subtractors, half subtractors, and borrow-propagating designs with systematic test patterns for accurate difference and borrow calculations.

## Purpose and Use Cases

### When to Use SubtractorTB
- Testing combinational subtractor circuits (ripple borrow, look-ahead borrow)
- Verifying half subtractor implementations  
- Validating full subtractor with borrow input/output
- Ensuring proper borrow propagation across bit widths
- Testing signed and unsigned subtraction operations

### Subtractor Fundamentals
Digital subtraction produces a difference and borrow:
- **Difference**: Result of minuend - subtrahend - borrow_in
- **Borrow Output**: Indicates when subtraction requires borrowing
- **Relationship**: minuend = difference + (subtrahend + borrow_in) + (borrow_out × 2^N)
- **Borrow Propagation**: Borrow chain through multiple bit positions

## Configuration

### Environment Variables
- `PARAM_N`: Bit width of the subtractor operands (default: 1)
- `TEST_LEVEL`: Test intensity - basic/medium/full (default: basic)
- `SEED`: Random number generator seed (default: 12345)
- `DUT`: Device under test identifier

### Expected DUT Interface

#### Full Subtractor Interface
```verilog
module full_subtractor #(parameter N = 8) (
    input  [N-1:0] i_a,            // Minuend
    input  [N-1:0] i_b,            // Subtrahend
    input          i_borrow_in,    // Borrow input (or i_b_in)
    output [N-1:0] ow_difference,  // Difference output (or ow_d)
    output         ow_carry_out    // Borrow output (or ow_b)
);
```

#### Half Subtractor Interface
```verilog
module half_subtractor (
    input  i_a,        // Minuend
    input  i_b,        // Subtrahend
    output o_d,        // Difference output (or ow_d)
    output o_b         // Borrow output (or ow_b)
);
```

## Test Methodologies

### 1. Main Loop Testing (`main_loop`)
**Purpose**: Comprehensive testing of standard subtraction operations

**Test Strategy**:
- **Small parameter spaces**: Exhaustive testing of all possible input combinations
- **Large parameter spaces**: Statistical sampling with random test vectors
- **Verification**: `a - b - borrow_in = difference + (borrow_out × 2^N)`

**Borrow Logic**:
```python
# For subtraction: a - b - borrow_in
expected_difference = (a - b - borrow_in) & mask
expected_borrow = int(a < (b + borrow_in))  # 1 if borrowing needed
```

**Test Vectors**:
```python
# For N-bit subtractors
total_combinations = 2^N × 2^N × 2  # a_values × b_values × borrow_values

# Generate test patterns
if max_val < count:
    # Exhaustive testing
    a_list = list(range(max_val))
    b_list = list(range(max_val))
else:
    # Random sampling
    a_list = [random.randint(0, mask) for _ in range(count)]
    b_list = [random.randint(0, mask) for _ in range(count)]

borrow_list = [0, 1]  # Test both borrow input conditions
```

### 2. Half Subtractor Testing (`half_subtractor_test`)
**Purpose**: Specific validation for half subtractor implementations

**Truth Table**:
| a | b | Difference | Borrow |
|---|---|------------|--------|
| 0 | 0 | 0          | 0      |
| 0 | 1 | 1          | 1      |
| 1 | 0 | 1          | 0      |
| 1 | 1 | 0          | 0      |

**Implementation**:
```python
async def half_subtractor_test(self):
    expected_results = {
        (0, 0): (0, 0),  # 0 - 0 = 0, no borrow
        (0, 1): (1, 1),  # 0 - 1 = -1 → 1 with borrow
        (1, 0): (1, 0),  # 1 - 0 = 1, no borrow
        (1, 1): (0, 0)   # 1 - 1 = 0, no borrow
    }
    
    for inputs, expected_output in expected_results.items():
        self.dut.i_a.value = inputs[0]
        self.dut.i_b.value = inputs[1]
        await Timer(1, units='ns')
        
        actual_output = (int(self.dut.o_d.value), int(self.dut.o_b.value))
        assert actual_output == expected_output
```

### 3. Walking Ones Test (`walking_ones_test`)
**Purpose**: Test borrow propagation with systematic bit patterns

**Pattern**: Single bit set to 1, walking through all positions
```python
# Test with a as walking ones, b=0
for pos in range(N):
    a = 1 << pos
    b = 0
    for borrow_in in [0, 1]:
        expected_difference = (a - b - borrow_in) & mask
        expected_borrow = int(a < (b + borrow_in))
        verify_subtraction(a, b, borrow_in, expected_difference, expected_borrow)

# Test with b as walking ones, a=max_val (all bits set)
for pos in range(N):
    a = mask  # All bits set
    b = 1 << pos
    for borrow_in in [0, 1]:
        expected_difference = (a - b - borrow_in) & mask
        expected_borrow = int(a < (b + borrow_in))
        verify_subtraction(a, b, borrow_in, expected_difference, expected_borrow)
```

### 4. Alternating Pattern Test (`alternating_pattern_test`)
**Purpose**: Test for adjacent bit interactions in borrow chains

**Patterns**:
- `pattern1`: 0101_0101... (alternating 01)
- `pattern2`: 1010_1010... (alternating 10)

**Test Implementation**:
```python
# Create alternating patterns
pattern1 = 0  # Will be 0101...
pattern2 = 0  # Will be 1010...

for i in range(N):
    if i % 2 == 0:
        pattern1 |= (1 << i)
    else:
        pattern2 |= (1 << i)

# Test all combinations with different borrow inputs
for a, b, borrow_in in itertools.product([pattern1, pattern2], [pattern1, pattern2], [0, 1]):
    verify_subtraction(a, b, borrow_in)
```

## Implementation Examples

### Basic Subtractor Test
```python
import cocotb
from CocoTBFramework.tbclasses.common.subtractor_testing import SubtractorTB

@cocotb.test()
async def test_full_subtractor(dut):
    """Test a full subtractor implementation"""
    tb = SubtractorTB(dut)
    tb.print_settings()
    await tb.run_comprehensive_tests()

@cocotb.test()
async def test_half_subtractor(dut):
    """Test a half subtractor implementation"""
    tb = SubtractorTB(dut)
    await tb.half_subtractor_test()
```

### Advanced Subtractor Testing
```python
@cocotb.test()
async def test_subtractor_comprehensive(dut):
    """Comprehensive subtractor testing with custom patterns"""
    tb = SubtractorTB(dut)
    
    tb.print_settings()
    await tb.clear_interface()
    
    # Test individual components
    await tb.main_loop(count=1000)
    await tb.walking_ones_test()
    await tb.alternating_pattern_test()
    
    # Test specific edge cases
    edge_cases = [
        (0, 0, 0),        # Zero - zero
        (0, 1, 0),        # Underflow case
        (255, 0, 0),      # Max - zero
        (255, 255, 0),    # Max - max
        (128, 127, 1),    # Mid-range with borrow
    ]
    
    for a, b, borrow_in in edge_cases:
        if a <= tb.mask and b <= tb.mask:
            tb.dut.i_a.value = a
            tb.dut.i_b.value = b
            try:
                tb.dut.i_borrow_in.value = borrow_in
            except AttributeError:
                tb.dut.i_b_in.value = borrow_in
            
            await tb.wait_time(1, 'ns')
            
            expected_diff = (a - b - borrow_in) & tb.mask
            expected_borrow = int(a < (b + borrow_in))
            
            try:
                actual_diff = int(tb.dut.ow_difference.value)
                actual_borrow = int(tb.dut.ow_carry_out.value)
            except AttributeError:
                actual_diff = int(tb.dut.ow_d.value)
                actual_borrow = int(tb.dut.ow_b.value)
            
            assert actual_diff == expected_diff, f"Edge case {a}-{b}-{borrow_in} difference failed"
            assert actual_borrow == expected_borrow, f"Edge case {a}-{b}-{borrow_in} borrow failed"
    
    tb.log.info(f"Final results: {tb.pass_count}/{tb.test_count} passed")

@cocotb.test()
async def test_borrow_propagation(dut):
    """Test borrow propagation through multiple bits"""
    tb = SubtractorTB(dut)
    
    # Test cases that require extensive borrow propagation
    borrow_cases = [
        (0b00000000, 0b00000001, 0),  # 0 - 1, requires borrow from all higher bits
        (0b10000000, 0b10000001, 0),  # MSB set, subtract 1 more
        (0b01111111, 0b10000000, 0),  # Large subtraction requiring MSB borrow
    ]
    
    for a, b, borrow_in in borrow_cases:
        if a <= tb.mask and b <= tb.mask:
            tb.dut.i_a.value = a
            tb.dut.i_b.value = b
            try:
                tb.dut.i_borrow_in.value = borrow_in
            except AttributeError:
                tb.dut.i_b_in.value = borrow_in
            
            await tb.wait_time(2, 'ns')  # Extra time for borrow propagation
            
            # Check result
            expected_diff = (a - b - borrow_in) & tb.mask
            expected_borrow = int(a < (b + borrow_in))
            
            try:
                actual_diff = int(tb.dut.ow_difference.value)
                actual_borrow = int(tb.dut.ow_carry_out.value)
            except AttributeError:
                actual_diff = int(tb.dut.ow_d.value)
                actual_borrow = int(tb.dut.ow_b.value)
            
            tb.log.info(f"Borrow test: {a:08b} - {b:08b} - {borrow_in} = {actual_diff:08b}, borrow={actual_borrow}")
            
            assert actual_diff == expected_diff
            assert actual_borrow == expected_borrow
```

### Signed Subtraction Test
```python
@cocotb.test()
async def test_signed_subtraction(dut):
    """Test signed subtraction operations"""
    tb = SubtractorTB(dut)
    
    # Test signed interpretation of results
    signed_cases = [
        (5, 3),    # Positive - positive, positive result
        (3, 5),    # Positive - positive, negative result  
        (0, 1),    # Zero - positive, negative result
        (127, 128), # Edge of signed range
    ]
    
    for a, b in signed_cases:
        if a <= tb.mask and b <= tb.mask:
            tb.dut.i_a.value = a
            tb.dut.i_b.value = b
            tb.dut.i_borrow_in.value = 0
            
            await tb.wait_time(1, 'ns')
            
            actual_diff = int(tb.dut.ow_difference.value)
            actual_borrow = int(tb.dut.ow_carry_out.value)
            
            # Interpret as signed values
            if actual_borrow:
                # Result is negative, use 2's complement
                signed_result = -(((~actual_diff) & tb.mask) + 1)
            else:
                signed_result = actual_diff
            
            expected_signed = a - b
            tb.log.info(f"Signed: {a} - {b} = {expected_signed} (got {signed_result})")
```

## Test Levels

### Basic Level
- **Test Count**: min(64, 2^N) test vectors
- **Includes**: Main loop testing only
- **Duration**: Fast, suitable for continuous integration

### Medium Level
- **Test Count**: min(128, 2^N) test vectors
- **Includes**: Main loop + walking ones test
- **Duration**: Moderate, good for regular validation

### Full Level
- **Test Count**: min(256, 2^N) test vectors
- **Includes**: All test patterns (main loop, walking ones, alternating patterns)
- **Duration**: Comprehensive, suitable for final verification

## Signal Interface Flexibility

The module handles different signal naming conventions:

### Primary Interface
- Inputs: `i_a`, `i_b`, `i_borrow_in`
- Outputs: `ow_difference`, `ow_carry_out`

### Alternative Interface
- Inputs: `i_a`, `i_b`, `i_b_in`
- Outputs: `ow_d`, `ow_b`

### Half Subtractor Interface
- Outputs: `o_d`, `o_b`

## Error Analysis

### Common Failure Patterns

#### 1. Borrow Propagation Errors
```
Test failed: 128 - 129 - 0
  Expected: difference=255, borrow=1
  Actual: difference=254, borrow=1
  
  Binary comparison:
    a      = 10000000
    b      = 10000001
    b_in   = 0
    exp_diff = 11111111
    act_diff = 11111110
  
  Debug: Check borrow chain implementation
```

#### 2. Interface Mismatches
```
AttributeError: 'dut' object has no attribute 'i_borrow_in'
  
  Solution: Check if DUT uses 'i_b_in' instead
  Or verify output signal names (ow_difference vs ow_d)
```

#### 3. Bit Width Issues
```
Walking ones test failed at bit position 7:
  Input: a=10000000, b=00000000, b_in=1
  Expected: difference=01111111, borrow=0
  Actual: difference=10000000, borrow=0
  
  Debug: Check MSB handling and bit width configuration
```

### Troubleshooting Steps

1. **Verify Interface**: Check signal names match DUT implementation
2. **Test Basic Cases**: Start with simple subtraction (1-0, 2-1, etc.)
3. **Check Bit Widths**: Ensure PARAM_N matches DUT configuration
4. **Analyze Patterns**: Look for systematic failures in specific bit positions

## Performance Optimization

### Automatic Test Vector Selection
```python
if self.max_val < count:
    # Exhaustive testing for small parameter spaces
    test_all_combinations()
else:
    # Statistical sampling for large parameter spaces
    stratified_random_sampling(count)
```

### Progress Reporting
- Periodic progress updates during long test runs
- Early termination on systematic failures
- Detailed failure analysis with binary representations

## Architecture-Specific Considerations

### Ripple Borrow Subtractors
- **Propagation Delay**: Account for borrow chain delay
- **Critical Path**: Longest borrow propagation path
- **Timing**: Adequate settling time for cascaded borrows

### Look-Ahead Borrow Subtractors
- **Generate/Propagate**: Proper G/P signal generation
- **Parallel Computation**: Simultaneous borrow calculation
- **Speed vs. Area**: Trade-off validation

### Signed vs. Unsigned
- **Two's Complement**: Proper handling of signed operands
- **Overflow Detection**: Identification of result overflow
- **Sign Extension**: Correct bit width handling

This module provides comprehensive validation of subtractor implementations, ensuring correct arithmetic operations, proper borrow handling, and accurate difference calculations across all operating conditions and input patterns.