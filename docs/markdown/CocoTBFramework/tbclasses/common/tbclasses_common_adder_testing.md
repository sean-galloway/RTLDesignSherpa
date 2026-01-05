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

# Adder Testing Module Documentation

## Overview

The `AdderTB` class provides comprehensive testing capabilities for various adder implementations including full adders, half adders, and carry-save adders. It systematically tests all aspects of addition operations with configurable test depths and detailed error analysis.

## Purpose and Use Cases

### When to Use AdderTB
- Testing combinational adder circuits (ripple carry, carry lookahead, etc.)
- Verifying half adder implementations
- Validating carry-save adder architectures
- Ensuring proper carry propagation across bit widths
- Stress testing with various input patterns

### Supported Adder Types
- **Full Adders**: With carry input (`i_c`) and carry output (`ow_carry`)
- **Half Adders**: Simple A + B operations without carry input
- **Carry-Save Adders**: Separate sum and carry outputs for each bit position

## Configuration

### Environment Variables
- `PARAM_N`: Bit width of the adder (default: 1)
- `TEST_LEVEL`: Test intensity - basic/medium/full (default: basic)
- `SEED`: Random number generator seed (default: 12345)
- `DUT`: Device under test identifier

### Expected DUT Interface

#### Full Adder Interface
```verilog
module full_adder #(parameter N = 8) (
    input  [N-1:0] i_a,        // First operand
    input  [N-1:0] i_b,        // Second operand  
    input          i_c,        // Carry input
    output [N-1:0] ow_sum,     // Sum output
    output         ow_carry    // Carry output
);
```

#### Half Adder Interface
```verilog
module half_adder (
    input  i_a,        // First operand
    input  i_b,        // Second operand
    output ow_sum,     // Sum output
    output ow_carry    // Carry output
);
```

#### Carry-Save Adder Interface
```verilog
module carry_save_adder #(parameter N = 8) (
    input  [N-1:0] i_a,        // First operand
    input  [N-1:0] i_b,        // Second operand
    input  [N-1:0] i_c,        // Third operand (carry input per bit)
    output [N-1:0] ow_sum,     // Sum output (per bit)
    output [N-1:0] ow_carry    // Carry output (per bit)
);
```

## Test Methodologies

### 1. Main Loop Testing (`main_loop`)
**Purpose**: Comprehensive testing of standard addition operations

**Test Strategy**:
- **Small parameter spaces**: Exhaustive testing of all possible input combinations
- **Large parameter spaces**: Statistical sampling with random test vectors
- **Verification**: `(a + b + carry_in) = sum + (carry_out × 2^N)`

**Test Vectors**:
```python
# For N-bit adders
total_combinations = 2^N × 2^N × 2  # a_values × b_values × carry_values
```

### 2. Half Adder Testing (`half_adder_test`)
**Purpose**: Specific validation for half adder implementations

**Test Cases**:
| a | b | Expected Sum | Expected Carry |
|---|---|--------------|----------------|
| 0 | 0 | 0           | 0              |
| 0 | 1 | 1           | 0              |
| 1 | 0 | 1           | 0              |
| 1 | 1 | 0           | 1              |

### 3. Carry-Save Adder Testing (`main_loop_carry_save`)
**Purpose**: Validate carry-save adder bit-level operations

**Algorithm**:
```python
for each bit position i:
    sum[i] = a[i] ⊕ b[i] ⊕ c[i]        # XOR operation
    carry[i] = (a[i] & b[i]) | (a[i] & c[i]) | (b[i] & c[i])  # Majority function
```

### 4. Walking Ones Test (`walking_ones_test`)
**Purpose**: Test carry propagation with systematic bit patterns

**Pattern**: Single bit set to 1, walking through all positions
```
Position 0: 0000_0001
Position 1: 0000_0010  
Position 2: 0000_0100
...
Position N-1: 1000_0000
```

### 5. Alternating Pattern Test (`alternating_pattern_test`)
**Purpose**: Test for adjacent bit interactions

**Patterns**:
- `pattern1`: 0101_0101... (alternating 01)
- `pattern2`: 1010_1010... (alternating 10)

## Implementation Example

### Basic Usage
```python
import cocotb
from CocoTBFramework.tbclasses.common.adder_testing import AdderTB

@cocotb.test()
async def test_full_adder(dut):
    """Test a full adder implementation"""
    tb = AdderTB(dut)
    tb.print_settings()
    await tb.run_comprehensive_tests()

@cocotb.test()
async def test_half_adder(dut):
    """Test a half adder implementation"""
    tb = AdderTB(dut)
    await tb.half_adder_test()

@cocotb.test()
async def test_carry_save_adder(dut):
    """Test a carry-save adder implementation"""
    tb = AdderTB(dut)
    await tb.main_loop_carry_save(count=500)
```

### Advanced Configuration
```python
@cocotb.test()
async def test_adder_comprehensive(dut):
    """Comprehensive adder testing with custom configuration"""
    tb = AdderTB(dut)
    
    # Print configuration for debugging
    tb.print_settings()
    
    # Run individual test suites
    await tb.clear_interface()
    await tb.main_loop(count=1000)
    await tb.walking_ones_test()
    await tb.alternating_pattern_test()
    
    # Report final statistics
    tb.log.info(f"Final results: {tb.pass_count}/{tb.test_count} passed")
```

## Test Levels

### Basic Level
- Test count: min(64, 2^N) test vectors
- Includes: Main loop testing only
- Duration: Fast, suitable for continuous integration

### Medium Level  
- Test count: min(128, 2^N) test vectors
- Includes: Main loop + walking ones test
- Duration: Moderate, good for regular validation

### Full Level
- Test count: min(256, 2^N) test vectors
- Includes: All test patterns (main loop, walking ones, alternating patterns)
- Duration: Comprehensive, suitable for final verification

## Error Analysis

### Failure Reporting
When a test fails, the module provides detailed analysis:

```
Test failed at 1234/5000:
  Input: a=85, b=170, c_in=1
  Expected: sum=0, carry=1
  Actual: sum=1, carry=0
  Binary comparison:
    a      = 01010101
    b      = 10101010  
    c_in   = 1
    exp_sum= 00000000
    act_sum= 00000001
```

### Common Failure Patterns
1. **Carry propagation errors**: Incorrect carry chain implementation
2. **Bit position errors**: Wrong bit ordering or indexing
3. **Overflow handling**: Incorrect handling of maximum value additions
4. **Interface mismatches**: Wrong signal names or bit widths

## Performance Optimization

### Automatic Test Vector Selection
```python
if self.max_val < count:
    # Exhaustive testing for small parameter spaces
    test_all_combinations()
else:
    # Random sampling for large parameter spaces  
    random_sampling(count)
```

### Progress Reporting
- Periodic progress updates during long test runs
- Automatic test termination on systematic failures
- Detailed timing and performance metrics

## Troubleshooting

### Common Issues
1. **AttributeError on signal access**: Check DUT interface signal names
2. **Timeout errors**: Increase safety limits for large parameter spaces
3. **Memory issues**: Reduce test count or increase memory limits

### Debug Strategies
1. Enable DEBUG logging: `TBBase.default_log_level = logging.DEBUG`
2. Run with basic test level first
3. Check individual test methods separately
4. Verify DUT interface matches expected signals

### Environment Setup
```bash
# Example configuration
export PARAM_N=8
export TEST_LEVEL=medium
export SEED=42
export TB_MAX_DURATION_MIN=30
```

This module provides a robust foundation for verifying adder implementations across various architectures and bit widths, ensuring comprehensive coverage of both functional correctness and edge case handling.