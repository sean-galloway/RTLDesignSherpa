# Divider Testing Module Documentation

## Overview

The `DividerTB` class provides comprehensive testing for digital divider implementations. It validates integer division operations, remainder calculations, divide-by-zero detection, and performance characteristics across various divider architectures including sequential and combinational designs.

## Purpose and Use Cases

### When to Use DividerTB
- Testing integer divider circuits (restoring, non-restoring, SRT algorithms)
- Verifying divide-by-zero detection and error handling
- Validating quotient and remainder accuracy
- Testing sequential divider timing and control logic
- Performance analysis and latency measurement

### Divider Fundamentals
Integer division produces two results:
- **Quotient**: Result of dividend ÷ divisor
- **Remainder**: What's left after division
- **Relationship**: dividend = (quotient × divisor) + remainder
- **Special Cases**: Division by zero must be detected and handled

## Configuration

### Environment Variables
- `PARAM_DATA_WIDTH`: Bit width for dividend and divisor (default: 16)
- `TEST_LEVEL`: Test intensity - basic/medium/full (default: basic)
- `SEED`: Random number generator seed (default: 12345)
- `DUT`: Device under test identifier

### Expected DUT Interface

```verilog
module divider #(
    parameter DATA_WIDTH = 16
) (
    input                      i_clk,        // Clock
    input                      i_rst_b,      // Active low reset
    
    // Control signals
    input                      i_start,      // Start division
    output                     o_done,       // Division complete
    output                     o_valid,      // Result valid
    output                     o_busy,       // Divider busy
    
    // Data interface
    input  [DATA_WIDTH-1:0]    i_dividend,   // Dividend input
    input  [DATA_WIDTH-1:0]    i_divisor,    // Divisor input
    output [DATA_WIDTH-1:0]    o_quotient,   // Quotient result
    output [DATA_WIDTH-1:0]    o_remainder,  // Remainder result
    output                     o_dbz         // Divide by zero flag
);
```

## Test Methodologies

### 1. Main Loop Testing (`main_loop`)
**Purpose**: Comprehensive division operation validation

**Test Strategy**:
- **Edge Cases**: Zero dividend, identity operations, maximum values
- **Divide by Zero**: Systematic testing of zero divisor detection
- **Random Testing**: Stratified sampling across value ranges
- **Boundary Testing**: Values near power-of-2 boundaries

**Test Vector Generation**:
```python
# Edge cases
edge_cases = [
    (0, 1),                # Zero dividend
    (1, 1),                # Identity  
    (max_val, 1),          # Max dividend, divisor 1
    (max_val, max_val)     # Max dividend, max divisor
]

# Divide by zero cases
dbz_cases = [(random.randint(1, max_val), 0) for _ in range(5)]

# Stratified random sampling
ranges = [
    (0, max_val//4),       # Small values
    (max_val//4, max_val//2),   # Medium values  
    (max_val//2, 3*max_val//4), # Large values
    (3*max_val//4, max_val)     # Maximum values
]
```

**Verification Logic**:
```python
if divisor == 0:
    # Should detect divide by zero
    assert dbz == True or valid == False
else:
    # Should produce correct quotient and remainder
    assert valid == True
    assert quotient == dividend // divisor
    assert remainder == dividend % divisor
    assert dividend == (quotient * divisor) + remainder
```

### 2. Latency Testing (`latency_test`)
**Purpose**: Measure division operation timing characteristics

**Measurement Method**:
```python
async def measure_latency(dividend, divisor):
    # Apply inputs
    dut.i_dividend.value = dividend
    dut.i_divisor.value = divisor
    
    # Start operation and measure time
    start_time = get_sim_time('ns')
    dut.i_start.value = 1
    await RisingEdge(dut.i_clk)
    dut.i_start.value = 0
    
    # Wait for completion
    while not int(dut.o_done.value):
        await RisingEdge(dut.i_clk)
    
    end_time = get_sim_time('ns')
    latency_cycles = (end_time - start_time) / clock_period
    return latency_cycles
```

**Analysis**:
- **Average Latency**: Mean cycles across all test cases
- **Worst Case**: Maximum latency observed
- **Best Case**: Minimum latency observed
- **Pattern Analysis**: Latency vs. operand magnitude

### 3. Back-to-Back Testing (`back_to_back_test`)
**Purpose**: Validate consecutive operation handling

**Test Pattern**:
```python
for i, (dividend, divisor) in enumerate(test_vectors):
    # Start operation immediately after previous
    dut.i_dividend.value = dividend
    dut.i_divisor.value = divisor
    dut.i_start.value = 1
    
    await RisingEdge(dut.i_clk)
    dut.i_start.value = 0
    
    # Wait for busy assertion
    await RisingEdge(dut.o_busy)
    
    # Wait for completion
    while not int(dut.o_done.value):
        await RisingEdge(dut.i_clk)
    
    # Verify results immediately
    verify_division_result(dividend, divisor)
    
    # No delay - start next operation
```

### 4. Performance Analysis
**Purpose**: Characterize divider performance across operating conditions

**Metrics**:
- **Throughput**: Operations per clock cycle
- **Latency Distribution**: Statistical analysis of completion times
- **Resource Utilization**: Clock cycles per bit width
- **Efficiency**: Comparison to theoretical optimal

## Implementation Examples

### Basic Divider Test
```python
import cocotb
from CocoTBFramework.tbclasses.common.divider_testing import DividerTB

@cocotb.test()
async def test_divider_basic(dut):
    """Basic divider functionality test"""
    tb = DividerTB(dut)
    tb.print_settings()
    await tb.run_comprehensive_tests()

@cocotb.test()
async def test_divide_by_zero(dut):
    """Test divide by zero detection"""
    tb = DividerTB(dut)
    
    await tb.start_clock()
    await tb.reset_dut()
    
    # Test various divide by zero cases
    test_dividends = [1, 100, 65535]
    
    for dividend in test_dividends:
        valid, quotient, remainder, dbz = await tb.perform_division(dividend, 0)
        assert dbz == True or valid == False, f"Divide by zero not detected for {dividend}/0"
```

### Performance Analysis Test
```python
@cocotb.test()
async def test_divider_performance(dut):
    """Analyze divider performance characteristics"""
    tb = DividerTB(dut)
    
    await tb.start_clock(10, 'ns')  # 100MHz clock
    await tb.reset_dut()
    
    # Run latency analysis
    await tb.latency_test(count=50)
    
    # Run back-to-back test
    await tb.back_to_back_test(count=20)
    
    # Custom performance test
    test_cases = [
        (1, 1),           # Minimum case
        (65535, 1),       # Maximum dividend
        (65535, 65535),   # Maximum both
        (32768, 2),       # Power of 2 divisor
        (65535, 3),       # Prime divisor
    ]
    
    for dividend, divisor in test_cases:
        latency = await tb.measure_operation_latency(dividend, divisor)
        tb.log.info(f"Latency for {dividend}/{divisor}: {latency} cycles")
```

### Advanced Divider Verification
```python
@cocotb.test()
async def test_divider_advanced(dut):
    """Advanced divider verification"""
    tb = DividerTB(dut)
    
    await tb.start_clock()
    await tb.reset_dut()
    
    # Test 1: Exhaustive small values
    if tb.DATA_WIDTH <= 8:
        for dividend in range(2**tb.DATA_WIDTH):
            for divisor in range(1, 2**tb.DATA_WIDTH):
                valid, q, r, dbz = await tb.perform_division(dividend, divisor)
                assert valid and not dbz
                assert q == dividend // divisor
                assert r == dividend % divisor
    
    # Test 2: Boundary conditions
    max_val = (2**tb.DATA_WIDTH) - 1
    boundary_tests = [
        (0, 1),           # Zero dividend
        (max_val, 1),     # Maximum dividend, unity divisor
        (max_val, max_val), # Maximum both
        (max_val//2, max_val//2), # Half maximum
    ]
    
    for dividend, divisor in boundary_tests:
        valid, q, r, dbz = await tb.perform_division(dividend, divisor)
        expected_q = dividend // divisor
        expected_r = dividend % divisor
        
        assert valid and not dbz, f"Operation {dividend}/{divisor} should be valid"
        assert q == expected_q, f"Quotient mismatch: expected {expected_q}, got {q}"
        assert r == expected_r, f"Remainder mismatch: expected {expected_r}, got {r}"
    
    # Test 3: Power of 2 divisors (should be fast)
    powers_of_2 = [1 << i for i in range(tb.DATA_WIDTH)]
    for divisor in powers_of_2:
        dividend = max_val
        valid, q, r, dbz = await tb.perform_division(dividend, divisor)
        expected_q = dividend // divisor
        expected_r = dividend % divisor
        
        assert q == expected_q and r == expected_r
```

## Test Levels

### Basic Level
- **Test Count**: 50 main operations, 10 latency tests, 5 back-to-back
- **Focus**: Essential functionality and divide-by-zero detection
- **Duration**: Fast, suitable for continuous integration

### Medium Level
- **Test Count**: 100 main operations, 20 latency tests, 10 back-to-back
- **Focus**: Performance analysis and extended validation
- **Duration**: Moderate, good for regular validation

### Full Level
- **Test Count**: 200 main operations, 30 latency tests, 20 back-to-back
- **Focus**: Comprehensive testing including stress conditions
- **Duration**: Extended, suitable for final verification

## Algorithm-Specific Considerations

### Sequential Dividers
- **Control Logic**: Start/done handshaking
- **State Machines**: Proper state transitions
- **Timing**: Predictable or data-dependent latency

### Combinational Dividers
- **Propagation Delay**: Critical path analysis
- **Resource Usage**: Gate count and complexity
- **Power Consumption**: Switching activity

### SRT Dividers
- **Quotient Selection**: Proper digit selection logic
- **Convergence**: Guaranteed completion
- **Precision**: Correct remainder calculation

## Error Analysis

### Common Failure Patterns
1. **Incorrect Quotient**: Off-by-one errors, algorithm bugs
2. **Wrong Remainder**: Incomplete subtraction, precision issues
3. **Divide-by-Zero Missed**: No detection or wrong flag
4. **Timing Issues**: Premature done signal, incomplete calculation

### Debug Information
```
Division test failed:
  Input: dividend=12345, divisor=67
  Expected: quotient=184, remainder=17
  Actual: quotient=183, remainder=84
  Verification: 12345 = (183 × 67) + 84 = 12261 + 84 = 12345 ✓
  Error: Quotient off by 1, remainder incorrect
```

### Troubleshooting Steps
1. **Verify Basic Cases**: Start with simple divisions (1/1, 2/1, etc.)
2. **Check Timing**: Ensure proper start/done handshaking
3. **Validate Interface**: Confirm signal names and bit widths
4. **Algorithm Analysis**: Review division algorithm implementation

## Performance Optimization

### Test Vector Selection
```python
# Automatic scaling based on data width
if DATA_WIDTH <= 8:
    # Exhaustive testing for small widths
    test_all_combinations()
elif DATA_WIDTH <= 16:
    # Representative sampling
    stratified_sampling(count)
else:
    # Statistical sampling only
    random_sampling(count)
```

### Parallel Testing
For large parameter spaces, tests can be parallelized:
- Multiple random seeds for independent test runs
- Separate test processes for different value ranges
- Concurrent latency and functional testing

This module provides comprehensive validation of divider implementations, ensuring correct arithmetic operations, proper error handling, and adequate performance across all operating conditions and data ranges.