# Adder Testing

## Overview

The `adder_testing` module provides a comprehensive testbench for verifying adder circuit implementations. It supports testing various adder types, including ripple-carry, carry-lookahead, and carry-save architectures. The module handles parameter configuration, test vector generation, and comprehensive verification with different test levels.

## Class Definition

```python
class AdderTB(TBBase):
    """Base Testbench for various adder implementations

    This class provides common functionality for testing various
    adder architectures and configurations.
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        # Gather the settings from the Parameters to verify them
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '1'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize the random generator
        random.seed(self.seed)

        # Track test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        # Get DUT type
        self.dut_type = os.environ.get('DUT', 'unknown')
        self.log.info(f"Testing {self.dut_type} with N={self.N}")
```

## Key Features

- Support for different adder architectures
- Bit-width parameterization via PARAM_N
- Directed test patterns (walking ones, alternating bits)
- Randomized test vector generation
- Special test for half adders
- Carry-save adder specific testing
- Binary representation in error messages
- Detailed test statistics and reporting

## Primary Methods

### main_loop

Tests all combinations of inputs up to max_val or randomly samples if max_val is larger than count.

```python
async def main_loop(self, count: int = 256) -> None:
    """Main test loop for standard adders.

    Tests all combinations of inputs up to max_val or randomly samples
    if max_val is larger than count.

    Args:
        count: Number of test vectors to generate if random sampling
    """
    # Implementation...
```

### half_adder_test

Specific test for half adders, testing only the four possible input combinations.

```python
async def half_adder_test(self) -> None:
    """Specific test for half adders.

    Tests all four input combinations for a half adder.
    Half adders only have i_a and i_b inputs (no carry in).
    """
    # Implementation...
```

### main_loop_carry_save

Test loop for carry-save adders which produce separate sum and carry outputs for each bit position.

```python
async def main_loop_carry_save(self, count: int = 256) -> None:
    """Test loop for carry-save adders.

    Carry-save adders produce separate sum and carry outputs for each bit position.

    Args:
        count: Number of test vectors to generate if random sampling
    """
    # Implementation...
```

### walking_ones_test

Tests the adder with a sequential pattern where a single bit is set to 1 and walks through all bit positions.

```python
async def walking_ones_test(self) -> None:
    """Walking ones test pattern.

    Tests the adder with a sequential pattern where a single bit
    is set to 1 and walks through all bit positions.
    """
    # Implementation...
```

### alternating_pattern_test

Tests with alternating bit patterns (0101... and 1010...) to check for issues with adjacent bits affecting each other.

```python
async def alternating_pattern_test(self) -> None:
    """Test with alternating bit patterns (0101... and 1010...).

    This tests for issues with adjacent bits affecting each other.
    """
    # Implementation...
```

### run_comprehensive_tests

Runs a comprehensive suite of tests based on the test_level.

```python
async def run_comprehensive_tests(self) -> None:
    """Run a comprehensive suite of tests based on test_level.

    This combines multiple test patterns to thoroughly test the adder.
    """
    # Implementation...
```

## Utility Methods

### clear_interface

Clears the DUT interface by setting all inputs to 0.

```python
async def clear_interface(self) -> None:
    """Clear the DUT interface by setting all inputs to 0."""
    # Implementation...
```

### print_settings

Prints the current testbench settings.

```python
def print_settings(self) -> None:
    """Print the current testbench settings."""
    # Implementation...
```

## Test Methodology

The adder testing methodology includes several approaches:

1. **Exhaustive Testing**: For small bit widths, tests all possible input combinations
2. **Randomized Testing**: For larger bit widths, tests random sampling of input space
3. **Directed Testing**: Uses specific patterns like walking ones and alternating bits
4. **Edge Cases**: Tests special cases like zero, maximum values, and carries

For each test case, the module:
1. Applies test vector inputs to the DUT
2. Computes expected outputs based on correct adder behavior
3. Compares DUT outputs with expected outputs
4. Reports detailed error information for failures

## Implementation Approach

The implementation provides detailed error reporting when failures occur:

```python
if (ow_sum != expected_sum) or (ow_carry != expected_carry):
    self.log.error(f"Test failed at {test_idx+1}/{total_tests}:")
    self.log.error(f"  Input: a={a}, b={b}, c_in={c_in}")
    self.log.error(f"  Expected: sum={expected_sum}, carry={expected_carry}")
    self.log.error(f"  Actual: sum={ow_sum}, carry={ow_carry}")
    self.fail_count += 1

    # For comprehensive analysis, also print binary representation
    self.log.error(f"  Binary comparison:")
    self.log.error(f"    a      = {bin(a)[2:].zfill(self.N)}")
    self.log.error(f"    b      = {bin(b)[2:].zfill(self.N)}")
    self.log.error(f"    c_in   = {bin(c_in)[2:]}")
    self.log.error(f"    exp_sum= {bin(expected_sum)[2:].zfill(self.N)}")
    self.log.error(f"    act_sum= {bin(ow_sum)[2:].zfill(self.N)}")

    assert False, f"Adder test failed: Input: a={a}, b={b}, c_in={c_in}\nExpected: sum={expected_sum}, carry={expected_carry}\nGot: sum={ow_sum}, carry={ow_carry}"
else:
    self.pass_count += 1
```

## Example Usage

Basic usage of the adder testbench:

```python
from CocoTBFramework.tbclasses.common.adder_testing import AdderTB

@cocotb.test()
async def test_adder(dut):
    # Create testbench
    tb = AdderTB(dut)
    
    # Print settings
    tb.print_settings()
    
    # Run comprehensive tests
    await tb.run_comprehensive_tests()
```

Testing a specific adder type with custom parameters:

```python
@cocotb.test()
async def test_carry_lookahead_adder(dut):
    # Create testbench
    tb = AdderTB(dut)
    
    # Override test level if needed
    tb.test_level = 'full'
    
    # For testing carry-lookahead efficiency
    tb.set_custom_timeout(10000, 'ns')
    
    # Run comprehensive tests
    await tb.run_comprehensive_tests()
```

Running a specific test for debugging:

```python
@cocotb.test()
async def debug_adder_pattern(dut):
    # Create testbench
    tb = AdderTB(dut)
    
    # Run only the walking ones test
    await tb.walking_ones_test()
```

## Implementation Notes

- DUT signals use standard names: i_a, i_b, i_c, ow_sum, ow_carry
- PARAM_N environment variable controls bit width
- TEST_LEVEL environment variable controls test complexity
- SEED environment variable ensures reproducible randomization
- Half adders have distinct testing due to simpler interface
- Carry-save adders need special handling for separate sum/carry outputs
- Different adder architectures can be tested by varying the DUT type

## See Also

- [Subtractor Testing](subtractor_testing.md) - Similar approach for subtractor verification
- [Multiplier Testing](multiplier_testing.md) - Testing for multiplier components

## Navigation

[↑ Common Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
