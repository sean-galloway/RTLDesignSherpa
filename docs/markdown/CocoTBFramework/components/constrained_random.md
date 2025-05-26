# ConstrainedRandom

## Overview

The `ConstrainedRandom` class provides functionality for generating random values based on specified constraints and weights. It's a fundamental building block for constrained random verification in the CocoTBFramework.

## Features

- Generate random integers or floating-point values
- Support for multiple constraint ranges with different probabilities
- Customizable weighting for different value ranges
- Simple but powerful API

## Classes

### ConstrainedRandom

The main class for generating constrained random values.

#### Constructor Parameters

```python
def __init__(self, constraints, weights, is_integer=True)
```

- `constraints`: List of tuples, where each tuple is a `(min_value, max_value)` range
- `weights`: List of weights corresponding to each constraint range
- `is_integer`: Boolean flag indicating whether to generate integer values (True) or floating-point values (False)

#### Methods

- `next()`: Generate the next constrained random value according to the configured constraints and weights

## Example Usage

### Basic Integer Randomization

```python
from CocoTBFramework.components.constrained_random import ConstrainedRandom

# Define constraints with two ranges:
# - 80% probability of values between 1-10
# - 20% probability of values between 50-100
constraints = [(1, 10), (50, 100)]
weights = [0.8, 0.2]

# Create the randomizer for integers
randomizer = ConstrainedRandom(constraints, weights)

# Generate 5 random values
for i in range(5):
    value = randomizer.next()
    print(f"Random value {i+1}: {value}")
```

### Floating-Point Randomization

```python
# Create a randomizer for floating-point values
# - 70% probability of values between 0.0-1.0
# - 30% probability of values between 5.0-10.0
constraints = [(0.0, 1.0), (5.0, 10.0)]
weights = [0.7, 0.3]

# The third parameter (False) indicates floating-point values
float_randomizer = ConstrainedRandom(constraints, weights, False)

# Generate 5 random floating-point values
for i in range(5):
    value = float_randomizer.next()
    print(f"Random float {i+1}: {value:.4f}")
```

### Using in a Test Environment

```python
# Create a randomizer for packet delay values
delay_randomizer = ConstrainedRandom(
    constraints=[(1, 5), (10, 20), (50, 100)],
    weights=[0.6, 0.3, 0.1]
)

# Use in a test loop
for i in range(10):
    # Get random delay value
    delay = delay_randomizer.next()
    
    # Use the delay in the test
    await Timer(delay, units='ns')
    await RisingEdge(dut.clk)
    
    # Apply stimulus with the random delay
    dut.data_in.value = i
    dut.valid_in.value = 1
```

## Notes

- The `ConstrainedRandom` class provides a simpler alternative to the more feature-rich [FlexRandomizer](flex_randomizer.md)
- Weights are normalized internally, so they don't need to sum to 1.0 or 100%
- Error handling is included to ensure constraints and weights arrays have the same length

## See Also

- [FlexRandomizer](flex_randomizer.md) - More advanced randomization capabilities
- [RandomizationConfig](randomization_config.md) - Configuration framework for randomization

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
