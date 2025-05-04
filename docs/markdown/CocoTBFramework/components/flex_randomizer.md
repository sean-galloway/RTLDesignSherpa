# FlexRandomizer

## Overview

The `FlexRandomizer` class provides a powerful and flexible approach to constrained randomization in verification environments. It extends beyond simple range-based randomization to support sequences, custom generators, and object randomization, giving users fine-grained control over randomization strategies.

## Features

- Constrained random generation with weighted distributions
- Sequence-based value generation
- Function-based generators that can depend on other values
- Support for object bins (not just numeric values)
- Dynamic switching between randomization modes
- Built on Cocotb's `Randomized` class for integration with coverage-driven verification

## Classes

### FlexRandomizer

The main class that randomizes values based on specified constraints.

#### Constructor

```python
def __init__(self, constraints: Dict)
```

- `constraints`: A dictionary defining the constraints for each field:
  - Key: Field name
  - Value: One of the following:
    - Tuple `(bins, weights)`: For constrained random generation
      - Bins: List of tuples `(min, max)` for integer ranges or lists of objects for selecting from discrete objects
      - Weights: List of relative weights for each bin
    - List/Tuple: For sequence looping
    - Callable: For function-based generation

#### Key Methods

- `next()`: Generate the next set of random values according to constraints
- `set_sequence(delay_name, sequence)`: Override a field to use a sequence
- `set_generator(delay_name, generator)`: Override a field to use a generator function
- `reset_to_random(delay_name)`: Reset a field back to using constrained random values

## Example Usage

### Basic Constrained Randomization

```python
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Define constraints with bins and weights
constraints = {
    'clock_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),  # 70% chance of 5-10, 30% chance of 20-30
    'data_delay': ([(1, 5), (8, 12), (15, 20)], [0.5, 0.3, 0.2]),  # Multiple bins with weights
    'reset_delay': ([(0, 5)], [1.0])  # Single bin with 100% weight
}

# Create the randomizer
flex_rand = FlexRandomizer(constraints)

# Generate and use random values
for i in range(5):
    values = flex_rand.next()
    print(f"Set {i+1}: {values}")
    
    # Use the values in your testbench
    clock_delay = values['clock_delay']
    data_delay = values['data_delay']
    # ... (use the delay values)
```

### Sequence Looping

```python
# Convert clock_delay to use a sequence
clock_sequence = [5, 10, 15, 20, 25]
flex_rand.set_sequence('clock_delay', clock_sequence)

# Generate values with the sequence
for i in range(8):
    values = flex_rand.next()
    print(f"Set {i+1}: {values}")
    # clock_delay will loop through the sequence: 5, 10, 15, 20, 25, 5, 10, 15
```

### Function Generators

```python
# Set data_delay to depend on clock_delay
flex_rand.set_generator('data_delay', lambda values: values['clock_delay'] * 2)

# Generate values with the generator
for i in range(5):
    values = flex_rand.next()
    print(f"Set {i+1}: {values}")
    # data_delay will always be twice the clock_delay
```

### Object Bins

```python
# Define constraints with various types of bins
constraints = {
    # Integer range bins
    'int_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),

    # String bins - each bin is a tuple of strings
    'message_type': ([('GET', 'PUT', 'POST'), ('DELETE', 'PATCH')], [0.7, 0.3]),

    # Complex object bins (using tuples for demonstration)
    'transaction': ([
        (('read', 4), ('read', 8)),    # Read transactions
        (('write', 4), ('write', 8))   # Write transactions
    ], [0.6, 0.4])
}

# Create the randomizer
flex_rand = FlexRandomizer(constraints)

# Generate random values
for i in range(5):
    values = flex_rand.next()
    print(f"Set {i+1}: {values}")
    
    # Use the object values in your testbench
    if values['message_type'] == 'GET':
        # Handle GET request
        pass
```

### Mixed Randomization Modes

```python
# Define constraints with different types
mixed_constraints = {
    'random_delay': ([(1, 10), (20, 30)], [0.8, 0.2]),  # Standard constrained random
    'sequence_delay': [5, 10, 15, 20],                  # Sequence for looping
    'function_delay': lambda: random.randint(1, 100)    # Function generator
}

# Create randomizer with mixed constraints
mixed_rand = FlexRandomizer(mixed_constraints)

# Generate values
for i in range(5):
    values = mixed_rand.next()
    print(f"Set {i+1}: {values}")
```

## Advanced Usage Patterns

### Testbench Timing Control

```python
# Create a randomizer for controlling timing parameters
timing_constraints = {
    'clk_to_q': ([(2, 5), (6, 10)], [0.8, 0.2]),
    'setup_time': ([(1, 3)], [1.0]),
    'hold_time': ([(1, 2)], [1.0]),
    'clock_period': ([(10, 20), (30, 50)], [0.7, 0.3])
}

timing_rand = FlexRandomizer(timing_constraints)

# Run tests with fully random values
for i in range(3):
    timing = timing_rand.next()
    # Use timing values in test

# Fix clock period for stability tests
timing_rand.set_sequence('clock_period', [20, 20, 20, 20, 20])

# Make hold time dependent on setup time
timing_rand.set_generator('hold_time', lambda values: values['setup_time'] // 2)

# Run controlled tests
for i in range(3):
    timing = timing_rand.next()
    # Use partially controlled timing values

# Reset to fully random for coverage-driven tests
timing_rand.reset_to_random('clock_period')
timing_rand.reset_to_random('hold_time')
```

## Comprehensive Examples

The module includes comprehensive examples in its source code that demonstrate:

- Basic constrained randomization
- Sequence looping 
- Function generators
- Mixed randomization modes
- Error handling
- Object bins
- Advanced usage patterns

## Notes

- `FlexRandomizer` extends the capabilities of the simpler [ConstrainedRandom](constrained_random.md) class
- It provides a unified interface for multiple randomization strategies
- It can be used directly or as a backend for the [RandomizationConfig](randomization_config.md) class
- The class handles type conversion and validation internally

## See Also

- [ConstrainedRandom](constrained_random.md) - Simpler constrained randomization
- [RandomizationConfig](randomization_config.md) - Higher-level configuration framework
- [Packet](packet.md) - Can use FlexRandomizer for field generation

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
