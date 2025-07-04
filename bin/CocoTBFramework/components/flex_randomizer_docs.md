# FlexRandomizer Documentation

## Overview

FlexRandomizer is a thread-safe randomization engine designed for protocol verification environments. It provides constrained randomization with multiple strategies including weighted bins, sequence looping, function-based generation, and object selection.

## Key Features

- **Thread-Safe**: Uses RLock for concurrent verification environments
- **Multiple Constraint Types**: Supports different randomization strategies
- **Dynamic Reconfiguration**: Change constraint types at runtime
- **Comprehensive Error Handling**: Detailed error messages with caller context
- **Object Support**: Handle both numeric ranges and discrete object selection

## Installation

```python
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
```

## Basic Usage

### 1. Constrained Random with Weighted Bins

```python
# Define constraints with weighted probability bins
constraints = {
    'clock_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),  # 70% chance of 5-10, 30% chance of 20-30
    'data_delay': ([(1, 5), (8, 12)], [0.6, 0.4])      # 60% chance of 1-5, 40% chance of 8-12
}

randomizer = FlexRandomizer(constraints)

# Generate values
values = randomizer.next()
print(values)  # {'clock_delay': 7, 'data_delay': 9}
```

### 2. Sequence-Based Randomization

```python
constraints = {
    'sequence_delay': [5, 10, 15, 20]  # Will cycle: 5, 10, 15, 20, 5, 10, ...
}

randomizer = FlexRandomizer(constraints)

# Generate sequence values
for i in range(6):
    values = randomizer.next()
    print(f"Step {i}: {values['sequence_delay']}")
# Output: 5, 10, 15, 20, 5, 10
```

### 3. Function-Based Generation

```python
import random

constraints = {
    'computed_delay': lambda: random.randint(1, 100),
    'dependent_delay': lambda vals: vals.get('computed_delay', 0) * 2
}

randomizer = FlexRandomizer(constraints)
values = randomizer.next()
print(values)  # {'computed_delay': 42, 'dependent_delay': 84}
```

### 4. Object Bins (Discrete Values)

```python
# Choose from discrete string values
constraints = {
    'message_type': ([['GET', 'POST'], ['DELETE']], [0.8, 0.2]),  # 80% GET/POST, 20% DELETE
    'priority': ([['HIGH'], ['MEDIUM', 'LOW']], [0.3, 0.7])       # 30% HIGH, 70% MEDIUM/LOW
}

randomizer = FlexRandomizer(constraints)
values = randomizer.next()
print(values)  # {'message_type': 'POST', 'priority': 'LOW'}
```

## Advanced Usage

### Mixed Constraint Types

```python
mixed_constraints = {
    # Constrained random
    'random_delay': ([(1, 10), (20, 30)], [0.8, 0.2]),
    
    # Sequence
    'sequence_delay': [5, 10, 15, 20],
    
    # Function with dependencies
    'computed_delay': lambda vals: vals.get('random_delay', 0) + 5,
    
    # Object selection
    'command_type': ([['READ'], ['WRITE', 'MODIFY']], [0.6, 0.4])
}

randomizer = FlexRandomizer(mixed_constraints)
```

### Dynamic Reconfiguration

```python
# Start with constrained random
constraints = {
    'delay': ([(1, 5), (10, 15)], [0.7, 0.3])
}
randomizer = FlexRandomizer(constraints)

# Switch to sequence mode
randomizer.set_sequence('delay', [2, 4, 6, 8])

# Switch to function mode
randomizer.set_generator('delay', lambda: random.choice([1, 5, 10]))

# Reset to original constraint
randomizer.reset_to_random('delay')
```

### Checking Constraint Types

```python
randomizer = FlexRandomizer({
    'field1': ([(1, 5)], [1]),
    'field2': [10, 20, 30],
    'field3': lambda: 42
})

print(randomizer.get_constraint_type('field1'))  # 'constrained_random'
print(randomizer.get_constraint_type('field2'))  # 'sequence'
print(randomizer.get_constraint_type('field3'))  # 'generator'
```

## Constraint Definition Reference

### Constrained Random Format

```python
# Format: (bins, weights)
'field_name': (
    [(min1, max1), (min2, max2), ...],  # List of (min, max) tuples
    [weight1, weight2, ...]             # Corresponding weights
)

# Examples:
'delay': ([(0, 5), (10, 20)], [0.8, 0.2])           # 80% 0-5, 20% 10-20
'cycles': ([(1, 1), (2, 4), (5, 10)], [5, 3, 2])    # Multi-bin with integer weights
```

### Object Bins Format

```python
# Format: (object_bins, weights)
'field_name': (
    [bin1, bin2, ...],      # Each bin can be a list/tuple of objects or single object
    [weight1, weight2, ...]  # Corresponding weights
)

# Examples:
'cmd': ([['READ', 'WRITE'], ['DELETE']], [0.9, 0.1])     # 90% READ/WRITE, 10% DELETE
'status': (['OK'], ['ERROR', 'TIMEOUT']], [0.8, 0.2])    # 80% OK, 20% ERROR/TIMEOUT
```

### Sequence Format

```python
# Format: List or tuple of values
'field_name': [value1, value2, value3, ...]

# Examples:
'pattern': [1, 2, 4, 8, 16]              # Powers of 2
'modes': ['IDLE', 'ACTIVE', 'SLEEP']     # String sequence
```

### Function Format

```python
# Format: Callable (with optional parameter)
'field_name': function

# Function signatures:
def no_params():
    return value

def with_params(current_values):
    # current_values is dict of all current field values
    return computed_value

# Examples:
'random_val': lambda: random.randint(1, 100)
'dependent': lambda vals: vals['other_field'] * 2
```

## Error Handling

FlexRandomizer provides detailed error messages with caller context:

```python
try:
    # Invalid constraint
    randomizer = FlexRandomizer({
        'bad_field': ([(1, 5)], [])  # Empty weights
    })
except ConstraintValidationError as e:
    print(f"Constraint error: {e}")
    # Shows filename, line number, and code context

try:
    values = randomizer.next()
except GeneratorError as e:
    print(f"Generation error: {e}")
```

## Best Practices

### 1. Constraint Validation

```python
# Good: Proper tuple format
'delay': ([(1, 5), (10, 15)], [0.7, 0.3])

# Bad: Wrong bracket types
'delay': ([[1, 5], [10, 15]], [0.7, 0.3])  # Should use () not []

# Good: Weights sum to positive number
'delay': ([(1, 5)], [0.5])

# Bad: Zero weight sum
'delay': ([(1, 5)], [0])
```

### 2. Thread Safety

```python
# FlexRandomizer is thread-safe
import threading

randomizer = FlexRandomizer(constraints)

def worker():
    for _ in range(100):
        values = randomizer.next()
        # Process values...

# Safe to use from multiple threads
threads = [threading.Thread(target=worker) for _ in range(4)]
for t in threads:
    t.start()
```

### 3. Function Dependencies

```python
# Ensure dependencies are generated first in constraint order
constraints = {
    'base_delay': ([(1, 10)], [1]),
    'derived_delay': lambda vals: vals.get('base_delay', 0) * 2
}

# FlexRandomizer handles dependency order automatically
randomizer = FlexRandomizer(constraints)
```

### 4. Naming Conventions

```python
# Use descriptive, valid field names
constraints = {
    'clock_delay': ...,        # Good: descriptive
    'data_setup_time': ...,    # Good: underscores OK
    'addr-phase-delay': ...,   # Good: hyphens OK
    '': ...,                   # Bad: empty name
    'field with spaces': ...,  # Bad: spaces not allowed
}
```

## API Reference

### Constructor

```python
FlexRandomizer(constraints: Dict[str, Union[Tuple, List, Callable]])
```

### Core Methods

- `next() -> Dict[str, Any]`: Generate next set of values
- `is_rand(name: str) -> bool`: Check if field uses constrained random
- `get_constraint_type(name: str) -> str`: Get current constraint type
- `get_field_names() -> List[str]`: Get all field names

### Dynamic Configuration

- `set_sequence(name: str, sequence: List[Any])`: Switch field to sequence mode
- `set_generator(name: str, generator: Callable)`: Switch field to function mode  
- `reset_to_random(name: str)`: Reset field to original constraint

### Utility Methods

- `__str__()`: Human-readable representation
- `__repr__()`: Debug representation

## Examples Repository

### Protocol Timing Example

```python
# APB protocol timing
apb_constraints = {
    'psel_delay': ([(0, 0), (1, 3)], [0.8, 0.2]),      # Mostly back-to-back
    'penable_delay': ([(1, 1), (2, 5)], [0.9, 0.1]),   # Usually 1 cycle
    'pready_cycles': [1, 2, 3, 1, 1],                   # Varied ready timing
    'error_inject': lambda: random.choice([False] * 19 + [True])  # 5% error rate
}

randomizer = FlexRandomizer(apb_constraints)
```

### Memory Controller Example

```python
# Memory controller patterns
memory_constraints = {
    'refresh_period': [64, 64, 64, 32],  # Mostly standard, occasional fast
    'cas_latency': ([(3, 3), (4, 5)], [0.7, 0.3]),
    'burst_length': ([['4'], ['8', '16']], [0.8, 0.2]),
    'bank_delay': lambda vals: 2 if vals.get('cas_latency', 3) > 3 else 1
}

randomizer = FlexRandomizer(memory_constraints)
```

This documentation covers the complete FlexRandomizer API with practical examples for protocol verification use cases.