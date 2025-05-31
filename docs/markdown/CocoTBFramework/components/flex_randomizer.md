# FlexRandomizer

## Overview

The `FlexRandomizer` class provides a powerful, thread-safe, and flexible approach to constrained randomization in verification environments. It extends beyond simple range-based randomization to support sequences, custom generators, and object randomization, giving users fine-grained control over randomization strategies with comprehensive error handling and debugging capabilities.

## Key Features

- **Thread-Safe Operations**: All operations use proper locking for concurrent access
- **Robust Error Handling**: Comprehensive validation with detailed error messages
- **Multiple Constraint Types**: Supports constrained random, sequences, generators, and object bins
- **Dynamic Mode Switching**: Change randomization strategies at runtime
- **Debug Support**: Rich string representations for troubleshooting
- **Type Safety**: Full type hints and runtime validation
- **Weighted Distributions**: Fine control over probability distributions
- **Function Dependencies**: Generators can depend on other field values

## Exception Hierarchy

```python
FlexRandomizerError                 # Base exception
├── ConstraintValidationError       # Invalid constraint definitions
└── GeneratorError                  # Runtime generation failures
```

## Classes

### FlexRandomizer

The main thread-safe class that randomizes values based on specified constraints.

#### Constructor

```python
def __init__(self, constraints: Dict[str, Union[Tuple, List, Callable]])
```

**Parameters:**
- `constraints`: Dictionary defining constraints for each field
  - **Keys**: Field names (must be valid identifiers)
  - **Values**: One of four constraint types:

**Constraint Types:**

1. **Constrained Random**: `(bins, weights)` tuple
   - `bins`: List of `(min, max)` tuples for integer ranges, or lists of objects for discrete selection
   - `weights`: List of relative weights (must be non-negative, sum > 0)

2. **Object Bins**: `(bins, weights)` tuple with non-numeric content
   - `bins`: List of tuples/lists containing discrete objects (strings, complex objects, etc.)
   - `weights`: Corresponding probability weights

3. **Sequence Looping**: List or tuple of values
   - Values will be returned in cyclic order
   - Cannot be empty

4. **Function Generators**: Callable that returns a value
   - Can optionally accept `Dict[str, Any]` parameter with current field values
   - Must return a single value

**Raises:**
- `TypeError`: If constraints is not a dictionary
- `ValueError`: If constraints is empty or field names are invalid
- `ConstraintValidationError`: If any constraint definition is invalid

#### Core Methods

##### next() -> Dict[str, Any]

Generate the next set of random values according to all constraints.

**Returns:** Dictionary mapping field names to generated values

**Raises:** `GeneratorError` if any generator function fails

**Thread Safety:** Fully thread-safe with internal locking

```python
# Generate values
values = randomizer.next()
print(values)  # {'delay1': 15, 'delay2': 'GET', 'delay3': 42}
```

##### set_sequence(delay_name: str, sequence: List[Any]) -> None

Override a field to use sequence looping.

**Parameters:**
- `delay_name`: Field name to modify
- `sequence`: Non-empty list/tuple of values to cycle through

**Raises:**
- `ValueError`: If field name not found or sequence is empty
- `TypeError`: If sequence is not list/tuple

```python
# Convert to sequence mode
randomizer.set_sequence('clock_delay', [10, 20, 30, 40])
# Will cycle: 10 → 20 → 30 → 40 → 10 → 20 → ...
```

##### set_generator(delay_name: str, generator: Callable) -> None

Override a field to use a function generator.

**Parameters:**
- `delay_name`: Field name to modify  
- `generator`: Function returning next value (can accept current values dict)

**Raises:**
- `ValueError`: If field name not found
- `TypeError`: If generator is not callable

```python
# Dependent generator
randomizer.set_generator('data_delay', lambda vals: vals['clock_delay'] * 2)

# Independent generator  
randomizer.set_generator('random_id', lambda: random.randint(1000, 9999))
```

##### reset_to_random(delay_name: str) -> None

Reset a field back to its original constraint definition.

**Parameters:**
- `delay_name`: Field name to reset

**Raises:**
- `ValueError`: If field name not found
- `ConstraintValidationError`: If original constraint is somehow invalid

```python
# Reset back to original constrained random behavior
randomizer.reset_to_random('clock_delay')
```

#### Utility Methods

##### get_constraint_type(delay_name: str) -> str

Get the current active constraint type for a field.

**Returns:** One of: `'sequence'`, `'generator'`, `'object_bin'`, `'constrained_random'`, `'unknown'`

##### get_field_names() -> List[str]

Get all defined field names.

##### is_rand(delay_name: str) -> bool

Check if a field uses constrained randomization (integer ranges).

#### Debug Support

##### \_\_str\_\_() -> str

Human-readable representation showing current state:

```
FlexRandomizer with 3 fields:
  clock_delay: 15 [constrained_random] (random: 2 bins)
  data_delay: 30 [generator] (generator: <lambda>)
  message_type: GET [sequence] (sequence: ['GET', 'POST', 'PUT'])
```

##### \_\_repr\_\_() -> str

Detailed representation for debugging:

```python
FlexRandomizer(constraints={...}, sequences={...}, generators=[...], ...)
```

## Example Usage

### Basic Constrained Randomization

```python
from flex_randomizer import FlexRandomizer

# Define weighted random constraints
constraints = {
    # 70% chance of 5-10, 30% chance of 20-30
    'clock_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),
    
    # Three bins with different probabilities  
    'data_delay': ([(1, 5), (8, 12), (15, 20)], [0.5, 0.3, 0.2]),
    
    # Single bin (always 0-5)
    'reset_delay': ([(0, 5)], [1.0])
}

try:
    randomizer = FlexRandomizer(constraints)
    
    # Generate random values
    for i in range(5):
        values = randomizer.next()
        print(f"Set {i+1}: {values}")
        # Use values in testbench...
        
except ConstraintValidationError as e:
    print(f"Invalid constraints: {e}")
except GeneratorError as e:
    print(f"Generation failed: {e}")
```

### Object Bins (Non-Numeric Values)

```python
# Define constraints with various object types
constraints = {
    # Integer ranges (standard constrained random)
    'packet_size': ([(64, 128), (256, 512), (1024, 1500)], [0.5, 0.3, 0.2]),

    # String object bins - 70% HTTP methods, 30% WebDAV methods  
    'http_method': ([
        ('GET', 'POST', 'PUT', 'DELETE'),    # Common HTTP methods
        ('PROPFIND', 'PROPPATCH', 'MKCOL')   # WebDAV methods
    ], [0.7, 0.3]),

    # Complex object bins (tuples representing transactions)
    'transaction_type': ([
        [('read', 4), ('read', 8), ('read', 16)],     # Read transactions
        [('write', 4), ('write', 8)],                 # Write transactions  
        [('atomic_swap', 8)]                          # Special operations
    ], [0.6, 0.3, 0.1]),
    
    # Mixed type bins
    'test_mode': ([
        ['normal', 'stress'],           # String modes
        [1, 2, 3],                     # Numeric modes
        [True, False]                  # Boolean modes  
    ], [0.5, 0.3, 0.2])
}

randomizer = FlexRandomizer(constraints)

for i in range(3):
    values = randomizer.next()
    print(f"Generated: {values}")
    
    # Use the values
    if values['http_method'] in ['GET', 'POST']:
        print(f"  Processing standard HTTP {values['http_method']}")
    elif isinstance(values['test_mode'], bool):
        print(f"  Boolean test mode: {values['test_mode']}")
```

### Sequence Looping

```python
# Start with random, then switch to sequence
timing_randomizer = FlexRandomizer({
    'clock_period': ([(10, 20), (30, 50)], [0.8, 0.2]),
    'phase_delay': ([(1, 5)], [1.0])
})

# Run with random values
print("Random phase:")
for i in range(3):
    print(f"  {timing_randomizer.next()}")

# Switch to deterministic sequence for specific test
timing_randomizer.set_sequence('clock_period', [15, 15, 20, 20, 25, 25])

print("\nSequence phase:")
for i in range(8):  # More than sequence length to show cycling
    values = timing_randomizer.next()
    print(f"  Period: {values['clock_period']}")  # Will cycle through sequence
```

### Function Generators with Dependencies

```python
# Create interdependent timing constraints
timing_constraints = {
    'clock_freq': ([(100, 200), (300, 500)], [0.6, 0.4]),  # MHz
    'setup_time': ([(1, 3)], [1.0]),                       # ns
    'hold_time': ([(1, 2)], [1.0])                         # ns
}

timing_rand = FlexRandomizer(timing_constraints)

# Make hold_time depend on setup_time (must be at least half)
timing_rand.set_generator('hold_time', 
    lambda vals: max(1, vals['setup_time'] // 2))

# Add computed clock period based on frequency
timing_rand.set_generator('clock_period',
    lambda vals: 1000 / vals['clock_freq'])  # Convert MHz to ns

print("Interdependent timing:")
for i in range(3):
    timing = timing_rand.next()
    print(f"  Freq: {timing['clock_freq']}MHz, "
          f"Period: {timing['clock_period']:.2f}ns, "
          f"Setup: {timing['setup_time']}ns, "
          f"Hold: {timing['hold_time']}ns")
```

### Error Handling and Validation

```python
# Example of comprehensive error handling
def create_safe_randomizer(constraints):
    try:
        return FlexRandomizer(constraints)
    except TypeError as e:
        print(f"Type error: {e}")
        return None
    except ValueError as e:
        print(f"Value error: {e}")
        return None
    except ConstraintValidationError as e:
        print(f"Constraint validation failed: {e}")
        return None

# Invalid constraints that will be caught
invalid_constraints = [
    # Empty constraints
    {},
    
    # Invalid field names
    {"": ([(1, 5)], [1.0])},
    {"123invalid": ([(1, 5)], [1.0])},
    
    # Mismatched bins and weights
    {"delay": ([(1, 5), (10, 15)], [1.0])},  # 2 bins, 1 weight
    
    # Invalid ranges
    {"delay": ([(10, 5)], [1.0])},  # min > max
    
    # Empty sequences
    {"delay": []},
    
    # Invalid weights
    {"delay": ([(1, 5)], [-1.0])},  # negative weight
    {"delay": ([(1, 5)], [0.0])},   # zero sum
]

for i, constraints in enumerate(invalid_constraints):
    print(f"Testing invalid constraint set {i+1}:")
    randomizer = create_safe_randomizer(constraints)
    if randomizer is None:
        print("  Correctly rejected")
    else:
        print("  ERROR: Should have been rejected!")
```

### Advanced Usage: Testbench Integration

```python
class TimingTestbench:
    def __init__(self):
        # Define comprehensive timing constraints
        self.timing_constraints = {
            # Clock timing with multiple frequency bands
            'clk_period': ([
                (8, 12),    # High speed: 83-125 MHz
                (20, 30),   # Medium speed: 33-50 MHz  
                (40, 60)    # Low speed: 16-25 MHz
            ], [0.5, 0.3, 0.2]),
            
            # Setup/hold times as percentage of clock period
            'setup_ratio': ([(10, 20), (25, 35)], [0.8, 0.2]),  # 10-35% of period
            'hold_ratio': ([(5, 15)], [1.0]),                   # 5-15% of period
            
            # Test patterns  
            'test_pattern': [
                'all_zeros', 'all_ones', 'checkerboard', 
                'walking_ones', 'walking_zeros', 'random'
            ],
            
            # Error injection rate (errors per 1000 cycles)
            'error_rate': ([(0, 1), (2, 5), (10, 20)], [0.7, 0.2, 0.1])
        }
        
        self.randomizer = FlexRandomizer(self.timing_constraints)
        
        # Set up dependent generators
        self.randomizer.set_generator('setup_time',
            lambda vals: (vals['clk_period'] * vals['setup_ratio']) // 100)
        self.randomizer.set_generator('hold_time', 
            lambda vals: (vals['clk_period'] * vals['hold_ratio']) // 100)
    
    def run_test_phase(self, phase_name: str, num_cycles: int):
        print(f"\n=== {phase_name} ===")
        
        for cycle in range(num_cycles):
            try:
                timing = self.randomizer.next()
                
                # Show current configuration  
                if cycle == 0 or cycle % 10 == 0:
                    print(f"Cycle {cycle}: {timing}")
                
                # Use timing in actual test
                self.apply_timing(timing)
                
            except GeneratorError as e:
                print(f"ERROR in cycle {cycle}: {e}")
                break
    
    def apply_timing(self, timing):
        # Simulate applying timing to testbench
        # In real code, this would configure the DUT
        pass
    
    def run_comprehensive_test(self):
        # Phase 1: Fully random
        print("Phase 1: Fully random timing")
        self.run_test_phase("Random Timing", 5)
        
        # Phase 2: Fixed pattern sequence for reproducibility
        print(f"\nCurrent randomizer state:\n{self.randomizer}")
        
        self.randomizer.set_sequence('test_pattern', 
            ['all_zeros', 'all_ones', 'checkerboard'])
        self.run_test_phase("Fixed Pattern Sequence", 6)
        
        # Phase 3: Stress test with fixed high-speed timing
        self.randomizer.set_sequence('clk_period', [8, 8, 8])  # High speed
        self.randomizer.set_generator('error_rate', lambda: 0)  # No errors
        self.run_test_phase("High-Speed Stress Test", 3)
        
        # Phase 4: Reset to random for coverage
        self.randomizer.reset_to_random('clk_period')
        self.randomizer.reset_to_random('test_pattern')
        self.randomizer.reset_to_random('error_rate')
        self.run_test_phase("Coverage Collection", 5)

# Run the testbench
if __name__ == "__main__":
    testbench = TimingTestbench()
    testbench.run_comprehensive_test()
```

### Debug and Introspection

```python
# Create a randomizer for debugging
debug_constraints = {
    'mode': (['fast', 'normal', 'slow'], [0.2, 0.6, 0.2]),
    'size': ([(1, 10), (50, 100)], [0.7, 0.3]),
    'enable': [True, False, True, False]  # Sequence
}

randomizer = FlexRandomizer(debug_constraints)

# Add a generator
randomizer.set_generator('computed', lambda vals: vals['size'] * 10)

# Inspect the randomizer state
print("=== Randomizer Debug Info ===")
print(f"String representation:\n{randomizer}\n")
print(f"Detailed representation:\n{repr(randomizer)}\n")

# Check individual field types
for field in randomizer.get_field_names():
    constraint_type = randomizer.get_constraint_type(field)
    is_random = randomizer.is_rand(field)
    print(f"Field '{field}': type={constraint_type}, is_rand={is_random}")

# Generate some values and show state changes
print("\n=== Generation Sequence ===")
for i in range(3):
    values = randomizer.next()
    print(f"Iteration {i+1}: {values}")
    # Note: enable field will cycle through sequence: True, False, True, False, ...
```

## Thread Safety

The `FlexRandomizer` class is designed to be thread-safe:

- All public methods use `threading.RLock()` for internal synchronization
- State modifications are atomic within lock boundaries  
- Multiple threads can safely call `next()` and other methods concurrently
- Generator functions should be thread-safe if used in concurrent environments

```python
import threading
import time

# Thread-safe usage example
randomizer = FlexRandomizer({
    'thread_id': ([(1, 100)], [1.0]),
    'delay': ([(10, 50)], [1.0])
})

def worker(thread_num, iterations):
    for i in range(iterations):
        values = randomizer.next()
        print(f"Thread {thread_num}, iter {i}: {values}")
        time.sleep(0.1)

# Start multiple threads
threads = []
for t in range(3):
    thread = threading.Thread(target=worker, args=(t, 5))
    threads.append(thread)
    thread.start()

# Wait for completion
for thread in threads:
    thread.join()
```

## Performance Considerations

- **Constraint Validation**: Performed once during initialization
- **Lock Overhead**: Minimal due to `RLock` and scoped locking
- **Memory Usage**: Sequences stored as `deque` for efficient rotation
- **Generator Calls**: Function call overhead depends on generator complexity

## Error Handling Best Practices

1. **Validate Constraints Early**: Check constraint definitions during development
2. **Handle Generator Errors**: Wrap generator functions in try/catch
3. **Use Type Hints**: Leverage static analysis to catch issues
4. **Test Edge Cases**: Empty sequences, extreme values, etc.
5. **Monitor State**: Use debug representations for troubleshooting

## Comparison with Other Randomization Approaches

| Feature | FlexRandomizer | Simple Random | ConstrainedRandom |
|---------|----------------|---------------|-------------------|
| Thread Safety | ✅ Built-in | ❌ Manual | ❌ Manual |
| Error Handling | ✅ Comprehensive | ❌ Basic | ⚠️ Limited |
| Object Support | ✅ Full | ❌ No | ❌ No |
| Dependencies | ✅ Function generators | ❌ No | ❌ No |
| Debug Support | ✅ Rich representations | ❌ No | ⚠️ Basic |
| Sequence Support | ✅ Built-in | ❌ Manual | ❌ Manual |

## See Also

- [ConstrainedRandom](constrained_random.md) - Simpler constrained randomization
- [RandomizationConfig](randomization_config.md) - Higher-level configuration framework  
- [Packet](packet.md) - Can use FlexRandomizer for field generation

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)