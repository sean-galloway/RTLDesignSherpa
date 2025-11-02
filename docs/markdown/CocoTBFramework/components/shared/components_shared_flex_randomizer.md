# flex_randomizer.py

Comprehensive randomization engine that supports multiple constraint types including constrained random, sequence looping, and function-based generation. Designed for thread-safe operation in concurrent verification environments.

## Overview

FlexRandomizer provides a flexible randomization framework that goes beyond simple constrained random to support sequences, custom generators, and object bins. It's designed to handle complex verification scenarios while maintaining thread safety and comprehensive error reporting.

## Exception Classes

### `FlexRandomizerError`
Base exception class for FlexRandomizer errors.

### `ConstraintValidationError`
Raised when constraint validation fails during initialization.

### `GeneratorError`
Raised when a generator function fails during value generation.

## Core Class

### FlexRandomizer

Main randomization class supporting multiple constraint types with thread-safe operations.

#### Constructor

```python
FlexRandomizer(constraints: Dict[str, Union[Tuple, List, Callable]])
```

**Parameters:**
- `constraints`: Dictionary defining constraints for each field. Values can be:
  - **Tuple (bins, weights)**: For constrained random generation
  - **List/Tuple**: For sequence looping (rotates through values)
  - **Callable**: For function-based generation

**Constraint Types:**

1. **Constrained Random**: `(bins, weights)`
   - `bins`: List of tuples `(min, max)` for integer ranges, or list of tuples/lists for object selection
   - `weights`: List of relative weights (must sum to > 0)

2. **Sequence Looping**: `[value1, value2, value3, ...]`
   - Rotates through values in order: 1, 2, 3, 1, 2, 3, ...

3. **Function Generators**: `callable`
   - Can optionally accept dict of current values as parameter
   - Should return a single value

```python
# Example constraints
constraints = {
    # Constrained random with 70% chance of 5-10, 30% chance of 20-30
    'delay1': ([(5, 10), (20, 30)], [0.7, 0.3]),
    
    # Object bins - choose from discrete string values
    'message_type': ([('GET', 'POST'), ('DELETE',)], [0.8, 0.2]),
    
    # Sequence that loops: 1, 2, 3, 1, 2, 3, ...
    'sequence_val': [1, 2, 3],
    
    # Function generator
    'computed_val': lambda vals: vals.get('delay1', 0) * 2
}

randomizer = FlexRandomizer(constraints)
```

#### Methods

##### `next() -> Dict[str, Any]`
Generate and set values for all fields based on their constraint types.

**Returns:** Dictionary containing the generated values for each field

**Thread Safety:** This method is thread-safe and can be called from multiple threads

```python
values = randomizer.next()
print(values)  # {'delay1': 7, 'message_type': 'GET', 'sequence_val': 1, 'computed_val': 14}

values = randomizer.next()
print(values)  # {'delay1': 22, 'message_type': 'POST', 'sequence_val': 2, 'computed_val': 44}
```

##### `set_sequence(delay_name: str, sequence: List[Any])`
Convert a field to use a looping sequence.

**Parameters:**
- `delay_name`: Name of the field to modify
- `sequence`: Sequence of values to loop through (must be non-empty)

```python
randomizer.set_sequence('clock_delay', [10, 20, 30])
# Now clock_delay will cycle: 10, 20, 30, 10, 20, 30, ...
```

##### `set_generator(delay_name: str, generator: Callable)`
Convert a field to use a function-based generator.

**Parameters:**
- `delay_name`: Name of the field to modify
- `generator`: Function that returns the next value (can optionally accept current values dict)

```python
# Make data_delay always be twice the clock_delay
randomizer.set_generator('data_delay', lambda vals: vals['clock_delay'] * 2)

# Use a parameterless generator
randomizer.set_generator('random_delay', lambda: random.randint(1, 100))
```

##### `reset_to_random(delay_name: str)`
Reset a field back to using its original constraint definition.

```python
# Reset field back to its original constrained random behavior
randomizer.reset_to_random('clock_delay')
```

##### `get_constraint_type(delay_name: str) -> str`
Get the current constraint type for a field.

**Returns:** String describing the constraint type: 'sequence', 'generator', 'object_bin', 'constrained_random', or 'unknown'

```python
constraint_type = randomizer.get_constraint_type('delay1')
print(f"delay1 uses {constraint_type} constraints")
```

##### `get_field_names() -> List[str]`
Get a list of all field names.

```python
fields = randomizer.get_field_names()
print(f"Available fields: {fields}")
```

##### `is_rand(name: str) -> bool`
Check if a field is set for constrained randomization.

```python
if randomizer.is_rand('delay1'):
    print("delay1 uses constrained randomization")
```

## Constraint Types in Detail

### 1. Constrained Random

#### Integer Range Bins
```python
constraints = {
    'address': ([(0x1000, 0x1FFF), (0x2000, 0x2FFF)], [0.7, 0.3]),
    'data': ([(0, 255), (256, 1023), (1024, 4095)], [0.5, 0.3, 0.2])
}
```

#### Object Bins
```python
constraints = {
    # HTTP methods with different probabilities
    'http_method': ([('GET', 'POST'), ('PUT',), ('DELETE',)], [0.7, 0.2, 0.1]),
    
    # Protocol states
    'state': ([('IDLE', 'ACTIVE'), ('ERROR', 'RESET')], [0.8, 0.2]),
    
    # Boolean values
    'enable': ([(True,), (False,)], [0.9, 0.1])
}
```

### 2. Sequence Looping

#### Fixed Sequences
```python
constraints = {
    'burst_length': [1, 2, 4, 8],        # Cycles: 1, 2, 4, 8, 1, 2, 4, 8, ...
    'test_pattern': [0xAA, 0x55, 0xFF, 0x00],  # Test patterns
    'priority': ['LOW', 'MEDIUM', 'HIGH'] # Priority levels
}
```

#### Dynamic Sequence Changes
```python
# Start with one sequence
randomizer = FlexRandomizer({'counter': [1, 2, 3]})

# Change sequence later
randomizer.set_sequence('counter', [10, 20, 30, 40])
```

### 3. Function Generators

#### Simple Generators
```python
import random

constraints = {
    'timestamp': lambda: int(time.time()),
    'random_id': lambda: random.randint(1000, 9999),
    'guid': lambda: str(uuid.uuid4())
}
```

#### Dependent Generators
```python
constraints = {
    'base_delay': ([(1, 10)], [1.0]),
    'dependent_delay': lambda vals: vals.get('base_delay', 0) + random.randint(0, 5),
    'total_delay': lambda vals: vals.get('base_delay', 0) + vals.get('dependent_delay', 0)
}
```

#### Complex Generators
```python
def address_generator(current_values):
    """Generate addresses based on current transaction type"""
    txn_type = current_values.get('transaction_type', 'READ')
    
    if txn_type == 'READ':
        return random.randint(0x1000, 0x1FFF)  # Read region
    elif txn_type == 'WRITE':
        return random.randint(0x2000, 0x2FFF)  # Write region
    else:
        return random.randint(0x3000, 0x3FFF)  # Special region

constraints = {
    'transaction_type': (['READ', 'write', 'special'], [0.5, 0.4, 0.1]),
    'address': address_generator
}
```

## Usage Patterns

### Basic Randomization

```python
# Define constraints
constraints = {
    'clock_delay': ([(0, 5), (10, 20)], [0.8, 0.2]),
    'data_delay': ([(1, 3), (5, 10)], [0.6, 0.4])
}

# Create randomizer
randomizer = FlexRandomizer(constraints)

# Generate values
for i in range(10):
    values = randomizer.next()
    print(f"Iteration {i}: clock={values['clock_delay']}, data={values['data_delay']}")
```

### Mixed Constraint Types

```python
# Complex constraint mix
constraints = {
    # Constrained random delay
    'setup_delay': ([(0, 0), (1, 5), (10, 20)], [0.5, 0.3, 0.2]),
    
    # Fixed sequence for burst lengths
    'burst_length': [1, 2, 4, 8],
    
    # Computed hold delay based on setup
    'hold_delay': lambda vals: max(1, vals.get('setup_delay', 0) // 2),
    
    # Random transaction ID
    'transaction_id': lambda: random.randint(1000, 9999)
}

randomizer = FlexRandomizer(constraints)

# Use in test
for cycle in range(20):
    timing = randomizer.next()
    print(f"Cycle {cycle}: {timing}")
```

### Protocol-Specific Randomization

```python
class ProtocolRandomizer:
    def __init__(self):
        self.randomizer = FlexRandomizer({
            # Address alignment patterns
            'address': ([(0x1000, 0x1FFC, 4), (0x2000, 0x2FFC, 8)], [0.7, 0.3]),
            
            # Data patterns
            'data_pattern': ['incremental', 'random', 'fixed', 'alternating'],
            
            # Transaction type with dependencies
            'txn_type': (['READ', 'write', 'rmw'], [0.4, 0.4, 0.2]),
            
            # Size based on transaction type
            'transfer_size': self._size_generator
        })
    
    def _size_generator(self, current_values):
        txn_type = current_values.get('txn_type', 'read')
        if txn_type == 'rmw':
            return random.choice([4, 8])  # RMW limited to word/dword
        else:
            return random.choice([1, 2, 4, 8, 16])  # Full range
    
    def generate_transaction(self):
        base_values = self.randomizer.next()
        
        # Post-process based on constraints
        if base_values['data_pattern'] == 'incremental':
            base_values['data'] = self._generate_incremental_data(base_values['transfer_size'])
        elif base_values['data_pattern'] == 'fixed':
            base_values['data'] = 0xDEADBEEF
        # ... handle other patterns
        
        return base_values
```

### Adaptive Randomization

```python
class AdaptiveRandomizer:
    def __init__(self):
        self.randomizer = FlexRandomizer({
            'delay': ([(0, 0), (1, 5), (10, 50)], [0.6, 0.3, 0.1])
        })
        self.performance_history = []
        
    def next_with_adaptation(self):
        values = self.randomizer.next()
        
        # Adapt based on performance history
        if len(self.performance_history) > 10:
            avg_performance = sum(self.performance_history[-10:]) / 10
            
            if avg_performance < 0.5:  # Performance is low
                # Switch to faster pattern
                self.randomizer.set_sequence('delay', [0, 0, 0, 1])
            elif avg_performance > 0.9:  # Performance is high
                # Switch to stress pattern
                self.randomizer.reset_to_random('delay')
        
        return values
    
    def record_performance(self, performance_metric):
        self.performance_history.append(performance_metric)
        # Keep only recent history
        if len(self.performance_history) > 100:
            self.performance_history = self.performance_history[-50:]
```

### Thread-Safe Usage

```python
import threading
import queue

class ThreadSafeRandomizerPool:
    def __init__(self, constraints, num_threads=4):
        # Single randomizer shared across threads (thread-safe)
        self.randomizer = FlexRandomizer(constraints)
        self.results_queue = queue.Queue()
        
    def worker_thread(self, thread_id, num_iterations):
        """Worker thread that generates random values"""
        for i in range(num_iterations):
            values = self.randomizer.next()  # Thread-safe call
            self.results_queue.put((thread_id, i, values))
    
    def run_parallel_generation(self, num_threads=4, iterations_per_thread=100):
        threads = []
        
        # Start worker threads
        for thread_id in range(num_threads):
            thread = threading.Thread(
                target=self.worker_thread,
                args=(thread_id, iterations_per_thread)
            )
            threads.append(thread)
            thread.start()
        
        # Wait for completion
        for thread in threads:
            thread.join()
        
        # Collect results
        results = []
        while not self.results_queue.empty():
            results.append(self.results_queue.get())
        
        return results

# Usage
constraints = {'delay': ([(0, 10), (20, 50)], [0.7, 0.3])}
pool = ThreadSafeRandomizerPool(constraints)
results = pool.run_parallel_generation(num_threads=8, iterations_per_thread=1000)
```

## Error Handling

### Constraint Validation Errors

```python
try:
    # Invalid constraint - weights don't match bins
    invalid_constraints = {
        'bad_field': ([(0, 10), (20, 30)], [0.5])  # 2 bins, 1 weight
    }
    randomizer = FlexRandomizer(invalid_constraints)
except ConstraintValidationError as e:
    print(f"Constraint validation failed: {e}")
    # Error includes caller information for debugging
```

### Generator Function Errors

```python
def problematic_generator(current_values):
    # This will cause a GeneratorError
    return current_values['nonexistent_field'] / 0

constraints = {
    'good_field': ([(1, 10)], [1.0]),
    'bad_field': problematic_generator
}

randomizer = FlexRandomizer(constraints)

try:
    values = randomizer.next()
except GeneratorError as e:
    print(f"Generator function failed: {e}")
    # Randomizer continues to work for other fields
```

### Robust Error Handling Pattern

```python
class RobustRandomizer:
    def __init__(self, constraints):
        try:
            self.randomizer = FlexRandomizer(constraints)
            self.fallback_values = {}
            self.error_count = 0
        except ConstraintValidationError as e:
            print(f"Failed to create randomizer: {e}")
            raise
    
    def safe_next(self, fallback_values=None):
        """Generate values with fallback on errors"""
        try:
            return self.randomizer.next()
        except GeneratorError as e:
            self.error_count += 1
            print(f"Generator error (#{self.error_count}): {e}")
            
            # Return fallback values
            if fallback_values:
                return fallback_values
            else:
                return self.fallback_values
    
    def set_fallback_values(self, **values):
        """Set fallback values for error conditions"""
        self.fallback_values.update(values)
```

## Advanced Features

### Dynamic Constraint Modification

```python
# Start with basic constraints
randomizer = FlexRandomizer({
    'delay': ([(0, 5)], [1.0]),
    'enable': [True, False]
})

# Modify constraints based on test phase
def setup_phase():
    randomizer.set_sequence('delay', [10, 15, 20])  # Slow during setup
    randomizer.set_sequence('enable', [True])       # Always enabled

def test_phase():
    randomizer.reset_to_random('delay')             # Random during test
    randomizer.reset_to_random('enable')            # Random enable

def cleanup_phase():
    randomizer.set_sequence('delay', [0, 0, 0, 5])  # Mostly fast cleanup
    randomizer.set_sequence('enable', [False])      # Always disabled
```

### Statistical Analysis

```python
def analyze_randomizer_distribution(randomizer, field_name, num_samples=10000):
    """Analyze the distribution of a randomized field"""
    samples = []
    for _ in range(num_samples):
        values = randomizer.next()
        samples.append(values[field_name])
    
    # Calculate statistics
    from collections import Counter
    distribution = Counter(samples)
    
    stats = {
        'samples': num_samples,
        'unique_values': len(distribution),
        'min_value': min(samples),
        'max_value': max(samples),
        'distribution': dict(distribution),
        'most_common': distribution.most_common(5)
    }
    
    return stats

# Usage
constraints = {'test_field': ([(0, 5), (10, 15)], [0.7, 0.3])}
randomizer = FlexRandomizer(constraints)
stats = analyze_randomizer_distribution(randomizer, 'test_field')
print(f"Distribution analysis: {stats}")
```

## Best Practices

### 1. **Validate Constraints Early**
Always validate your constraints when creating the randomizer:

```python
try:
    randomizer = FlexRandomizer(constraints)
except ConstraintValidationError as e:
    log.error(f"Invalid constraints: {e}")
    # Fix constraints and retry
```

### 2. **Use Meaningful Field Names**
Choose descriptive names that indicate purpose:

```python
constraints = {
    'setup_delay_cycles': ([(0, 5), (10, 20)], [0.8, 0.2]),
    'data_valid_probability': ([(0.7, 0.9)], [1.0]),
    'burst_transfer_length': [1, 2, 4, 8, 16]
}
```

### 3. **Document Complex Generators**
Add clear documentation for function generators:

```python
def address_alignment_generator(current_values):
    """
    Generate aligned addresses based on transfer size.
    Ensures addresses are properly aligned for the given transfer size.
    """
    transfer_size = current_values.get('transfer_size', 4)
    base_addr = random.randint(0x1000, 0x8000)
    return (base_addr // transfer_size) * transfer_size

constraints = {
    'transfer_size': [1, 2, 4, 8],
    'address': address_alignment_generator
}
```

### 4. **Handle Dependencies Carefully**
When using dependent generators, handle missing dependencies gracefully:

```python
def safe_dependent_generator(current_values):
    base_value = current_values.get('base_field', 0)  # Default to 0
    if base_value > 10:
        return base_value * 2
    else:
        return base_value + random.randint(1, 5)
```

### 5. **Use Type Checking**
Validate generator return types when possible:

```python
def validated_generator(current_values):
    result = some_complex_calculation(current_values)
    assert isinstance(result, int), f"Expected int, got {type(result)}"
    assert 0 <= result <= 1000, f"Result {result} out of valid range"
    return result
```

FlexRandomizer provides a powerful foundation for complex verification scenarios while maintaining simplicity for basic use cases. Its thread-safe design and comprehensive error handling make it suitable for both simple scripts and large-scale parallel verification environments.
