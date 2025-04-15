# Constrained Randomization Documentation

## Overview
The constrained randomization module provides components for generating random values with specific constraints, which is essential for modern verification environments. This module includes two primary classes:

1. `ConstrainedRandom`: A simple class for generating weighted random values from defined ranges
2. `FlexRandomizer`: An advanced randomization engine with multiple generation modes and customizable constraints

These components enable verification engineers to create directed random tests with precise control over the generated values.

## ConstrainedRandom Class

### Purpose
The `ConstrainedRandom` class provides a straightforward way to generate weighted random values from a set of predefined constraints.

### Class Definition
```python
class ConstrainedRandom:
    """Generates random values based on specified constraints and weights.

    This class allows for weighted random selection from a set of constraints,
    generating either integer or floating-point values within the chosen range.
    """
    def __init__(self, constraints, weights, is_integer=True):
        if len(constraints) != len(weights):
            raise ValueError("Constraints and weights must have the same length")

        self.constraints = constraints
        self.weights = weights
        self.random_generator = random.Random()
        self.is_integer = is_integer
```

### Key Methods

```python
def next(self):
    """Generate the next constrained random value.

    Returns:
        int or float: The next random value, either an integer or a float,
            depending on the is_integer flag.
    """
```
Generates the next random value based on the defined constraints and weights.

### Usage Example

```python
# Define constraints and weights
constraints = [(1, 10), (20, 30), (50, 100)]
weights = [0.7, 0.2, 0.1]  # 70% chance of 1-10, 20% chance of 20-30, 10% chance of 50-100

# Create constrained random generator
rand_gen = ConstrainedRandom(constraints, weights)

# Generate 10 random values
for i in range(10):
    value = rand_gen.next()
    print(f"Random value {i+1}: {value}")
```

## FlexRandomizer Class

### Purpose
The `FlexRandomizer` class provides a flexible, feature-rich randomization engine that supports multiple generation modes, including constrained random, sequence-based, and function-based generation.

### Class Definition
```python
class FlexRandomizer(Randomized):
    """Randomizes delays based on specified constraints.

    This class allows for constrained randomization of delays, ensuring
    that generated values fall within specified ranges and distributions.
    It also supports sequence looping and function-based generation.
    """

    def __init__(self, constraints: Dict):
        """Initialize the FlexRandomizer with delay constraints.

        Args:
            constraints (dict): A dictionary defining the constraints for each delay.
                The keys are the names of the delays, and the values can be:
                - Tuple (bins, weights): For constrained random generation
                    Bins can be either:
                    - List of tuples (min, max) for integer ranges
                    - List of tuples/lists of objects for selecting from discrete objects
                - List/Tuple: For sequence looping
                - Callable: For function-based generation
        """
```

### Key Features

#### Multiple Generation Modes
- **Constrained Random**: Generate random values from weighted bins
- **Sequence Looping**: Cycle through a predefined sequence of values
- **Function-Based**: Use custom functions to generate values
- **Object Bins**: Generate non-numeric objects from collections

#### Dynamic Configuration
```python
def set_sequence(self, delay_name: str, sequence: List):
    """Set a looping sequence for a specific delay."""
```
Configures a field to use sequence-based generation.

```python
def set_generator(self, delay_name: str, generator: Callable):
    """Set a generator function for a specific delay."""
```
Configures a field to use function-based generation.

```python
def reset_to_random(self, delay_name: str):
    """Reset a delay back to using constrained random values."""
```
Resets a field to use constrained random generation.

#### Interdependent Field Values
The function-based generators can create dependencies between fields by referring to other field values:

```python
# Create interdependent fields
constraints = {
    'a': ([(1, 10)], [1.0]),  # Field a: 1-10
    'b': lambda values: values['a'] * 2  # Field b: 2 times value of field a
}
```

### Usage Examples

#### Basic Constrained Random
```python
# Define constraints
constraints = {
    'clock_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),  # 70% chance of 5-10, 30% chance of 20-30
    'data_delay': ([(1, 5), (8, 12), (15, 20)], [0.5, 0.3, 0.2])  # Multiple bins with weights
}

# Create randomizer
flex_rand = FlexRandomizer(constraints)

# Generate values
for i in range(5):
    values = flex_rand.next()
    print(f"Iteration {i+1}: {values}")
```

#### Sequence-Based Generation
```python
# Create randomizer with initial constraints
flex_rand = FlexRandomizer({
    'clock_delay': ([(5, 10)], [1.0]),
    'data_delay': ([(1, 5)], [1.0])
})

# Convert clock_delay to use a sequence
clock_sequence = [5, 10, 15, 20, 25]
flex_rand.set_sequence('clock_delay', clock_sequence)

# Generate values
for i in range(8):
    values = flex_rand.next()
    print(f"Iteration {i+1}: {values}")
```

#### Function-Based Generation
```python
# Create randomizer
flex_rand = FlexRandomizer({
    'clock_delay': ([(5, 10), (20, 30)], [0.7, 0.3]),
    'data_delay': ([(1, 5)], [1.0])
})

# Set function-based generator for data_delay
flex_rand.set_generator('data_delay', lambda values: values['clock_delay'] * 2)

# Generate values
for i in range(5):
    values = flex_rand.next()
    print(f"Iteration {i+1}: {values}")
    print(f"  data_delay = clock_delay * 2: {values['data_delay']} = {values['clock_delay']} * 2")
```

#### Object Bins
```python
# Define constraints with object bins
constraints = {
    # String bins - each bin is a tuple of strings
    'message_type': ([('GET', 'PUT', 'POST'), ('DELETE', 'PATCH')], [0.7, 0.3]),
    
    # Complex object bins (using tuples for demonstration)
    'transaction': ([
        (('read', 4), ('read', 8)),    # Read transactions
        (('write', 4), ('write', 8))   # Write transactions
    ], [0.6, 0.4])
}

# Create randomizer
flex_rand = FlexRandomizer(constraints)

# Generate values
for i in range(5):
    values = flex_rand.next()
    print(f"Iteration {i+1}: message_type={values['message_type']}, transaction={values['transaction']}")
```

#### Mixed Generation Modes
```python
# Define constraints with different types
mixed_constraints = {
    'random_delay': ([(1, 10), (20, 30)], [0.8, 0.2]),  # Standard constrained random
    'sequence_delay': [5, 10, 15, 20],  # Sequence for looping
    'function_delay': lambda: random.randint(1, 100)  # Function generator
}

# Create randomizer
mixed_rand = FlexRandomizer(mixed_constraints)

# Generate values
for i in range(5):
    values = mixed_rand.next()
    print(f"Iteration {i+1}: {values}")
```

### Advanced Usage Patterns

#### Realistic Testing Scenario
```python
# Define timing constraints for a testbench
timing_constraints = {
    'clk_to_q': ([(2, 5), (6, 10)], [0.8, 0.2]),
    'setup_time': ([(1, 3)], [1.0]),
    'hold_time': ([(1, 2)], [1.0]),
    'clock_period': ([(10, 20), (30, 50)], [0.7, 0.3])
}

# Create timing randomizer
timing_rand = FlexRandomizer(timing_constraints)

# Run random tests
print("Running 3 iterations with fully random values:")
for i in range(3):
    timing = timing_rand.next()
    print(f"  Iteration {i+1}: {timing}")

# Fix clock period for stability tests
timing_rand.set_sequence('clock_period', [20, 20, 20, 20, 20])
print("Fixed clock_period to 20ns for stability tests")

# Make hold time dependent on setup time
timing_rand.set_generator('hold_time', lambda values: values['setup_time'] // 2)
print("Set hold_time to be half of setup_time")

# Run controlled tests
print("Running 3 iterations with partially controlled values:")
for i in range(3):
    timing = timing_rand.next()
    print(f"  Iteration {i+1}: {timing}")

# Reset to fully random for coverage testing
timing_rand.reset_to_random('clock_period')
timing_rand.reset_to_random('hold_time')
print("Reset to fully random for coverage testing")
```

## RandomizationConfig Class

The `RandomizationConfig` module extends the randomization capabilities with a more structured approach to field configuration, providing additional features for protocol verification.

### Key Components

#### RandomizationMode Enum
```python
class RandomizationMode(Enum):
    """Defines possible randomization modes."""
    DETERMINISTIC = auto()  # Fixed values, not random
    CONSTRAINED = auto()    # Constrained random with weights
    DIRECTED = auto()       # Directed test patterns
    SEQUENCE = auto()       # Sequence of values in order
    CUSTOM = auto()         # Custom generator function
```

#### FieldRandomizationConfig
```python
@dataclass
class FieldRandomizationConfig:
    """Configuration for randomizing a specific field."""
    enabled: bool = True
    mode: RandomizationMode = RandomizationMode.CONSTRAINED
    constraints: Optional[Dict] = None
    sequence: Optional[List[Any]] = None
    custom_generator: Optional[Callable] = None
    dependencies: List[str] = field(default_factory=list)
```

#### RandomizationConfig
```python
class RandomizationConfig:
    """
    Configuration for randomizing protocol fields.

    This class provides a flexible framework for configuring how
    protocol fields are randomized, using FlexRandomizer as the
    underlying randomization engine.
    """
```

### Key Features

- **Field-Specific Configuration**: Configure each field independently
- **Dependency Management**: Generate values based on dependencies between fields
- **Group-Based Configuration**: Configure multiple fields with the same settings
- **Topological Sorting**: Handle dependencies in the correct order
- **Factory Methods**: Easily create common constraint configurations
- **Multiple Generation Modes**: Support for all randomization modes from FlexRandomizer

### Usage Example

```python
# Create randomization configuration
config = RandomizationConfig("APB_Config")

# Configure fields individually
config.configure_field("addr", FieldRandomizationConfig(
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0x1000, 0x1FFF), (0x2000, 0x2FFF)],
        "weights": [0.7, 0.3]
    }
))

config.configure_field("data", FieldRandomizationConfig(
    mode=RandomizationMode.SEQUENCE,
    sequence=[0xA5A5, 0x5A5A, 0xFFFF, 0x0000]
))

# Create field dependencies
config.configure_field("prot", FieldRandomizationConfig(
    mode=RandomizationMode.CUSTOM,
    custom_generator=lambda values: 1 if values['addr'] >= 0x2000 else 0,
    dependencies=['addr']
))

# Create field groups
config.add_to_group("control", "strb")
config.add_to_group("control", "burst")
config.add_to_group("control", "lock")

# Configure groups
config.configure_group("control", 
                      mode=RandomizationMode.CONSTRAINED,
                      constraints={"bins": [(0, 3)], "weights": [1.0]})

# Generate values
fields = ["addr", "data", "prot", "strb", "burst", "lock"]
values = config.generate_values(fields)
print(values)
```

## Best Practices

1. **Choose the Right Tool**:
   - Use `ConstrainedRandom` for simple weighted random generation
   - Use `FlexRandomizer` for advanced features like sequences and function-based generation
   - Use `RandomizationConfig` for structured protocol verification

2. **Define Meaningful Constraints**:
   - Create realistic value distributions that match actual hardware behavior
   - Use weights to prioritize common or edge cases as needed
   - Consider the relationships between fields when defining constraints

3. **Use Multiple Generation Modes**:
   - Use constrained random for exploration
   - Use sequences for regression testing
   - Use function-based generation for correlated fields

4. **Manage Dependencies**:
   - Clearly identify dependencies between fields
   - Use the dependency resolution features of RandomizationConfig
   - Create validation functions that verify field combinations are valid

5. **Structure Test Phases**:
   - Start with fully random tests for exploration
   - Progress to more directed tests for targeted verification
   - Finish with specific sequences for regression testing

6. **Monitor Coverage**:
   - Track which values are generated to ensure coverage goals are met
   - Adjust weights based on coverage results
   - Use reset_to_random() to return to exploration mode as needed

7. **Performance Considerations**:
   - Reuse randomization configurations when possible
   - Use efficient generation modes for high-volume testing
   - Balance between randomization complexity and performance
