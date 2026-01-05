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

# gaxi_sequence.py

Enhanced GAXI sequence generator leveraging shared infrastructure for creating complex test patterns with dependency tracking, randomization, and built-in packet field masking.

## Overview

The `GAXISequence` class provides:
- **Enhanced sequence generation** using existing infrastructure
- **FlexRandomizer integration** for value generation and constraints
- **Built-in packet field masking** (no custom implementation needed)
- **Standard dependency tracking** patterns
- **Performance optimization** for large field configurations
- **Multiple sequence types** (burst, pattern, randomized, dependency chains)

This simplified version eliminates custom field masking and uses existing infrastructure more effectively while preserving all existing APIs.

## Class

### GAXISequence

```python
class GAXISequence:
    def __init__(self, name="basic", field_config=None, packet_class=None, log=None)
```

**Parameters:**
- `name`: Sequence name for identification
- `field_config`: Field configuration (FieldConfig object or dictionary)
- `packet_class`: Packet class to use (defaults to GAXIPacket)
- `log`: Logger instance

**Performance Note:** The class automatically detects large field configurations (>50 bits) and uses optimized initialization to avoid performance issues.

## Core Methods

### Randomization Setup

#### `set_randomizer(constraints_dict)`
Set up randomizer for field value generation using FlexRandomizer.

**Parameters:**
- `constraints_dict`: Dictionary of field constraints for FlexRandomizer

**Returns:** Self for method chaining

```python
sequence = GAXISequence("randomized_test", field_config)

# Set up randomizer with constraints
sequence.set_randomizer({
    'data': ([(0x0000, 0xFFFF), (0x10000, 0x1FFFF)], [0.7, 0.3]),
    'addr': ([(0, 1023)], [1.0])
})
```

### Transaction Management

#### `add_transaction(field_values=None, delay=0, depends_on=None)`
Add a transaction to the sequence with automatic field masking.

**Parameters:**
- `field_values`: Dictionary of field values (automatically masked by Packet)
- `delay`: Delay after this transaction
- `depends_on`: Index of transaction this depends on (None for no dependency)

**Returns:** Index of added transaction for dependency tracking

```python
# Add basic transaction
index = sequence.add_transaction({
    'addr': 0x1000,
    'data': 0xDEADBEEF,
    'cmd': 0x2
}, delay=5)

# Add transaction with dependency
dependent_index = sequence.add_transaction({
    'addr': 0x2000,
    'data': 0xCAFEBABE
}, depends_on=index)
```

#### `add_data_transaction(data, delay=0, depends_on=None)`
Add a simple data transaction.

**Parameters:**
- `data`: Data value (automatically masked by Packet class)
- `delay`: Delay after transaction
- `depends_on`: Index of transaction this depends on

**Returns:** Index of added transaction

```python
# Add data-only transactions
seq_index = sequence.add_data_transaction(0x12345678, delay=2)
next_index = sequence.add_data_transaction(0x87654321, depends_on=seq_index)
```

### Pattern Generation

#### `add_burst(count, start_data=0, data_step=1, delay=0, dependency_chain=False)`
Add a burst of transactions with incrementing data.

**Parameters:**
- `count`: Number of transactions in burst
- `start_data`: Starting data value
- `data_step`: Step between data values
- `delay`: Delay between transactions
- `dependency_chain`: If True, each transaction depends on the previous

**Returns:** List of transaction indexes

```python
# Add burst without dependencies
burst_indexes = sequence.add_burst(
    count=8,
    start_data=0x1000,
    data_step=0x100,
    delay=1
)

# Add burst with dependency chain
chain_indexes = sequence.add_burst(
    count=5,
    start_data=0x2000,
    data_step=4,
    dependency_chain=True  # Each depends on previous
)
```

#### `add_pattern(pattern_name, data_width=32, delay=0)`
Add common test patterns.

**Parameters:**
- `pattern_name`: Type of pattern ('walking_ones', 'walking_zeros', 'alternating')
- `data_width`: Width of data field
- `delay`: Delay between pattern transactions

**Returns:** List of transaction indexes

```python
# Add walking ones pattern
ones_indexes = sequence.add_pattern('walking_ones', data_width=32, delay=1)

# Add walking zeros pattern
zeros_indexes = sequence.add_pattern('walking_zeros', data_width=16, delay=2)

# Add alternating bit patterns
alt_indexes = sequence.add_pattern('alternating', data_width=32, delay=0)
```

### Randomized Transactions

#### `add_randomized_transaction(delay=0, depends_on=None, field_overrides=None)`
Add a transaction with randomized field values using FlexRandomizer.

**Parameters:**
- `delay`: Delay after transaction
- `depends_on`: Index of transaction this depends on
- `field_overrides`: Dictionary of field values to override random values

**Returns:** Index of added transaction

```python
# Must set randomizer first
sequence.set_randomizer({
    'addr': ([(0x1000, 0x8000)], [1.0]),
    'data': ([(0, 0xFFFFFFFF)], [1.0])
})

# Add randomized transaction
rand_index = sequence.add_randomized_transaction(
    delay=3,
    field_overrides={'cmd': 0x2}  # Override command to WRITE
)
```

#### `generate_packets_with_randomization(count)`
Generate packets with randomized values using FlexRandomizer.

**Parameters:**
- `count`: Number of packets to generate

**Returns:** List of packets with randomized field values

```python
# Generate random test packets
random_packets = sequence.generate_packets_with_randomization(count=20)
for packet in random_packets:
    print(f"Random: {packet.formatted(compact=True)}")
```

### Backward Compatibility Methods

#### `add_data_value(data, delay=0)`
Add a transaction with a data value - backward compatibility.

```python
index = sequence.add_data_value(0xDEADBEEF, delay=5)
```

#### `add_data_value_with_dependency(data, delay=0, depends_on_index=None, dependency_type="after")`
Add a data transaction that depends on completion of a previous transaction.

```python
base_index = sequence.add_data_value(0x1000)
dep_index = sequence.add_data_value_with_dependency(0x2000, depends_on_index=base_index)
```

#### `add_data_incrementing(count, data_start=0, data_step=1, delay=0)`
Add transactions with incrementing data values.

**Returns:** Tuple of (self, list of indexes) for method chaining

```python
seq, indexes = sequence.add_data_incrementing(
    count=10,
    data_start=0x1000,
    data_step=0x100,
    delay=2
)
```

### Pattern Convenience Methods

#### `add_walking_ones(data_width=32, delay=0)`
Add transactions with walking ones pattern.

```python
ones_indexes = sequence.add_walking_ones(data_width=32, delay=1)
```

#### `add_walking_zeros(data_width=32, delay=0)`
Add transactions with walking zeros pattern.

```python
zeros_indexes = sequence.add_walking_zeros(data_width=16, delay=2)
```

#### `add_alternating_bits(data_width=32, delay=0)`
Add transactions with alternating bit patterns.

```python
alt_indexes = sequence.add_alternating_bits(data_width=24, delay=1)
```

### Dependency Management

#### `add_burst_with_dependencies(count, data_start=0, data_step=1, delay=0, dependency_spacing=1)`
Add a burst where each transaction depends on a previous one.

**Parameters:**
- `count`: Number of transactions
- `data_start`: Starting data value
- `data_step`: Step size between data values
- `delay`: Delay between transactions
- `dependency_spacing`: How many transactions back to depend on

**Returns:** Tuple of (self, list of indexes)

```python
# Each transaction depends on the previous one
seq, chain_indexes = sequence.add_burst_with_dependencies(
    count=5,
    data_start=0x1000,
    dependency_spacing=1
)

# Each transaction depends on two transactions back
seq, spaced_indexes = sequence.add_burst_with_dependencies(
    count=10,
    dependency_spacing=2
)
```

#### `add_dependency_chain(count, data_start=0, data_step=1, delay=0)`
Add a chain where each transaction depends on the previous one.

```python
seq, chain_indexes = sequence.add_dependency_chain(
    count=8,
    data_start=0x2000,
    data_step=4
)
```

## Packet Generation

### `generate_packets(count=None)`
Generate packets from the sequence with dependency information.

**Parameters:**
- `count`: Number of packets to generate (None for all)

**Returns:** List of generated packets with dependency metadata

```python
# Generate all packets
all_packets = sequence.generate_packets()

# Generate first 10 packets
first_packets = sequence.generate_packets(count=10)

# Each packet includes dependency metadata
for packet in all_packets:
    if hasattr(packet, 'depends_on_index'):
        print(f"Packet {packet.sequence_index} depends on {packet.depends_on_index}")
```

## Dependency Analysis

### `get_dependency_order()`
Get the order in which transactions should be executed based on dependencies.

**Returns:** List of transaction indexes in dependency-resolved order

```python
# Get execution order
execution_order = sequence.get_dependency_order()
print(f"Execute transactions in order: {execution_order}")

# Generate packets in dependency order
ordered_packets = []
all_packets = sequence.generate_packets()
for index in execution_order:
    ordered_packets.append(all_packets[index])
```

### `validate_dependencies()`
Validate that all dependencies are resolvable.

**Returns:** True if valid, raises ValueError if invalid

```python
try:
    sequence.validate_dependencies()
    print("All dependencies are valid")
except ValueError as e:
    print(f"Dependency validation failed: {e}")
```

### `get_dependency_graph()`
Get a representation of the transaction dependencies.

**Returns:** Dictionary mapping transaction indexes to their dependencies

```python
dep_graph = sequence.get_dependency_graph()
print(f"Dependencies: {dep_graph['dependencies']}")
print(f"Transaction count: {dep_graph['transaction_count']}")
```

## Statistics and Information

### `get_stats()`
Get sequence generation statistics.

**Returns:** Dictionary with comprehensive statistics

```python
stats = sequence.get_stats()
print(f"Sequence length: {stats['sequence_length']}")
print(f"Dependencies: {stats['dependencies']}")
print(f"Dependency percentage: {stats.get('dependency_percentage', 0):.1f}%")
print(f"Uses randomization: {stats['uses_randomization']}")
```

### `reset()`
Reset sequence to empty state.

```python
sequence.reset()  # Clear all transactions and dependencies
```

### `__len__()`
Return number of transactions in sequence.

```python
transaction_count = len(sequence)
```

## Usage Patterns

### Basic Sequence Creation

```python
from CocoTBFramework.components.gaxi import GAXISequence
from CocoTBFramework.shared.field_config import FieldConfig

# Create field configuration
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))
field_config.add_field(FieldDefinition("cmd", 4, format="hex"))

# Create sequence
sequence = GAXISequence("basic_test", field_config)

# Add various transaction types
sequence.add_transaction({'addr': 0x1000, 'data': 0xDEADBEEF, 'cmd': 0x2})
sequence.add_data_transaction(0x12345678, delay=2)
sequence.add_burst(count=5, start_data=0x1000, data_step=0x100)

# Generate packets
packets = sequence.generate_packets()
print(f"Generated {len(packets)} packets")
```

### Randomized Sequence

```python
# Create sequence with randomization
sequence = GAXISequence("random_test", field_config)

# Set up randomizer
sequence.set_randomizer({
    'addr': ([(0x1000, 0x1FFF), (0x8000, 0x8FFF)], [0.7, 0.3]),
    'data': ([(0, 0xFFFF), (0x10000, 0xFFFFFFFF)], [0.5, 0.5]),
    'cmd': ([(0x1, 0x2)], [1.0])  # READ or WRITE only
})

# Add randomized transactions
for i in range(20):
    sequence.add_randomized_transaction(delay=random.randint(0, 5))

# Generate packets with random values
packets = sequence.generate_packets()
```

### Pattern-Based Testing

```python
# Create pattern sequence
pattern_sequence = GAXISequence("pattern_test", field_config)

# Add different test patterns
pattern_sequence.add_walking_ones(data_width=32, delay=1)
pattern_sequence.add_walking_zeros(data_width=32, delay=1)
pattern_sequence.add_alternating_bits(data_width=32, delay=2)

# Add custom patterns
custom_patterns = [0xAAAAAAAA, 0x55555555, 0xCCCCCCCC, 0x33333333]
for pattern in custom_patterns:
    pattern_sequence.add_data_transaction(pattern, delay=1)

packets = pattern_sequence.generate_packets()
print(f"Pattern sequence has {len(packets)} packets")
```

### Dependency Chain Testing

```python
# Create dependency sequence
dep_sequence = GAXISequence("dependency_test", field_config)

# Add initial transaction
base_index = dep_sequence.add_transaction({
    'addr': 0x1000,
    'data': 0x1,
    'cmd': 0x2  # WRITE
})

# Add chain of dependent transactions
for i in range(1, 10):
    dep_index = dep_sequence.add_transaction({
        'addr': 0x1000 + i*4,
        'data': i,
        'cmd': 0x2
    }, depends_on=base_index + i - 1)  # Depends on previous

# Validate dependencies
dep_sequence.validate_dependencies()

# Get execution order
order = dep_sequence.get_dependency_order()
print(f"Execution order: {order}")

# Generate packets in dependency order
packets = dep_sequence.generate_packets()
```

### Complex Mixed Sequence

```python
def create_complex_test_sequence(field_config):
    """Create a complex sequence with mixed transaction types"""
    sequence = GAXISequence("complex_test", field_config)
    
    # Set up randomizer for some transactions
    sequence.set_randomizer({
        'addr': ([(0x1000, 0x8000)], [1.0]),
        'data': ([(0, 0xFFFFFFFF)], [1.0])
    })
    
    # Phase 1: Initialization burst
    init_indexes = sequence.add_burst(
        count=4,
        start_data=0x10000000,
        data_step=0x100,
        delay=0
    )
    
    # Phase 2: Pattern testing (depends on init)
    pattern_start = sequence.add_walking_ones(data_width=32, delay=1)
    for idx in pattern_start[:3]:  # First 3 patterns depend on init
        sequence.sequence_data[idx] = (
            sequence.sequence_data[idx][0],  # field_values
            sequence.sequence_data[idx][1],  # delay
            init_indexes[-1]  # depends_on last init transaction
        )
    
    # Phase 3: Random transactions
    random_indexes = []
    for i in range(10):
        rand_idx = sequence.add_randomized_transaction(delay=2)
        random_indexes.append(rand_idx)
    
    # Phase 4: Cleanup (depends on random completion)
    cleanup_indexes = sequence.add_burst(
        count=3,
        start_data=0x99999999,
        dependency_chain=True
    )
    
    return sequence

# Create and use complex sequence
complex_seq = create_complex_test_sequence(field_config)
packets = complex_seq.generate_packets()

# Analyze sequence
stats = complex_seq.get_stats()
print(f"Complex sequence statistics: {stats}")
```

### Factory Methods

The class provides factory methods for common sequence types:

#### `create_burst_sequence(name, count, start_data=0, data_step=1, field_config=None, dependency_chain=False)`
Create a burst sequence with incrementing data.

```python
burst_seq = GAXISequence.create_burst_sequence(
    name="burst_test",
    count=16,
    start_data=0x1000,
    data_step=4,
    field_config=field_config,
    dependency_chain=True
)
```

#### `create_pattern_sequence(name, pattern_name, data_width=32, field_config=None)`
Create a sequence with test patterns.

```python
pattern_seq = GAXISequence.create_pattern_sequence(
    name="walking_ones_test",
    pattern_name="walking_ones",
    data_width=32,
    field_config=field_config
)
```

#### `create_randomized_sequence(name, constraints, count, field_config=None)`
Create a sequence with randomized values.

```python
random_seq = GAXISequence.create_randomized_sequence(
    name="random_test",
    constraints={
        'addr': ([(0x1000, 0x8000)], [1.0]),
        'data': ([(0, 0xFFFFFFFF)], [1.0])
    },
    count=50,
    field_config=field_config
)
```

#### `create_dependency_chain(name="dependency_chain", count=5, data_start=0, data_step=1, delay=0)`
Create a sequence with transactions forming a dependency chain.

```python
chain_seq = GAXISequence.create_dependency_chain(
    name="chain_test",
    count=8,
    data_start=0x2000,
    data_step=8,
    delay=1
)
```

## Performance Considerations

### Large Field Configurations
For field configurations with >50 total bits, the class automatically uses optimized initialization:

```python
# Automatically optimized for large configs
large_config = create_large_field_config()  # >50 bits
sequence = GAXISequence("large_test", large_config)  # Uses optimized mode
```

### Memory Usage
The class efficiently manages memory for large sequences:

```python
# Efficient for large sequences
large_sequence = GAXISequence("large", field_config)
for i in range(10000):
    large_sequence.add_data_transaction(i)
# Memory usage remains reasonable
```

## Error Handling

### Dependency Validation
```python
try:
    sequence.validate_dependencies()
except ValueError as e:
    print(f"Invalid dependencies: {e}")
    # Fix dependencies and retry
```

### Randomizer Errors
```python
try:
    sequence.add_randomized_transaction()
except ValueError as e:
    print(f"No randomizer set: {e}")
    # Set randomizer first
    sequence.set_randomizer(constraints)
```

### Field Validation
```python
# Field validation handled automatically by Packet class
sequence.add_transaction({'addr': 0x123456789})  # Automatically masked
```

## Best Practices

### 1. **Use Factory Methods for Common Patterns**
```python
# Prefer factory methods
burst_seq = GAXISequence.create_burst_sequence("test", 10, 0x1000)
# Over manual creation
```

### 2. **Validate Dependencies Early**
```python
# Validate after adding dependent transactions
sequence.add_burst_with_dependencies(count=5, dependency_spacing=1)
sequence.validate_dependencies()  # Catch errors early
```

### 3. **Use Randomization for Stress Testing**
```python
# Set up realistic randomization constraints
sequence.set_randomizer({
    'addr': ([(0x1000, 0x7FFF)], [1.0]),  # Valid address range
    'data': ([(0, 0xFFFFFFFF)], [1.0])     # Full data range
})
```

### 4. **Generate Packets in Dependency Order**
```python
# For dependency chains, use dependency order
order = sequence.get_dependency_order()
packets = sequence.generate_packets()
ordered_packets = [packets[i] for i in order]
```

### 5. **Monitor Sequence Statistics**
```python
# Check sequence health
stats = sequence.get_stats()
if stats['dependency_percentage'] > 50:
    print("Warning: High dependency ratio may affect parallelism")
```

The GAXISequence provides a powerful and flexible framework for creating comprehensive test patterns with dependency management, randomization, and performance optimization for GAXI protocol verification.