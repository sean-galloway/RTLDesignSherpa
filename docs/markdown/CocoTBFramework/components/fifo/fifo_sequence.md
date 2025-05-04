# FIFO Sequence Documentation

## Overview

`fifo_sequence.py` implements the FIFOSequence class, which generates and manages sequences of FIFO transactions for testing. It provides powerful capabilities for creating complex test patterns with transaction dependencies, value masking, and comprehensive test case generation.

## Class: FIFOSequence

```python
class FIFOSequence:
    """
    Generates sequences of FIFO transactions for testing with built-in masking
    and transaction dependency tracking.

    This class creates test patterns for FIFO transactions with dependency tracking,
    allowing for the creation of complex sequences where transactions depend on
    the completion of previous transactions.
    """
```

### Key Features

- **Transaction Sequence Generation**:
  - Create sequences of transactions with defined fields and values
  - Support for various data patterns (incrementing, walking bits, etc.)
  - Add delays between transactions
  
- **Transaction Dependency Tracking**:
  - Define transactions that depend on previous ones
  - Model complex dependency relationships
  - Support for different dependency types
  
- **FIFO State Modeling**:
  - Model FIFO depth and utilization
  - Simulate back-pressure and capacity constraints
  - Track realistic FIFO behavior
  
- **Value Masking**:
  - Automatically mask field values to match field bit widths
  - Track masked values for verification
  
- **Randomization Support**:
  - Random selection from sequences
  - Integration with FlexRandomizer for timing constraints
  
- **Built-in Test Patterns**:
  - Walking ones/zeros, alternating bits
  - Dependency chains, bursts
  - Capacity tests, stress tests

### Initialization

```python
def __init__(self, name="basic", field_config=None, packet_class=FIFOPacket):
    """
    Initialize the FIFO sequence.

    Args:
        name: Sequence name
        field_config: Field configuration (FieldConfig object or dictionary)
        packet_class: Class to use for packet creation
    """
```

### Key Methods

#### Transaction Addition

- **add_transaction(field_values=None, delay=0)**:
  Add a transaction to the sequence with automatic field value masking.
  
- **add_transaction_with_dependency(field_values=None, delay=0, depends_on_index=None, dependency_type="after")**:
  Add a transaction that depends on completion of a previous transaction.
  
- **add_data_value(data, delay=0)**:
  Add a transaction with a simple data value.
  
- **add_data_value_with_dependency(data, delay=0, depends_on_index=None, dependency_type="after")**:
  Add a data transaction that depends on a previous transaction.

- **add_delay(clocks)**:
  Add a delay to the sequence.

#### Sequence Configuration

- **set_random_selection(enable=True)**:
  Enable/disable random selection from sequences.
  
- **set_master_randomizer(randomizer)**:
  Set the randomizer to use for master timing constraints.
  
- **set_slave_randomizer(randomizer)**:
  Set the randomizer to use for slave timing constraints.
  
- **set_fifo_parameters(capacity=8, back_pressure=0.0)**:
  Set FIFO-specific parameters for more realistic sequence generation.

#### Sequence Iteration

- **reset_iterators()**:
  Reset all sequence iterators to the beginning.
  
- **next_field_value(field_name)**:
  Get the next value for a specific field from the sequence.
  
- **next_delay()**:
  Get the next delay value from the sequence.

#### FIFO State Modeling

- **update_fifo_depth(is_write=True, max_increment=1)**:
  Update the modeled FIFO depth based on operation.
  
- **should_apply_back_pressure()**:
  Determine if back pressure should be applied based on FIFO depth.

#### Packet Generation

- **generate_packet(apply_fifo_metadata=True)**:
  Generate the next packet in the sequence with FIFO metadata.
  
- **generate_packets(count=None, apply_fifo_metadata=True)**:
  Generate multiple packets.
  
- **get_packet(index=0)**:
  Get a specific packet from the generated list.

#### Information Retrieval

- **get_dependency_graph()**:
  Get a representation of the transaction dependencies.
  
- **get_stats()**:
  Get statistics about the sequence generation.
  
- **resolve_dependencies(completed_transactions=None)**:
  Determine which transactions are ready to execute based on dependencies.

#### Advanced Data Pattern Methods

- **add_data_incrementing(count, data_start=0, data_step=1, delay=0)**:
  Add transactions with incrementing data values.
  
- **add_data_pattern(patterns, delay=0)**:
  Add transactions with various data patterns.
  
- **add_walking_ones(data_width=32, delay=0)**:
  Add transactions with walking ones pattern.
  
- **add_walking_zeros(data_width=32, delay=0)**:
  Add transactions with walking zeros pattern.
  
- **add_alternating_bits(data_width=32, delay=0)**:
  Add transactions with alternating bit patterns.
  
- **add_random_data(count, data_mask=None, delay=0)**:
  Add transactions with random data.
  
- **add_burst_with_dependencies(count, data_start=0, data_step=1, delay=0, dependency_spacing=1)**:
  Add a burst of transactions where each one depends on a previous one.
  
- **add_dependency_chain(count, data_start=0, data_step=1, delay=0)**:
  Add a chain of transactions where each depends on the previous one.
  
- **add_fifo_stress_pattern(depth_targets=None, delay_range=None)**:
  Add a sequence designed to stress FIFO full/empty boundaries.

#### Factory Methods

- **create_dependency_chain(name, count, data_start, data_step, delay)**:
  Create a sequence with transactions forming a dependency chain.
  
- **create_burst_sequence(name, count, burst_size, pattern_type)**:
  Create a burst sequence with multiple write operations followed by multiple reads.
  
- **create_fifo_capacity_test(name, capacity)**:
  Create a sequence specifically designed to test FIFO capacity boundaries.
  
- **create_data_stress_test(name, data_width, delay)**:
  Create a comprehensive data stress test sequence.
  
- **create_timing_variation_test(name, data_width, capacity)**:
  Create a sequence with timing variations to test FIFO timing behavior.
  
- **create_comprehensive_test(name, capacity, data_width)**:
  Create a comprehensive test with many different patterns.

### Transaction Field Storage

The sequence stores field values in dictionaries indexed by field name:

```python
self.field_data_seq = {}  # Dictionary of field_name -> list of values
```

For a sequence with multiple transactions, the values for a specific field are stored as a list:

```python
self.field_data_seq['data'] = [0xA, 0xB, 0xC, 0xD]  # Values for 4 transactions
```

### Dependency Tracking

The sequence tracks dependencies between transactions using indices:

```python
self.dependencies = {}    # Maps transaction index -> dependency index
self.dependency_types = {} # Maps transaction index -> dependency type
```

For example, if transaction 3 depends on transaction 1:

```python
self.dependencies[3] = 1
self.dependency_types[3] = "after"  # Only proceed after txn 1 completes
```

### FIFO Modeling

The sequence includes built-in FIFO modeling:

```python
self.fifo_capacity = 8   # Default FIFO capacity for modeling
self.fifo_depth = 0      # Current modeled FIFO depth
self.back_pressure = 0.0  # Probability of back-pressure (0.0 to 1.0)
```

## Usage Examples

### Basic Sequence Creation

```python
# Create a field configuration
field_config = FieldConfig.create_data_only(32)

# Create a simple sequence
sequence = FIFOSequence("basic_test", field_config)
sequence.add_data_value(0xAAAAAAAA)
sequence.add_data_value(0x55555555)
sequence.add_data_value(0x33333333)
sequence.add_data_value(0xCCCCCCCC)

# Generate packets
packets = sequence.generate_packets()
for i, packet in enumerate(packets):
    print(f"Packet {i}: data=0x{packet.data:X}")
```

### Dependency Chain Sequence

```python
# Create a sequence with dependencies
sequence = FIFOSequence("dependency_chain", field_config)

# First transaction (base transaction)
base_idx = sequence.add_data_value(0x1000)

# Second transaction depends on first
idx2 = sequence.add_data_value_with_dependency(
    0x2000, 
    depends_on_index=base_idx
)

# Third transaction depends on second
idx3 = sequence.add_data_value_with_dependency(
    0x3000, 
    depends_on_index=idx2
)

# Generate packets with dependencies
packets = sequence.generate_packets()

# Get dependency graph
dep_graph = sequence.get_dependency_graph()
print(f"Dependencies: {dep_graph['dependencies']}")
```

### Using Built-in Pattern Methods

```python
# Create a sequence with various patterns
sequence = FIFOSequence("pattern_test", field_config)

# Add incrementing values
sequence, idx_list1 = sequence.add_data_incrementing(
    count=5, 
    data_start=0x100, 
    data_step=0x100
)

# Add walking ones pattern
sequence, idx_list2 = sequence.add_walking_ones(data_width=32)

# Add random data
sequence, idx_list3 = sequence.add_random_data(count=3)

# Generate packets
packets = sequence.generate_packets()
```

### Using Factory Methods

```python
# Create a dependency chain sequence
dep_chain = FIFOSequence.create_dependency_chain(
    name="dep_chain",
    count=5,
    data_start=0x1000,
    data_step=0x1000,
    delay=1
)

# Create a FIFO capacity test
capacity_test = FIFOSequence.create_fifo_capacity_test(
    name="capacity_test",
    capacity=8
)

# Create a comprehensive test
comprehensive = FIFOSequence.create_comprehensive_test(
    name="full_test",
    capacity=8,
    data_width=32
)
```

### Modeling FIFO State

```python
# Create a sequence with FIFO modeling
sequence = FIFOSequence("fifo_model", field_config)
sequence.set_fifo_parameters(capacity=8, back_pressure=0.3)

# Add transactions
for i in range(10):
    # Check if back pressure would be applied
    if sequence.should_apply_back_pressure():
        print(f"Adding delay due to back pressure at depth {sequence.fifo_depth}")
        sequence.add_delay(5)
    
    # Add transaction and update depth model
    sequence.add_data_value(0x1000 + i)
    prev_depth, new_depth = sequence.update_fifo_depth(is_write=True)
    print(f"FIFO depth: {prev_depth} -> {new_depth}")
```

### Creating and Resolving Dependency Graphs

```python
# Create a complex dependency graph
sequence = FIFOSequence("dep_graph", field_config)

# First wave - independent transactions
idx1 = sequence.add_data_value(0x1000)
idx2 = sequence.add_data_value(0x2000)
idx3 = sequence.add_data_value(0x3000)

# Second wave - depend on first wave
idx4 = sequence.add_data_value_with_dependency(0x4000, depends_on_index=idx1)
idx5 = sequence.add_data_value_with_dependency(0x5000, depends_on_index=idx2)
idx6 = sequence.add_data_value_with_dependency(0x6000, depends_on_index=idx3)

# Third wave - depends on second wave
idx7 = sequence.add_data_value_with_dependency(0x7000, depends_on_index=idx5)

# Check which transactions are ready to run
completed = set()  # No transactions completed yet
ready = sequence.resolve_dependencies(completed)
print(f"Ready transactions: {ready}")  # Should be idx1, idx2, idx3

# After completing idx1
completed.add(idx1)
ready = sequence.resolve_dependencies(completed)
print(f"Ready transactions: {ready}")  # Should add idx4
```

## Advanced Pattern Generation

### Walking Ones Pattern

```python
def add_walking_ones(self, data_width=32, delay=0):
    """
    Add transactions with walking ones pattern.
    
    Args:
        data_width: Width of data in bits
        delay: Delay between transactions
        
    Returns:
        Tuple of (self, list of transaction indexes)
    """
    indexes = []
    for bit in range(data_width):
        pattern = 1 << bit
        index = self.add_data_value(pattern, delay=delay)
        indexes.append(index)
            
    return self, indexes
```

### Stress Testing FIFO Boundaries

```python
def add_fifo_stress_pattern(self, depth_targets=None, delay_range=None):
    """
    Add a sequence designed to stress FIFO full/empty boundaries.

    Args:
        depth_targets: List of target depths to hit, or None for defaults
        delay_range: Tuple of (min_delay, max_delay), or None for defaults

    Returns:
        Tuple of (self, list of transaction indexes)
    """
    # Default parameters
    if depth_targets is None:
        # Target empty, 25%, 50%, 75%, almost full, and completely full
        depth_targets = [
            0,
            self.fifo_capacity // 4,
            self.fifo_capacity // 2,
            self.fifo_capacity * 3 // 4,
            self.fifo_capacity - 1,
            self.fifo_capacity
        ]

    if delay_range is None:
        delay_range = (0, 5)

    # Create test data that will force varying FIFO depths
    indexes = []
    for depth in depth_targets:
        # Use data value equal to target depth (for easy debugging)
        data = depth

        # Random delay within range
        delay = random.randint(delay_range[0], delay_range[1])

        # Add the transaction
        index = self.add_data_value(data, delay=delay)
        indexes.append(index)

    return self, indexes
```

## Integration with Other Components

The FIFOSequence class is designed to work with:

- **FIFOPacket**: Each sequence generates FIFOPacket objects
- **FIFOCommandHandler**: Can process entire sequences for testing
- **FIFOMaster/FIFOSlave**: Sequences control the transaction flow
- **FlexRandomizer**: Provides randomized timing constraints
- **Field Config**: Defines the structure of generated packets

## Performance Considerations

1. **Efficient Masking**: Masks field values once during addition
2. **Incremental Generation**: Generates packets only when needed
3. **Cached Field Masks**: Calculate field masks once and reuse
4. **Dynamic FIFO Modeling**: Adjusts behavior based on current state
5. **Dependency Resolution**: Only processes ready transactions

## Best Practices

1. **Use Factory Methods**: Leverage built-in factory methods for common patterns
2. **Model Realistic Behavior**: Configure back-pressure and capacity
3. **Add Dependencies Carefully**: Ensure valid dependency relationships
4. **Combine Patterns**: Mix different patterns for comprehensive testing
5. **Check Statistics**: Analyze statistics to validate test coverage

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
