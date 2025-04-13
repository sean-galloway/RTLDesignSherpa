# GAXISequence Component

## Overview

The `GAXISequence` class provides sophisticated capabilities for generating test sequences of GAXI transactions. It supports a wide range of patterns, transaction dependencies, and custom data patterns for comprehensive testing of GAXI interfaces.

## Key Features

- Generates sequences of transactions with configurable patterns
- Supports transaction dependency tracking for modeling complex relationships
- Provides built-in masking of field values to match field widths
- Includes standard test patterns like walking ones, alternating bits, etc.
- Supports random or sequential selection from sequences
- Allows for custom timing control through master and slave randomizers
- Provides statistics and diagnostics for sequence execution

## Class Definition

```python
class GAXISequence:
    def __init__(self, name="basic", field_config=None, packet_class=GAXIPacket):
        # ...
```

## Parameters

- **name**: Sequence name
- **field_config**: Field configuration defining transaction structure
- **packet_class**: Class to use for packet creation (default: `GAXIPacket`)

## Sequence Building Methods

### Basic Sequence Building

```python
def add_transaction(self, field_values=None, delay=0):
    """Add a transaction to the sequence with automatic field value masking"""
    
def add_transaction_with_dependency(self, field_values=None, delay=0, 
                                  depends_on_index=None, dependency_type="after"):
    """Add a transaction that depends on completion of a previous transaction"""
    
def add_data_value(self, data, delay=0):
    """Add a transaction with a data value"""
    
def add_data_value_with_dependency(self, data, delay=0, 
                                 depends_on_index=None, dependency_type="after"):
    """Add a data transaction that depends on completion of a previous transaction"""
    
def add_delay(self, clocks):
    """Add a delay to the sequence"""
```

### Advanced Pattern Generation

```python
def add_data_incrementing(self, count, data_start=0, data_step=1, delay=0):
    """Add transactions with incrementing data values"""
    
def add_data_pattern(self, patterns, delay=0):
    """Add transactions with various data patterns"""
    
def add_walking_ones(self, data_width=32, delay=0):
    """Add transactions with walking ones pattern"""
    
def add_walking_zeros(self, data_width=32, delay=0):
    """Add transactions with walking zeros pattern"""
    
def add_alternating_bits(self, data_width=32, delay=0):
    """Add transactions with alternating bit patterns"""
    
def add_burst_with_dependencies(self, count, data_start=0, data_step=1, 
                              delay=0, dependency_spacing=1):
    """Add a burst of transactions where each one depends on a previous one"""
    
def add_dependency_chain(self, count, data_start=0, data_step=1, delay=0):
    """Add a chain of transactions where each depends on the previous one"""
```

### Randomization Control

```python
def set_random_selection(self, enable=True):
    """Enable/disable random selection from sequences"""
    
def set_master_randomizer(self, randomizer):
    """Set the randomizer to use for master timing constraints"""
    
def set_slave_randomizer(self, randomizer):
    """Set the randomizer to use for slave timing constraints"""
```

### Packet Generation

```python
def generate_packet(self):
    """Generate the next packet in the sequence"""
    
def generate_packets(self, count=None):
    """Generate multiple packets"""
    
def get_packet(self, index=0):
    """Get a specific packet from the generated list"""
    
def reset_iterators(self):
    """Reset all sequence iterators to the beginning"""
```

### Dependency Management

```python
def get_dependency_graph(self):
    """Get a representation of the transaction dependencies"""
    
def resolve_dependencies(self, completed_transactions=None):
    """Determine which transactions are ready to execute based on dependencies"""
```

### Statistics and Diagnostics

```python
def get_stats(self):
    """Get statistics about the sequence generation"""
    
def mask_field_value(self, field_name, value):
    """Mask a value according to the corresponding field's bit width"""
```

## Factory Methods

```python
@classmethod
def create_dependency_chain(cls, name="dependency_chain", count=5, 
                         data_start=0, data_step=1, delay=0):
    """Create a sequence with transactions forming a dependency chain"""
```

## Usage Example

```python
# Create a field configuration
field_config = FieldConfig()
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})

# Create a basic sequence
sequence = GAXISequence("test_sequence", field_config)

# Add different types of transactions
sequence.add_data_value(0x12345678, delay=0)
sequence.add_data_value(0xABCDEF01, delay=2)
sequence.add_data_value(0x87654321, delay=1)

# Generate packets from the sequence
packets = sequence.generate_packets()

# Send the packets through a master
for packet in packets:
    await master.send(packet)
```

## Advanced Pattern Example

```python
# Create a sequence with various patterns
sequence = GAXISequence("pattern_sequence", field_config)

# Add incrementing values
sequence.add_data_incrementing(count=10, data_start=0, data_step=1, delay=0)

# Add walking ones pattern
sequence.add_walking_ones(data_width=32, delay=1)

# Add alternating bits pattern
sequence.add_alternating_bits(data_width=32, delay=2)

# Generate packets from the sequence
packets = sequence.generate_packets()

# Print information about the packets
for i, packet in enumerate(packets):
    print(f"Packet {i}: data=0x{packet.data:X}, delay={sequence.delay_seq[i]}")
```

## Dependency Chain Example

```python
# Create a sequence with transaction dependencies
sequence = GAXISequence("dependency_sequence", field_config)

# Add a chain of dependencies where each transaction depends on the previous one
sequence.add_dependency_chain(count=5, data_start=0x1000, data_step=0x1000, delay=0)

# Generate packets with dependency information
packets = sequence.generate_packets()

# Explore the dependencies
for i, packet in enumerate(packets):
    if hasattr(packet, 'depends_on_index'):
        print(f"Packet {i} depends on packet {packet.depends_on_index}")
    else:
        print(f"Packet {i} has no dependencies")

# Get the dependency graph
dep_graph = sequence.get_dependency_graph()
print(f"Dependencies: {dep_graph['dependencies']}")
print(f"Dependency types: {dep_graph['dependency_types']}")
```

## Randomized Selection Example

```python
# Create a sequence with many transactions
sequence = GAXISequence("random_sequence", field_config)
sequence.add_data_incrementing(count=100, data_start=0, data_step=1, delay=0)

# Enable random selection
sequence.set_random_selection(True)

# Generate a few packets with random selection
for _ in range(5):
    packet = sequence.generate_packet()
    print(f"Random packet: data=0x{packet.data:X}")
```

## Randomized Timing Example

```python
# Create randomizers for master and slave
master_randomizer = FlexRandomizer({
    'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
})
slave_randomizer = FlexRandomizer({
    'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
})

# Create a sequence with randomizers
sequence = GAXISequence("timed_sequence", field_config)
sequence.set_master_randomizer(master_randomizer)
sequence.set_slave_randomizer(slave_randomizer)

# Add transactions
sequence.add_data_incrementing(count=10, data_start=0, data_step=1, delay=0)

# Generate packets with randomized timing
packets = sequence.generate_packets()

# Send packets with randomized timing
for packet in packets:
    master_delay = packet.get_master_delay()
    slave_delay = packet.get_slave_delay()
    print(f"Packet data=0x{packet.data:X}, master_delay={master_delay}, slave_delay={slave_delay}")
```

## Statistics Example

```python
# Create a sequence with various patterns
sequence = GAXISequence("stats_sequence", field_config)
sequence.add_data_incrementing(count=10, data_start=0, data_step=1, delay=0)
sequence.add_walking_ones(data_width=32, delay=1)
sequence.add_alternating_bits(data_width=32, delay=2)

# Add a value that exceeds the field width to test masking
sequence.add_data_value(0x1234567890ABCDEF, delay=0)  # Too large for 32-bit field

# Generate packets
packets = sequence.generate_packets()

# Get statistics
stats = sequence.get_stats()
print(f"Total transactions: {stats['total_transactions']}")
print(f"Masked values: {stats['masked_values']}")
print(f"Masking percentage: {stats['masking_percentage']:.2f}%")
print(f"Field stats: {stats['field_stats']}")
```

## Buffer Testing Example

```python
# Create a sequence for testing a skid buffer
buffer_sequence = GAXISequence("buffer_test", field_config)

# Add various patterns
buffer_sequence.add_data_incrementing(count=20, data_start=0, data_step=1, delay=0)
buffer_sequence.add_data_value(0xAAAAAAAA, delay=0)  # Alternating 1010...
buffer_sequence.add_data_value(0x55555555, delay=0)  # Alternating 0101...
buffer_sequence.add_walking_ones(data_width=32, delay=0)

# Generate packets
packets = buffer_sequence.generate_packets()

# Run the test
for packet in packets:
    # Send to master
    await master.send(packet)
    # Wait for valid/ready handshake
    await RisingEdge(dut.clk)
    # Check if packet appears at slave side
    if slave.received_queue:
        rx_packet = slave.received_queue.popleft()
        if rx_packet.data != packet.data:
            print(f"Data mismatch: sent 0x{packet.data:X}, received 0x{rx_packet.data:X}")
```

## Factory Methods Example

```python
# Use factory method to create a dependency chain sequence
chain_sequence = GAXISequence.create_dependency_chain(
    name="factory_chain",
    count=10,
    data_start=0x1000,
    data_step=0x1000,
    delay=1
)

# Generate packets with dependency information
packets = chain_sequence.generate_packets()

# Print dependency information
dep_graph = chain_sequence.get_dependency_graph()
print(f"Dependencies: {dep_graph['dependencies']}")

# Explore dependencies resolution
completed = set([0])  # Mark the first transaction as completed
ready = chain_sequence.resolve_dependencies(completed)
print(f"Ready transactions: {ready}")
```

## Tips and Best Practices

1. **Sequence Design**: Start with simple sequences and build up to more complex patterns
2. **Dependencies**: Use dependencies to model realistic transaction ordering constraints
3. **Field Configuration**: Define field configurations carefully, especially bit widths
4. **Masking**: Let the sequence handle masking automatically instead of manually masking values
5. **Randomization**: Use master and slave randomizers to create realistic timing variations
6. **Statistics**: Monitor sequence statistics to validate test coverage
7. **Factory Methods**: Use factory methods for common sequence patterns to simplify test setup
8. **Custom Patterns**: Combine basic patterns to create custom test scenarios
9. **Iterator Reset**: Call reset_iterators() when reusing sequences to ensure consistent behavior
10. **Dependency Handling**: Use resolve_dependencies() to determine which transactions are ready to execute
