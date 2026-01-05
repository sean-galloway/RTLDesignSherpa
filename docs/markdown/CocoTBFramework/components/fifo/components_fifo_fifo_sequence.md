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

# fifo_sequence.py

Simplified FIFO sequence generator focused on core pattern generation functionality. This module provides a clean approach to creating test sequences by removing complex dependency tracking and FIFO modeling, instead focusing on pattern generation and leveraging existing infrastructure.

## Overview

The `fifo_sequence.py` module provides the `FIFOSequence` class for generating test patterns and transaction sequences. It emphasizes simplicity and maintainability by:

- Using simple transaction lists instead of complex dependency graphs
- Focusing on pattern generation (incremental, walking bits, random, etc.)
- Leveraging existing PacketFactory and FieldConfig infrastructure
- Providing clean factory methods for common test patterns
- Eliminating unnecessary complexity while keeping useful features

### Key Features
- **Simple transaction management**: List-based transaction storage
- **Pattern generation**: Built-in methods for common test patterns
- **Factory methods**: Pre-configured sequences for typical test scenarios
- **Randomization support**: Integration with FlexRandomizer for timing control
- **Field configuration**: Full support for multi-field packets
- **FIFO-specific optimizations**: Capacity and back-pressure considerations

## Core Class

### FIFOSequence

Simplified FIFO sequence generator focused on core functionality.

#### Constructor

```python
FIFOSequence(name="basic", field_config=None, packet_class=FIFOPacket, log=None)
```

**Parameters:**
- `name`: Sequence name for identification and logging
- `field_config`: Field configuration (FieldConfig object, dict, or None for data-only)
- `packet_class`: Packet class to use (default: FIFOPacket)
- `log`: Logger instance

**Properties:**
- `name`: Sequence identifier
- `field_config`: Normalized FieldConfig object
- `packet_factory`: PacketFactory instance for creating packets
- `transactions`: List of (field_values, delay) tuples
- `use_random_selection`: Whether to use random selection from sequences
- `master_randomizer`: Optional randomizer for master interface timing
- `slave_randomizer`: Optional randomizer for slave interface timing

```python
from .fifo_sequence import FIFOSequence
from ..shared.field_config import FieldConfig

# Create basic sequence
sequence = FIFOSequence("test_sequence", log=log)

# Create sequence with field configuration
field_config = FieldConfig.create_standard(addr_width=32, data_width=32)
sequence = FIFOSequence("multi_field", field_config=field_config, log=log)
```

## Transaction Management

### `add_transaction(field_values=None, delay=0)`

Add a transaction to the sequence.

**Parameters:**
- `field_values`: Dictionary of field values (default: empty dict)
- `delay`: Delay in cycles before this transaction

**Returns:** Transaction index in sequence

```python
# Add single data transaction
sequence.add_transaction({'data': 0x12345678}, delay=0)

# Add multi-field transaction
sequence.add_transaction({
    'addr': 0x1000,
    'data': 0xDEADBEEF,
    'cmd': 0x2
}, delay=2)
```

### `add_data_value(data, delay=0)`

Add a transaction with a data value (convenience method).

**Parameters:**
- `data`: Data value
- `delay`: Delay in cycles

**Returns:** Transaction index

```python
# Add simple data values
sequence.add_data_value(0xDEADBEEF)
sequence.add_data_value(0xCAFEBABE, delay=3)
```

## Randomization Control

### `set_randomizers(master_randomizer=None, slave_randomizer=None)`

Set randomizers for timing control.

**Parameters:**
- `master_randomizer`: FlexRandomizer for master interface
- `slave_randomizer`: FlexRandomizer for slave interface

**Returns:** Self for method chaining

```python
from ..shared.flex_randomizer import FlexRandomizer

# Create randomizers
master_rand = FlexRandomizer({'write_delay': ([(0, 5)], [1.0])})
slave_rand = FlexRandomizer({'read_delay': ([(0, 3)], [1.0])})

# Apply to sequence
sequence.set_randomizers(master_randomizer=master_rand, slave_randomizer=slave_rand)
```

### `set_random_selection(enable=True)`

Enable/disable random selection from sequences.

```python
sequence.set_random_selection(True)  # Enable random selection
```

### `set_fifo_parameters(capacity=8, back_pressure=0.0)`

Set FIFO-specific parameters for realistic sequence generation.

**Parameters:**
- `capacity`: FIFO capacity in entries
- `back_pressure`: Probability of back-pressure (0.0 to 1.0)

**Returns:** Self for method chaining

```python
sequence.set_fifo_parameters(capacity=16, back_pressure=0.1)
```

## Pattern Generation Methods

### `add_data_incrementing(count, start=0, step=1, delay=0)`

Add incrementing data pattern.

```python
# Add 10 incrementing values starting from 0x1000
sequence.add_data_incrementing(count=10, start=0x1000, step=1)
```

### `add_walking_ones(data_width=32, delay=0)`

Add walking ones pattern.

```python
# Add walking ones for 16-bit data
sequence.add_walking_ones(data_width=16)
```

### `add_walking_zeros(data_width=32, delay=0)`

Add walking zeros pattern.

```python
# Add walking zeros for 32-bit data
sequence.add_walking_zeros(data_width=32)
```

### `add_random_data(count, delay=0)`

Add random data pattern.

```python
# Add 20 random data values
sequence.add_random_data(count=20)
```

### `add_corner_cases(delay=0)`

Add common corner case values.

```python
# Add standard corner cases: 0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA
sequence.add_corner_cases()
```

## Packet Generation

### `generate_packets(count=None, apply_fifo_metadata=True)`

Generate packets from the sequence.

**Parameters:**
- `count`: Number of packets to generate (None = all transactions)
- `apply_fifo_metadata`: Whether to apply FIFO metadata (compatibility flag)

**Returns:** List of generated FIFOPacket instances

```python
# Generate all packets
packets = sequence.generate_packets()

# Generate first 5 packets
packets = sequence.generate_packets(count=5)

# Use packets with master
for packet in packets:
    await master.send(packet)
```

## Factory Methods

### `create_burst(name="burst", count=10, start=0x1000, log=None)`

Create a simple burst sequence.

```python
burst_seq = FIFOSequence.create_burst(
    name="data_burst",
    count=16,
    start=0x2000,
    log=log
)
```

### `create_pattern_test(name="patterns", data_width=32, log=None)`

Create a sequence with common test patterns.

```python
pattern_seq = FIFOSequence.create_pattern_test(
    name="comprehensive_patterns",
    data_width=32,
    log=log
)
```

### `create_stress_test(name="stress", count=50, burst_size=10, log=None)`

Create a stress test with bursts and gaps.

```python
stress_seq = FIFOSequence.create_stress_test(
    name="stress_test",
    count=100,
    burst_size=20,
    log=log
)
```

### `create_data_stress_test(name="data_stress", data_width=32, delay=1, log=None)`

Create a comprehensive data stress test sequence.

```python
data_stress = FIFOSequence.create_data_stress_test(
    name="data_patterns",
    data_width=32,
    delay=2,
    log=log
)
```

### `create_comprehensive_test(name="comprehensive", field_config=None, packets_per_pattern=10, data_width=32, capacity=None, include_dependencies=True, log=None)`

Create a comprehensive test sequence with multiple patterns.

```python
comprehensive_seq = FIFOSequence.create_comprehensive_test(
    name="full_test",
    field_config=field_config,
    packets_per_pattern=15,
    data_width=32,
    capacity=16,
    include_dependencies=True,
    log=log
)
```

### `create_capacity_test(name="capacity_test", capacity=8, log=None)`

Create a test sequence designed to test FIFO capacity limits.

```python
capacity_seq = FIFOSequence.create_capacity_test(
    name="capacity_boundary",
    capacity=32,
    log=log
)
```

### `create_corner_case_test(name="corner_cases", field_config=None, log=None)`

Create a sequence focused on corner case testing.

```python
corner_seq = FIFOSequence.create_corner_case_test(
    name="edge_cases",
    field_config=field_config,
    log=log
)
```

### `create_dependency_chain(name="dependency_chain", count=5, data_start=0, data_step=1, delay=0, log=None)`

Create a sequence with simple dependency chain (simplified version).

```python
dep_seq = FIFOSequence.create_dependency_chain(
    name="dependent_ops",
    count=8,
    data_start=0x5000,
    data_step=4,
    delay=1,
    log=log
)
```

## Utility Methods

### `clear()`

Clear the sequence.

```python
sequence.clear()  # Remove all transactions
```

### `get_stats()`

Get simple statistics.

**Returns:** Dictionary with sequence statistics

```python
stats = sequence.get_stats()
print(f"Sequence '{stats['sequence_name']}' has {stats['transaction_count']} transactions")
```

### `get_dependency_graph()`

Get a simple representation of transaction dependencies (backward compatibility).

**Returns:** Minimal dependency graph structure

```python
dep_graph = sequence.get_dependency_graph()
print(f"Transaction count: {dep_graph['transaction_count']}")
```

## Usage Patterns

### Basic Sequence Creation and Usage

```python
# Create sequence with basic patterns
sequence = FIFOSequence("basic_test", log=log)

# Add various patterns
sequence.add_data_incrementing(10, start=0x1000)
sequence.add_walking_ones(16)
sequence.add_random_data(5)
sequence.add_corner_cases()

# Generate packets and run
packets = sequence.generate_packets()
for packet in packets:
    await master.send(packet)
```

### Multi-Field Sequence Testing

```python
# Create field configuration
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))
field_config.add_field(FieldDefinition("cmd", 4, format="hex"))

# Create sequence with multi-field support
sequence = FIFOSequence("multi_field_test", field_config=field_config, log=log)

# Add multi-field transactions
sequence.add_transaction({
    'addr': 0x1000,
    'data': 0xDEADBEEF,
    'cmd': 0x2  # WRITE
})

sequence.add_transaction({
    'addr': 0x2000,
    'data': 0x0,
    'cmd': 0x1  # READ
}, delay=3)

# Generate and use packets
packets = sequence.generate_packets()
```

### Factory-Based Test Generation

```python
class FIFOTestSuite:
    def __init__(self, master, slave, log):
        self.master = master
        self.slave = slave
        self.log = log
        
    async def run_pattern_tests(self):
        """Run comprehensive pattern tests"""
        # Create different test sequences
        sequences = [
            FIFOSequence.create_burst("burst", count=20, log=self.log),
            FIFOSequence.create_pattern_test("patterns", data_width=32, log=self.log),
            FIFOSequence.create_stress_test("stress", count=50, burst_size=10, log=self.log),
            FIFOSequence.create_corner_case_test("corners", log=self.log)
        ]
        
        for sequence in sequences:
            self.log.info(f"Running sequence: {sequence.name}")
            packets = sequence.generate_packets()
            
            for packet in packets:
                await self.master.send(packet)
                
            self.log.info(f"Completed sequence: {sequence.name} ({len(packets)} packets)")
    
    async def run_capacity_tests(self, fifo_capacity=16):
        """Run FIFO capacity boundary tests"""
        capacity_seq = FIFOSequence.create_capacity_test("capacity", capacity=fifo_capacity, log=self.log)
        packets = capacity_seq.generate_packets()
        
        for packet in packets:
            await self.master.send(packet)
```

### Randomized Sequence Testing

```python
# Create randomizers
master_randomizer = FlexRandomizer({
    'write_delay': ([(0, 0), (1, 5), (10, 20)], [0.6, 0.3, 0.1])
})

slave_randomizer = FlexRandomizer({
    'read_delay': ([(0, 1), (2, 8)], [0.8, 0.2])
})

# Create sequence with randomization
sequence = FIFOSequence("randomized_test", log=log)
sequence.set_randomizers(master_randomizer=master_randomizer, slave_randomizer=slave_randomizer)
sequence.set_fifo_parameters(capacity=32, back_pressure=0.05)

# Add patterns with varying delays
sequence.add_data_incrementing(20, start=0x8000, step=4, delay=0)
sequence.add_random_data(15, delay=1)

# Generate packets with randomization applied
packets = sequence.generate_packets()
```

### Custom Pattern Creation

```python
def create_custom_test_sequence(name, field_config, log):
    """Create a custom test sequence for specific testing needs"""
    sequence = FIFOSequence(name, field_config=field_config, log=log)
    
    # Phase 1: Basic connectivity
    sequence.add_data_incrementing(5, start=0x100, step=1)
    
    # Phase 2: Walking patterns
    sequence.add_walking_ones(16, delay=1)
    sequence.add_walking_zeros(16, delay=1)
    
    # Phase 3: Random stress
    sequence.add_random_data(20, delay=0)
    
    # Phase 4: Corner cases
    sequence.add_corner_cases(delay=2)
    
    # Phase 5: Burst patterns
    for i in range(3):
        sequence.add_data_incrementing(8, start=0x2000 + i*0x100, step=1, delay=0)
        if i < 2:  # Gap between bursts
            sequence.add_data_value(0x0, delay=5)
    
    return sequence

# Usage
custom_seq = create_custom_test_sequence("custom_test", field_config, log)
packets = custom_seq.generate_packets()
```

## Integration with Command Handler

```python
# Create sequence
sequence = FIFOSequence.create_comprehensive_test("full_test", log=log)

# Process through command handler
await command_handler.process_sequence(sequence)

# Or process individual packets
packets = sequence.generate_packets()
for packet in packets:
    await command_handler.send_packet_with_delay(packet, delay_cycles=packet.sequence_delay)
```

## Best Practices

### 1. **Use Factory Methods for Common Patterns**
```python
# Prefer factory methods over manual construction
burst_seq = FIFOSequence.create_burst("burst", count=20)  # Good
```

### 2. **Set Meaningful Sequence Names**
```python
# Use descriptive names for debugging
sequence = FIFOSequence("write_burst_test_phase1", log=log)
```

### 3. **Configure FIFO Parameters for Realistic Testing**
```python
sequence.set_fifo_parameters(capacity=actual_fifo_capacity, back_pressure=0.1)
```

### 4. **Use Appropriate Delays**
```python
# Add delays between transaction groups
sequence.add_data_incrementing(10, start=0x1000, delay=0)  # Burst
sequence.add_data_value(0x0, delay=5)  # Gap
sequence.add_data_incrementing(10, start=0x2000, delay=0)  # Next burst
```

### 5. **Leverage Randomization for Comprehensive Testing**
```python
sequence.set_randomizers(master_randomizer=master_rand, slave_randomizer=slave_rand)
```

### 6. **Clear Sequences When Reusing**
```python
sequence.clear()  # Clear before adding new patterns
```

The FIFOSequence class provides a clean, maintainable approach to test pattern generation while preserving the essential functionality needed for comprehensive FIFO testing. Its simplified design eliminates complexity while maintaining all the features needed for effective verification.
