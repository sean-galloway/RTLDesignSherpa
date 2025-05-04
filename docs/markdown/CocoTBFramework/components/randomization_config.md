# RandomizationConfig

## Overview

The `RandomizationConfig` module provides a flexible configuration framework for controlling randomization behavior in protocol verification environments. It acts as a higher-level abstraction over the `FlexRandomizer` component, offering more structured and protocol-aware randomization capabilities.

## Features

- Multiple randomization modes: constrained, deterministic, sequence, custom
- Support for field dependencies and ordering
- Group-based configuration for collective settings
- Dependency-aware value generation
- Pluggable architecture using `FlexRandomizer` as the backend

## Classes

### RandomizationMode

An enumeration defining possible randomization modes:

- `DETERMINISTIC`: Fixed values, not random
- `CONSTRAINED`: Constrained random with weights
- `DIRECTED`: Directed test patterns
- `SEQUENCE`: Sequence of values in order
- `CUSTOM`: Custom generator function

### FieldRandomizationConfig

A dataclass that configures randomization for a specific field.

#### Attributes

- `enabled`: Boolean flag to enable/disable randomization (default: True)
- `mode`: Randomization mode from the `RandomizationMode` enum (default: `CONSTRAINED`)
- `constraints`: Optional dictionary with constraints (default: `None`)
- `sequence`: Optional list of values for sequence mode (default: `None`)
- `custom_generator`: Optional function for custom mode (default: `None`)
- `dependencies`: List of field names this field depends on (default: empty list)

### RandomizationConfig

The main configuration class for randomizing protocol fields.

#### Constructor

```python
def __init__(self, protocol_name: str = "generic", seed: Optional[int] = None)
```

- `protocol_name`: Name of the protocol (e.g., "AXI4", "APB")
- `seed`: Master random seed for reproducibility

#### Key Methods

- `configure_field(field_name, config)`: Configure randomization for a specific field
- `add_to_group(group_name, field_name)`: Add a field to a named group for collective configuration
- `configure_group(group_name, **config_kwargs)`: Configure all fields in a group with the same settings
- `get_field_config(field_name)`: Get configuration for a specific field
- `generate_value(field_name)`: Generate a random value for a field based on its configuration
- `generate_values(field_names)`: Generate values for multiple fields at once
- `enable()` / `disable()`: Enable or disable randomization
- `set_seed(seed)`: Set the master random seed
- `reset_sequences()`: Reset all sequence positions to start
- `create_constrained_config(field_name, bins, weights)`: Create a constrained randomization configuration
- `create_sequence_config(field_name, sequence)`: Create a sequence-based configuration
- `create_custom_config(field_name, generator)`: Create a custom randomization configuration

## Example Usage

### Basic Configuration

```python
from CocoTBFramework.components.randomization_config import (
    RandomizationConfig, RandomizationMode, FieldRandomizationConfig
)

# Create a randomization configuration for a protocol
rand_config = RandomizationConfig(protocol_name="AXI4", seed=12345)

# Configure individual fields
rand_config.configure_field(
    "addr",
    FieldRandomizationConfig(
        mode=RandomizationMode.CONSTRAINED,
        constraints={
            "bins": [(0x1000, 0x1FFF), (0x8000, 0x8FFF)],
            "weights": [0.7, 0.3]
        }
    )
)

rand_config.configure_field(
    "data",
    FieldRandomizationConfig(
        mode=RandomizationMode.SEQUENCE,
        sequence=[0xA5A5A5A5, 0x5A5A5A5A, 0xFFFFFFFF, 0x00000000]
    )
)

# Generate values
addr_value = rand_config.generate_value("addr")
data_value = rand_config.generate_value("data")

print(f"Generated addr: 0x{addr_value:X}")
print(f"Generated data: 0x{data_value:X}")
```

### Using Field Dependencies

```python
# Configure fields with dependencies
rand_config.configure_field(
    "burst_length",
    FieldRandomizationConfig(
        mode=RandomizationMode.CONSTRAINED,
        constraints={
            "bins": [(1, 16), (32, 64), (128, 256)],
            "weights": [0.6, 0.3, 0.1]
        }
    )
)

# Make burst_type dependent on burst_length
rand_config.configure_field(
    "burst_type",
    FieldRandomizationConfig(
        mode=RandomizationMode.CUSTOM,
        custom_generator=lambda values: 
            0 if values.get('burst_length', 0) <= 16 else 
            1 if values.get('burst_length', 0) <= 64 else 
            2,
        dependencies=["burst_length"]
    )
)

# Generate values in dependency order
values = rand_config.generate_values(["burst_length", "burst_type"])
print(f"Burst length: {values['burst_length']}")
print(f"Burst type: {values['burst_type']}")
```

### Group Configuration

```python
# Add fields to groups
rand_config.add_to_group("address_signals", "addr")
rand_config.add_to_group("address_signals", "addr_valid")
rand_config.add_to_group("address_signals", "addr_ready")

rand_config.add_to_group("data_signals", "data")
rand_config.add_to_group("data_signals", "data_valid")
rand_config.add_to_group("data_signals", "data_ready")

# Configure all fields in a group
rand_config.configure_group(
    "address_signals",
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0, 1)],
        "weights": [1.0]
    }
)

# Configure another group differently
rand_config.configure_group(
    "data_signals",
    mode=RandomizationMode.SEQUENCE,
    sequence=[0, 1, 0, 0, 1]
)
```

### Helper Methods for Common Configurations

```python
# Create constrained configuration
rand_config.create_constrained_config(
    "prot",
    bins=[(0, 1), (2, 3), (4, 7)],
    weights=[0.5, 0.3, 0.2]
)

# Create sequence configuration
rand_config.create_sequence_config(
    "resp",
    sequence=[0, 0, 1, 2, 3, 0]
)

# Create custom generator
def generate_id(values):
    # Generate ID based on transaction type
    if 'is_read' in values and values['is_read']:
        return random.randint(0, 7)  # Read IDs in range 0-7
    else:
        return random.randint(8, 15)  # Write IDs in range 8-15

rand_config.create_custom_config("id", generate_id)
```

### Integration with Test Environment

```python
from CocoTBFramework.components.randomization_config import RandomizationConfig
from CocoTBFramework.components.packet import Packet
from CocoTBFramework.components.field_config import FieldConfig

# Create field configuration for packets
field_config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create randomization configuration
rand_config = RandomizationConfig("APB")

# Configure fields
rand_config.create_constrained_config(
    "addr",
    bins=[(0x0000, 0x0FFF), (0x1000, 0x1FFF)],
    weights=[0.3, 0.7]
)

rand_config.create_constrained_config(
    "data",
    bins=[(0x00000000, 0xFFFFFFFF)],
    weights=[1.0]
)

# Generate multiple random packets
for i in range(10):
    # Generate random values
    values = rand_config.generate_values(["addr", "data"])
    
    # Create packet with random values
    packet = Packet(field_config, **values)
    
    # Use packet in test
    print(f"Packet {i}: {packet}")
```

## Advanced Features

### Topological Sorting for Dependencies

The `RandomizationConfig` class automatically determines the correct order for generating dependent fields:

```python
# Configure fields with complex dependencies
rand_config.configure_field(
    "a", FieldRandomizationConfig(
        mode=RandomizationMode.CONSTRAINED,
        constraints={"bins": [(1, 10)], "weights": [1.0]}
    )
)

rand_config.configure_field(
    "b", FieldRandomizationConfig(
        mode=RandomizationMode.CUSTOM,
        custom_generator=lambda values: values["a"] * 2,
        dependencies=["a"]
    )
)

rand_config.configure_field(
    "c", FieldRandomizationConfig(
        mode=RandomizationMode.CUSTOM,
        custom_generator=lambda values: values["a"] + values["b"],
        dependencies=["a", "b"]
    )
)

# Will automatically generate values in the correct order: a, b, c
values = rand_config.generate_values(["c", "a", "b"])
print(values)
```

### Controlling Randomization Globally

```python
# Disable randomization (use defaults or first value in sequences)
rand_config.disable()

# Generate values (will use deterministic values)
values = rand_config.generate_values(["addr", "data", "resp"])
print("Deterministic values:", values)

# Re-enable randomization
rand_config.enable()

# Generate random values
values = rand_config.generate_values(["addr", "data", "resp"])
print("Random values:", values)
```

## Integration with Protocol-Specific Components

The framework includes protocol-specific randomization configurations in subdirectories:

- `axi4/axi4_randomization_config.py`: Specialization for AXI4 protocol
- `gaxi/gaxi_buffer_configs.py`: Specialization for Generic AXI protocol

## Notes

- The `RandomizationConfig` class uses the `FlexRandomizer` class as its backend
- It provides a more structured and protocol-aware approach to randomization
- Dependency management ensures values are generated in the correct order
- Group-based configuration simplifies managing related fields

## See Also

- [FlexRandomizer](flex_randomizer.md) - Used as the backend for RandomizationConfig
- [ConstrainedRandom](constrained_random.md) - Simpler constrained randomization
- [Packet](packet.md) - Can be populated with randomized values

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
